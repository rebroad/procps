#!/usr/bin/env bash
set -euo pipefail

# Replicate Debian's procps configure flags (see debian/rules in Debian source).
# This is useful for matching distro behavior such as watch formatting.

if ! command -v dpkg-architecture >/dev/null 2>&1; then
  echo "dpkg-architecture not found. This script is intended for Debian/Ubuntu." >&2
  exit 1
fi

DEB_HOST_MULTIARCH=$(dpkg-architecture -qDEB_HOST_MULTIARCH)
DEB_HOST_GNU_TYPE=$(dpkg-architecture -qDEB_HOST_GNU_TYPE)
DEB_BUILD_GNU_TYPE=$(dpkg-architecture -qDEB_BUILD_GNU_TYPE)
DEB_HOST_ARCH_OS=$(dpkg-architecture -qDEB_HOST_ARCH_OS)

linux_flags=()
if [[ "${DEB_HOST_ARCH_OS}" == "linux" ]]; then
  linux_flags=(--with-systemd --enable-libselinux)
fi

./configure \
  --disable-silent-rules \
  --enable-watch8bit --enable-colorwatch \
  --enable-w-from \
  --enable-skill \
  --disable-pidof \
  --disable-modern-top \
  --prefix=/usr \
  --libdir="/usr/lib/${DEB_HOST_MULTIARCH}" \
  --build="${DEB_BUILD_GNU_TYPE}" \
  --host="${DEB_HOST_GNU_TYPE}" \
  "${linux_flags[@]}"
