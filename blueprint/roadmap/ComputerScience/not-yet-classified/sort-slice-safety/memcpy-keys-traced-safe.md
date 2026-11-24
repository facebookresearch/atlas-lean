# Memcpy Keys Traced safe

The key phase of `memcpy` succeeds on exact valid ranges, records only
in-bounds accesses, and preserves the destination extent.
