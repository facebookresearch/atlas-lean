# Merge Getmem grown

A guard-admitted growth request installs fresh live heap backing of exactly
`need.toNat` logical cells, keeps keyed/unkeyed mode, and records `need` as the
new capacity.
