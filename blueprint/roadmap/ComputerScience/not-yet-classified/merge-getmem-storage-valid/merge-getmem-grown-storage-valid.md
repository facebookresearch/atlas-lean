# Merge Getmem grown storage valid

The growth branch installs fresh live heap backing of exactly
`need.toNat` logical cells.  Its physical allocation is exactly the old
keyed/unkeyed multiplier times that request and remains within the precise
pointer-count allocation limit.
