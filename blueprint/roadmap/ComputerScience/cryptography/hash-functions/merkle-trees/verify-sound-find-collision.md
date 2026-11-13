# Constructive soundness

**Constructive soundness** of Merkle inclusion proofs: if a path for `x` at position `i`
verifies against the root of `l`, then `x` is the actual leaf or `findCollision` returns unequal
hash-input pairs from the forged and actual paths on which `h` agrees.
