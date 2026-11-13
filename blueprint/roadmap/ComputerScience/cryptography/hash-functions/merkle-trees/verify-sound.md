# Existential soundness

**Existential soundness** of Merkle inclusion proofs: if a path for `x` at position `i` verifies
against the root of `l`, then leaf `i` of `l` is `x`, or `h` has some collision.

This theorem is retained for compatibility and does not tie the existential collision to the given
proof. For the computational strengthening that extracts a collision from the forged and actual
paths, use `verify_sound_findCollision` from `MerkleTree.Collision`.
