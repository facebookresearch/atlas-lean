# Root

The Merkle root: iterate `level` for the height `Nat.clog 2 l.length` of the tree (after which
at most one node is left, `length_iterate_level_clog_le_one`) and take the remaining node; `none`
for an empty list of leaves.
