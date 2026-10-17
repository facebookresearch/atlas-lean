---
article_id: af_6e52c8543977dcd21af22271
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.SparseTable.entry_build_eq_min?
---

# Entry build eq min?

A built table's in-range entry is `List.min?` of its interval slice. The
interval-fit premise alone suffices: it implies `2 ^ k ≤ a.length`, hence the
level bound `k ≤ Nat.log2 a.length`, which is derived internally.

## Depends on

- [Build](build.md)
- [Entry](entry.md)

## Proof depends on

- [Sparse Table](sparse-table.md)
- [Build valid](build-valid.md)
- [Entry eq of valid](entry-eq-of-valid.md)
- [Level](level.md)
- [Omin](omin.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SparseTable](../../../../../../../sources/v2/CSLibExt.md)
