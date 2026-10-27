---
article_id: af_a349e2061bb4c6e85f2b0ec8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.RangeTree.valid_build_of_sorted
---

# Valid build of sorted

Building from a sorted list yields a valid (classical) range tree:
correct cached bounds and sorted leaf order. Without the sortedness
hypothesis only `boundsOk_build` holds.

## Depends on

- [Valid](../part-01/valid.md)
- [Build](build.md)

## Proof depends on

- [Bounds Ok](../part-01/bounds-ok.md)
- [Bounds Ok build](bounds-ok-build.md)
- [To List](../part-01/to-list.md)
- [To List build](to-list-build.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RangeTree](../../../../../../../../sources/v2/CSLibExt.md)
