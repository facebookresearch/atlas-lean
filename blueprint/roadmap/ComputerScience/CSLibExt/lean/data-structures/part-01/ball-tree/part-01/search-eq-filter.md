---
article_id: af_c960d15213a0441681615bf8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BallTree.search_eq_filter
---

# Search eq filter

The search of a valid tree is its point list filtered by the distance
predicate; pruning against the bounding spheres loses no point.

## Depends on

- [Ball Tree](ball-tree.md)
- [Valid](valid.md)
- [Dist Sq](dist-sq.md)
- [Search](search.md)
- [To List](to-list.md)

## Proof depends on

- [Dist Sq comm](dist-sq-comm.md)
- [Dist Sq le two mul](dist-sq-le-two-mul.md)
- [Search Aux](search-aux.md)
- [To List Aux](to-list-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BallTree](../../../../../../../../sources/v2/CSLibExt.md)
