---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.approxVertexCover_two_approximation
---

# Approx Vertex Cover two approximation

CLRS Theorem 35.1: if `edges` lists exactly the edges of `G`, each in at least one orientation,
then `approxVertexCover edges` is a vertex cover of `G` of size at most twice the vertex cover
number.

## Depends on

- [Approx Vertex Cover](approx-vertex-cover.md)

## Proof depends on

- [Approx Vertex Cover is Vertex Cover](approx-vertex-cover-is-vertex-cover.md)
- [Card approx Vertex Cover le two mul](card-approx-vertex-cover-le-two-mul.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.VertexCover](../../../../../../sources/v2/CSLibExt.md)
