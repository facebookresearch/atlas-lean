---
article_id: af_8d3af17b81c2156aff74af09
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.fleischner
---

# Fleischner

Fleischner's theorem (https://en.wikipedia.org/wiki/Fleischner%27s_theorem):
    the square of a 2-vertex-connected finite simple graph with at least three
    vertices is Hamiltonian. Here `H` is the square of `G`: distinct vertices are
    adjacent in `H` iff they are adjacent in `G` or share a common neighbor.

## Depends on

- [Is Vertex Connected](../part-04/vertex-connectivity/is-vertex-connected.md)

## Proof depends on

- [Has Strong Square Cycle](../part-03/strong-square-cycle/has-strong-square-cycle.md)
- [Card gt](../part-04/vertex-connectivity/card-gt.md)
- [Fleischner Strong](has-strong-square-cycle.md)
- [Eq square iff](../part-03/square/eq-square-iff.md)
- [Square](../part-03/square/square.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SimpleGraph.Fleischner](../../../../../../sources/v2/MathlibExt.md)
- Herbert Fleischner, "The Square of Every Two-Connected Graph Is Hamiltonian," Journal of Combinatorial Theory, Series B 16 (1974), 29–34, DOI 10.1016/0095-8956(74)90091-4, https://doi.org/10.1016/0095-8956(74)90091-4. Proof: the strengthened vertex-rooted induction of A. Georgakopoulos, "A short proof of Fleischner's theorem", Discrete Math. 309 (2009), 6632–6634.
