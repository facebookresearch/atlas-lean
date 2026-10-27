---
article_id: af_90a593955ab0036fdbdeaed7
declaration: def
origin: cited
statement: formalized
lean: SimpleGraph.cochromaticNumber
---

# Cochromatic Number

The cochromatic number of a graph is the minimal number of colors needed to color its vertices
so that each color class induces either an independent set or a complete graph.
This is `⊤` (infinity) iff `G` isn't cocolorable with finitely many colors.

If `G` is cocolorable, then `ENat.toNat G.cochromaticNumber` is the `ℕ`-valued cochromatic number.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Cocolorable](cocolorable.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SimpleGraph.Coloring.Vertex](../../../../../../../../sources/v2/MathlibExt.md)
