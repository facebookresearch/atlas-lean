---
article_id: af_df7f3bfa1f51327348fc25e8
declaration: structure
origin: cited
statement: formalized
lean: MathlibExt.Geometry.OptimalMoebiusWanted.OptimalMoebius.IsMoebiusEmbedding
---

# Is Moebius Embedding

A Moebius embedding is defined in the paper to be a smooth isometric embedding.

We use a function `f` defined on all of `ℝ²`, but only impose conditions on `f` on the unit strip
`[0, 1] × ℝ`. We glue the strip into a Moebius band by imposing `f(1 - x, y + a) = f(x, y)`.

We require the map to be an embedding by requiring injectivity of `f` on a fundamental domain.
We require the embedding to be isometric by requiring the derivative of `f` to be an isometry.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Geometry.OptimalMoebiusWanted](../../../../../sources/v2/WantedExt.md)
