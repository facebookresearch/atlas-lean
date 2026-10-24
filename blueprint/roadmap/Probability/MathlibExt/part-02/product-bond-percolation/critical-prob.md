---
article_id: af_709772c312d5b59cf48f3b2e
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Probability.ProductBondPercolation.criticalProb
---

# Critical Prob

The critical probability `p_c(G)` for bond percolation on a graph
`G` with countable vertex type: the infimum of densities at which an
infinite open cluster exists with positive probability, with `1`
inserted so that graphs which never percolate (empty density set) get
`p_c(G) = 1`, the standard `[0, 1]`-valued threshold convention
(`sInf ∅ = 0` in `ℝ`). Countability is part of the domain so that the
global "some infinite cluster exists" event is measurable for the
`Measure.infinitePi` product law.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Gbernoulli Law](gbernoulli-law.md)
- [Gcluster](gcluster.md)

## Sources

- [MathlibExt, MathlibExt.Probability.ProductBondPercolation](../../../../../sources/v2/MathlibExt.md)
