---
article_id: af_17a66cdcdbb3aa577655a962
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.goldstine
---

# Banach Space

For a normed space over `ℝ` or `ℂ` (`RCLike 𝕜`), the image of the unit ball under
`StrongDual.toWeakDual ∘ inclusionInDoubleDual` is weak-star dense, with closure equal to the
bidual unit ball in `WeakDual`. Source: H. H. Goldstine, Weakly complete Banach spaces,
Duke Math. J. 4 (1938), DOI 10.1215/S0012-7094-38-00410-7; Rudin, Functional Analysis, 2nd
ed.; Lean states `RCLike` field case with metric closedBall formulation.
Proves `Wanted` entry `goldstine`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.BanachSpace](../../../../../../sources/v2/MathlibExt.md)
