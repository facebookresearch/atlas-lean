---
article_id: af_60425bce09febbf73fbb0e6b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted.eberlein_smulian
---

# Eberlein Smulian

For a Banach space over `ℝ` or `ℂ`, a set in the weak topology `WeakSpace 𝕜 E` is compact iff it
is sequentially compact. Source: W. F. Eberlein, Weak Compactness in Banach Spaces,
PNAS 33 (1947), 51–53, DOI 10.1073/pnas.33.3.51, and V. Smulian (1947); Dunford-Schwartz,
Linear Operators I, 1958, V.5-6; Lean states `RCLike` Banach case with
`IsCompact ↔ IsSeqCompact` in `WeakSpace`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.EberleinSmulian](../../../../../../sources/v2/MathlibExt.md)
