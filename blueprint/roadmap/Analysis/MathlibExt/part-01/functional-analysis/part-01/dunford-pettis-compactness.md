---
article_id: af_9e2a794a75f276c0d4286594
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.DunfordPettisWanted.dunford_pettis_compactness
---

# Dunford Pettis

On a finite measure space, a family `f : ι → α → ℝ` with `MemLp 1` is uniformly integrable
`UniformIntegrable f 1 μ` iff its image in `WeakSpace ℝ (Lp ℝ 1 μ)` has weakly compact closure,
i.e. relative weak compactness in `L¹`. Source: N. Dunford and B. J. Pettis,
Linear Operations on Summable Functions, Trans. Amer. Math. Soc. 47 (1940), 323–392,
DOI 10.1090/S0002-9947-1940-0002020-4, criterion for weak compactness in `L¹`;
Dunford-Schwartz IV; Lean states finite-measure real `L¹` specialization with weak-space
closure characterization.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Eberlein Smulian](eberlein-smulian.md)
- [Milman Pettis](milman-pettis.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.DunfordPettis](../../../../../../sources/v2/MathlibExt.md)
