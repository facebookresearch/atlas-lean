---
article_id: af_e48fd1af4145d6fd950cad7a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.BanachSaksWanted.banach_saks
---

# Banach Saks

In a uniformly convex real Banach space, every norm-bounded sequence `x : ℕ → E` admits a strictly
increasing subsequence `φ` and a point `y` such that the Cesàro means `(n:ℝ)⁻¹ • ∑ i ∈ range n, x
(φ i)` converge to `y` in norm. Source: S. Banach and S. Saks, Studia Math. 2 (1930) 51-57;
uniformly convex form and property due to Kakutani, 1939; textbook Diestel, Sequences and Series
in Banach Spaces; Lean gives uniformly convex real Banach specialization with explicit `StrictMono
φ` and norm-convergent Cesàro means.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Eberlein Smulian](eberlein-smulian.md)
- [Milman Pettis](milman-pettis.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.BanachSaks](../../../../../../sources/v2/MathlibExt.md)
