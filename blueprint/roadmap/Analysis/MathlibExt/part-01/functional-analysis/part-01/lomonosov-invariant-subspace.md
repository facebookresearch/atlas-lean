---
article_id: af_51fabefef9e01f1c0db00bf5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.LomonosovInvariantSubspaceWanted.lomonosov_invariantSubspace
---

# Lomonosov Invariant Subspace

In an infinite-dimensional complex Banach space `E`, if `K ≠ 0` is compact and `T : E →L[ℂ] E`
commutes with `K`, then `T` has a nontrivial proper closed `ℂ`-invariant subspace `M` with `M ≠
⊥`, `M ≠ ⊤`, `IsClosed M`, `T '' M ⊆ M`. Source: V. Lomonosov, Functional Anal. Appl. 7 (1973)
and J. Hilden elementary proof, Bull. Amer. Math. Soc.; Aronszajn-Smith 1954 precursor;
Radjavi-Rosenthal invariant subspace book, 1973; Lean states complex Banach infinite-dimensional
case `K≠0` compact commuting with `T` yields nontrivial closed invariant subspace.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.LomonosovInvariantSubspace](../../../../../../sources/v2/MathlibExt.md)
