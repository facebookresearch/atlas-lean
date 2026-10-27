---
article_id: af_d86d6f48e3003bfeab6702b9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.CStarAlgebra.StinespringWanted.stinespring_dilation
---

# Stinespring

Every completely positive map `φ : A →CP B(H)` from a unital C*-algebra `A` to `B(H)` dilates as
`φ a = V† (π a) V` for some Hilbert space `K`, `∗`-homomorphism `π : A →⋆ₐ B(K)` and `V : H →L[ℂ]
K`. Source: Stinespring dilation theorem, W. F. Stinespring, Proc. Amer. Math. Soc. 6 (1955); see
Paulsen, Completely Bounded Maps; Lean is general CP map A →CP B(H) dilation V† π(a) V, not
finite-dimensional Kraus form.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.CStarAlgebra.Stinespring](../../../../../sources/v2/MathlibExt.md)
