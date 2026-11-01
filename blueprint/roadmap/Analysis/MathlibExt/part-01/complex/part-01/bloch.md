---
article_id: af_d8949582e84ec99535c42bf0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.BlochWanted.bloch
---

# Bloch

There exists universal `B > 0` such that every `f : ℂ → ℂ` holomorphic on `ball (0:ℂ) 1` with
`deriv f 0 = 1` admits an open connected `V ⊆ ball 0 1` and `w : ℂ` with `Set.InjOn f V` and `f ''
V = ball w B`. Source: A. Bloch, Les théorèmes de M. Valiron sur les fonctions entières et la
théorie de l'uniformisation, Ann. Fac. Sci. Toulouse 17 (1925), 1–22, DOI 10.5802/afst.335; see
Ahlfors, Complex Analysis, Univalent Functions; Lean is universal B > 0 exact schlicht disc
f '' V = ball w B for open connected V, stronger than Landau.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.Bloch](../../../../../../sources/v2/MathlibExt.md)
