---
article_id: af_917ad9e65c56f47071050ab9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.GrothendieckInequalityWanted.grothendieck_inequality_real
---

# Grothendieck Inequality

There exists a universal `K>0` such that for every `m n`, real matrix `A`, real Hilbert space `H`,
and families `x : Fin m → H`, `y : Fin n → H` in the unit ball, some signs `ε i, δ j ∈ {±1}`
satisfy `|∑ A i j ⟪x i, y j⟫| ≤ K|∑ A i j ε i δ j|`. Source: A. Grothendieck, Resume de la theorie
metrique des produits tensoriels topologiques, Bol. Soc. Mat. Sao Paulo 8 (1953) 1-79, inequality;
Pisier, Grothendieck's theorem past and present, 2012; Lean states real finite-matrix scalarized
form with `Fin`-indexed unit vectors and `±1` signs, existential universal constant `K`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.GrothendieckInequality](../../../../../../sources/v2/MathlibExt.md)
