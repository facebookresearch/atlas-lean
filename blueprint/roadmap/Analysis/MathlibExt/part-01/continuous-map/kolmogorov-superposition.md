---
article_id: af_9c7563dff27db89f88c54afb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.ContinuousMap.KolmogorovSuperpositionWanted.kolmogorov_superposition
---

# Kolmogorov Superposition

For every `n ≥ 2` there exist inner `ψ : Fin (2n+1) → Fin n → C(Icc 0 1, ℝ)` depending only on `n`
such that every `f : C((Fin n → Icc 0 1), ℝ)` is `f x = ∑ q, φ_q(∑ p, ψ_qp (x_p))` for some outer
`φ : Fin (2n+1) → C(ℝ, ℝ)`. Source: Kolmogorov superposition theorem, A. N. Kolmogorov, Dokl.
Akad. Nauk SSSR 114 (1957) 953–956, refined Arnold 1957; see Braun–Griebel, Acta Numer. 2009
review; Lean is n ≥ 2 exact cardinal Fin (2n+1) with inner ψ in C(Icc 0 1, ℝ) independent of f
and outer φ in C(ℝ, ℝ), compact-source specialization [0, 1]^n as Fin n → Icc.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.ContinuousMap.KolmogorovSuperposition](../../../../../sources/v2/MathlibExt.md)
