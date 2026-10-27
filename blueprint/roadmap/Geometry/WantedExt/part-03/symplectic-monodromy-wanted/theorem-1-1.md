---
article_id: af_a885919330f27ad8fab8a2fb
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Geometry.SymplecticMonodromyWanted.SymplecticMonodromy.theorem_1_1
---

# Theorem 1 1

Statement of Theorem 1.1:

Let `(fₜ)` be a continuous family of power series. If the Milnor number `μ(fₜ)` is independent
of `t` and finite, then the multiplicity `ν(fₜ)` is also independent of `t`.

Note that what the paper calls "multiplicity" is exactly `MvPowerSeries.order`; see
for instance `MvPowerSeries.order_eq_nat`.

Even though not explicitly mentioned by the paper, we need to require the constant coefficients
to vanish. This is equivalent to saying that `fₜ` is a germ `(ℂⁿ, 0) → (ℂ, 0)`, i.e. that it's
a family of isolated hypersurface singularities through the origin, which is mentioned both in the
abstract and in Corollary 1.3, but not explicitly in Theorem 1.1. For an example showing that we
need this assumption, consider `fₜ = z + t`: The Milnor number is `0` for all `t` (the Jacobian quotient is the zero module since the derivative ideal contains `1`), but
`order(f₀) = 1` while `order(f₁) = 0`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Geometry.SymplecticMonodromyWanted](../../../../../sources/v2/WantedExt.md)
- J. Fernández de Bobadilla and T. Pełka, `Symplectic monodromy at radius zero and equimultiplicity of μ-constant families`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-SymplecticMonodromy.lean Via leanprover/lean-eval@38361be, problem `annals_symplectic_monodromy`.
