/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormulaDirichlet
import MathlibExt.NumberTheory.LSeries.RiemannZetaResidues
import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormulaContour

/-!
# The explicit formula for `ψ(x, χ)`, `χ` even

For a primitive even nonprincipal Dirichlet character `χ` and `x > 1` not a prime power,
`ψ(x, χ) = -∑_ρ x^ρ/ρ - log x - b(χ) - ½ log (1 - x⁻²)`, where `ρ` runs over the nontrivial zeros of
`L(s, χ)` with multiplicity and `b(χ)` is the constant term of `L'/L(s, χ)` at `s = 0`. The zero sum
converges conditionally, as the limit of its truncations to `|Im ρ| < R`. This is the even case of
`DirichletCharacter.tendsto_tsum_cpow_div_zeros_explicit_formula`: the trivial zeros `-2m`
contribute `∑_{m ≥ 1} x^{-2m}/(2m) = -½ log (1 - x⁻²)`.

## Main statements

* `DirichletCharacter.tendsto_tsum_cpow_div_zeros_explicit_formula_of_even`: the explicit formula
  for `ψ(x, χ)`, `χ` even.
-/

@[expose] public section

universe u

open Complex Filter Topology

namespace DirichletCharacter

/-- **The explicit formula for `ψ(x, χ)`, `χ` even.** For a primitive even nonprincipal Dirichlet
character `χ` modulo `q` and real `x > 1` not a prime power,
`∑_ρ x^ρ/ρ = -ψ(x, χ) - log x - b(χ) - ½ log (1 - x⁻²)`, where `b(χ)` is the constant term of
`L'/L(s, χ)` at `s = 0` (`DirichletCharacter.logDerivConstAtZero`). The sum over the nontrivial
zeros `ρ = β + iγ`, listed with multiplicity by any family `z` listing the zeros of `ξ(s, χ)`,
converges only conditionally: it is the limit as `R → ∞` of its truncations to `|γ| < R`, each
with finite support. -/
theorem tendsto_tsum_cpow_div_zeros_explicit_formula_of_even {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (heven : χ.Even)
    {ι : Type u} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) (hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n) :
    Tendsto (fun R : ℝ => ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) atTop
      (𝓝 (-χ.chebyshevPsi x - (Real.log x : ℂ) - χ.logDerivConstAtZero -
        ((1 / 2 * Real.log (1 - x ^ (-2 : ℤ)) : ℝ) : ℂ))) := by
  have h := tendsto_tsum_cpow_div_zeros_explicit_formula hχ hχ1 z hz hx hpp
  have ha : (1 - χ (-1)) / 2 = ((0 : ℝ) : ℂ) := by
    rw [show χ (-1) = 1 from heven]; simp
  rw [ha] at h
  -- the trivial zeros `-2m`
  have hsum : ∑' m : ℕ, (x : ℂ) ^ (((0 : ℝ) : ℂ) - 2 * ((m : ℂ) + 1)) /
      (2 * ((m : ℂ) + 1) - ((0 : ℝ) : ℂ)) = -(((1 / 2 * Real.log (1 - x ^ (-2 : ℤ))) : ℝ) : ℂ) := by
    refine tendsto_nhds_unique (tendsto_sum_cpow_sub_two_mul_div_two_mul_sub hx zero_le_one) ?_
    have h2 := tendsto_sum_cpow_neg_two_mul_div_two_mul hx
    push_cast at h2 ⊢
    simpa only [zero_sub, sub_zero, neg_mul] using h2
  rw [hsum] at h
  convert h using 2
  push_cast
  ring

end DirichletCharacter
