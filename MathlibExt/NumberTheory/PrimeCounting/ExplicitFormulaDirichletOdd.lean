/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormulaDirichlet

/-!
# The explicit formula for `ψ(x, χ)`, `χ` odd

For a primitive odd Dirichlet character `χ` modulo `q` and real `x > 1` not a prime power,
`ψ(x, χ) = -∑_ρ x^ρ/ρ - L'(0, χ)/L(0, χ) + ∑_{m ≥ 0} x^{-(2m+1)}/(2m+1)`,
the sum running over the nontrivial zeros `ρ = β + iγ` of `L(s, χ)` with multiplicity, as the limit
of the truncated sums over `|γ| < R`. This is the odd case of
`DirichletCharacter.tendsto_tsum_cpow_div_zeros_explicit_formula`.

## Main statements

* `DirichletCharacter.tendsto_tsum_cpow_div_zeros_explicit_formula_of_odd`: the explicit formula
  for `ψ(x, χ)`, `χ` odd.
-/

@[expose] public section

universe u

open Complex Filter Topology

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **The explicit formula for `ψ(x, χ)`, `χ` odd.** For a primitive odd Dirichlet character `χ`
modulo `q`, a family `z` listing the zeros of `ξ(s, χ)` with multiplicity (the nontrivial zeros
`ρ = β + iγ` of `L(s, χ)`), and real `x > 1` not a prime power,
`∑_{|γ| < R} x^ρ/ρ → -L'(0, χ)/L(0, χ) + ∑_{m ≥ 0} x^{-(2m+1)}/(2m+1) - ψ(x, χ)` as `R → ∞`.
Each truncated sum has finite support. -/
theorem tendsto_tsum_cpow_div_zeros_explicit_formula_of_odd (hχ : χ.IsPrimitive) (hodd : χ.Odd)
    {ι : Type u} (z : ι → ℂ) (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w)
    {x : ℝ} (hx : 1 < x) (hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n) :
    Tendsto (fun R : ℝ => ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) atTop
      (𝓝 (-(deriv (LFunction χ) 0 / LFunction χ 0) +
        ((∑' m : ℕ, x ^ (-(2 * (m : ℤ) + 1)) / (2 * m + 1) : ℝ) : ℂ) - χ.chebyshevPsi x)) := by
  have hodd' : χ (-1) = -1 := hodd
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    rw [MulChar.one_apply isUnit_one.neg] at hodd'
    norm_num at hodd'
  have h := tendsto_tsum_cpow_div_zeros_explicit_formula hχ hχ1 z hz hx hpp
  have ha : (1 - χ (-1)) / 2 = ((1 : ℝ) : ℂ) := by
    rw [hodd']; norm_num
  rw [ha] at h
  -- the trivial zeros `-(2m + 1)`
  have hsum : ∑' m : ℕ, (x : ℂ) ^ (((1 : ℝ) : ℂ) - 2 * ((m : ℂ) + 1)) /
      (2 * ((m : ℂ) + 1) - ((1 : ℝ) : ℂ)) =
      ((∑' m : ℕ, x ^ (-(2 * (m : ℤ) + 1)) / (2 * m + 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun m => ?_
    have e : ((1 : ℝ) : ℂ) - 2 * ((m : ℂ) + 1) = ((-(2 * (m : ℤ) + 1) : ℤ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.cpow_intCast, Complex.ofReal_div, Complex.ofReal_zpow]
    congr 1
    push_cast
    ring
  rw [hsum] at h
  convert h using 2
  push_cast
  ring

end DirichletCharacter
