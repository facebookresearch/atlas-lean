/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ToricIdeal

@[expose] public section

open MvPolynomial MathlibExt.RingTheory.ToricIdeal

namespace MathlibExtTest.RingTheory.ToricIdeal

/-- The statistic of two cells that both record one unit of the same count (`x₀, x₁ ↦ t`). -/
noncomputable abbrev T₂ : Fin 2 → Unit →₀ ℕ := fun _ ↦ Finsupp.single () 1

/-- Non-vacuity: `x₀ - x₁` lies in the toric ideal of `x₀, x₁ ↦ t`. -/
example : monomial (Finsupp.single 0 1) (1 : ℚ) - monomial (Finsupp.single 1 1) 1 ∈
    toricIdeal ℚ T₂ := by
  rw [monomial_sub_monomial_mem_toricIdeal_iff]
  simp [Finsupp.linearCombination_single]

/-- The toric ideal is proper: the variable `x₀` does not lie in it. -/
example : (X 0 : MvPolynomial (Fin 2) ℚ) ∉ toricIdeal ℚ T₂ := by
  intro h
  have h0 : toricMap ℚ T₂ (monomial (Finsupp.single 0 1) 1) = 0 := h
  rw [toricMap_monomial] at h0
  exact one_ne_zero ((monomial_eq_zero).1 h0)

/-- Binomials with different statistics are excluded: `x₀ - 1 ∉ I_T`. -/
example : monomial (Finsupp.single 0 1) (1 : ℚ) - monomial 0 1 ∉ toricIdeal ℚ T₂ := by
  rw [monomial_sub_monomial_mem_toricIdeal_iff]
  simp [Finsupp.linearCombination_single]

/-- The generation theorem applies to any statistic, here that of the `2 × 2` independence
model (row and column sums). -/
example (T : Fin 2 × Fin 2 → Fin 2 ⊕ Fin 2 →₀ ℕ) :
    toricIdeal ℚ T = Ideal.span (binomials ℚ T) :=
  toricIdeal_eq_span_binomials ℚ T

end MathlibExtTest.RingTheory.ToricIdeal
