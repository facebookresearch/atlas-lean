/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.ToggleSwitchGeneral
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! Tests for the toggle-switch equilibrium count with general Hill exponents.

Every witness below is checked against the definitions (`IsEquilibrium`, `uDot`, `vDot`, `hill`,
`Polynomial.eval`), not through the theorems under test.

* `β = 1`, `γ = 3`, `a = 7/2`, `b = 27/4`: three equilibria with `u = 1/2`, `u = 2` and
  `u = (1 + √15)/2`, so the Descartes bound `3` is attained where the degree bound is `4`.
* `β = γ = 1`, `a = b = 2`: the single equilibrium `(1, 1)`; the equilibrium polynomial
  `u² + u - 2` also has the negative root `-2`, which is not an equilibrium, so the positivity
  condition in `isEquilibrium_one_iff` is needed.
* `γ = 0`: the equilibrium polynomial is `(2 + b) X - 2a`, not monic, so `γ ≥ 1` is needed for
  `monic_equilibriumPolyOne`.
* `β = γ = 2`, `a = b = 5/2`: the equilibria `(1/2, 2)` and `(2, 1/2)` are roots of the quintic.
-/

open Set Polynomial

namespace MathlibExtTest.Biology.Dynamics.ToggleSwitchGeneral

open MathlibExt.Biology.Dynamics.ToggleSwitch

/-! ### `β = 1`, `γ = 3`: three equilibria, degree four -/

section GammaThree

lemma sqrt15_sq : √15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)

lemma eq_half : IsEquilibrium (7 / 2) (27 / 4) 1 3 (1 / 2) 6 := by
  norm_num [IsEquilibrium, uDot, vDot, hill]

lemma eq_two : IsEquilibrium (7 / 2) (27 / 4) 1 3 2 (3 / 4) := by
  norm_num [IsEquilibrium, uDot, vDot, hill]

/-- The irrational equilibrium `u = (1 + √15)/2`, `v = 3 / (3 + √15)`, from `u² = u + 7/2`. -/
lemma eq_sqrt : IsEquilibrium (7 / 2) (27 / 4) 1 3 ((1 + √15) / 2) (3 / (3 + √15)) := by
  have h := sqrt15_sq
  have hs : 0 ≤ √15 := Real.sqrt_nonneg _
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · simp only [uDot, hill, pow_one, sub_eq_zero]
    rw [div_eq_iff (by positivity)]
    field_simp
    linear_combination (-1 : ℝ) * h
  · simp only [vDot, hill, sub_eq_zero]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-9 / 8 - 3 / 8 * √15 : ℝ) * h

/-- The equilibrium polynomial has degree `4` here (computed directly). -/
example : (equilibriumPolyOne (7 / 2) (27 / 4) 3).natDegree = 4 := by
  unfold equilibriumPolyOne
  compute_degree!

theorem gammaThree_ncard : (equilibria (7 / 2) (27 / 4) 1 3).ncard = 3 := by
  have hs : 0 < √15 := Real.sqrt_pos.2 (by norm_num)
  have h15 := sqrt15_sq
  have hfin : (equilibria (7 / 2) (27 / 4) 1 3).Finite := by
    rw [equilibria_one_eq_image (by norm_num) (by norm_num)]
    exact (finite_setOf_pos_isRoot (equilibriumPolyOne_ne_zero (by norm_num) _ _)).image _
  have hsub : ({(1 / 2, 6), (2, 3 / 4), ((1 + √15) / 2, 3 / (3 + √15))} : Set (ℝ × ℝ)) ⊆
      equilibria (7 / 2) (27 / 4) 1 3 := by
    rintro p (rfl | rfl | rfl)
    exacts [eq_half, eq_two, eq_sqrt]
  have h3 : ({(1 / 2, 6), (2, 3 / 4), ((1 + √15) / 2, 3 / (3 + √15))} :
      Set (ℝ × ℝ)).ncard = 3 := by
    rw [ncard_eq_three]
    refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> simp only [ne_eq, Prod.mk.injEq, not_and] <;>
      intro h <;> nlinarith
  have hle := ncard_le_ncard hsub hfin
  rw [h3] at hle
  exact le_antisymm (ncard_equilibria_one_le_three (by norm_num) (by norm_num)) hle

end GammaThree

/-! ### `β = γ = 1`: one equilibrium, and a negative root that is not one -/

section GammaOne

example : IsEquilibrium 2 2 1 1 1 1 := by
  norm_num [IsEquilibrium, uDot, vDot, hill]

example : equilibria 2 2 1 1 = {(1, 1)} := by
  have hmem : ((1 : ℝ), (1 : ℝ)) ∈ equilibria 2 2 1 1 := by
    norm_num [equilibria, IsEquilibrium, uDot, vDot, hill]
  obtain ⟨p, hp⟩ := ncard_eq_one.1 (ncard_equilibria_one_one (a := 2) (b := 2)
    (by norm_num) (by norm_num))
  rw [hp] at hmem ⊢
  rw [mem_singleton_iff.1 hmem]

/-- `-2` is a root of `u² + u - 2`, the `a = b = 2`, `γ = 1` equilibrium polynomial. -/
example : (equilibriumPolyOne 2 2 1).IsRoot (-2) := by
  norm_num [IsRoot, equilibriumPolyOne]

/-- No equilibrium has `u = -2`. -/
example (v : ℝ) : ¬ IsEquilibrium 2 2 1 1 (-2) v := fun h ↦ by
  have := h.1
  norm_num at this

end GammaOne

/-! ### `γ = 0`: the degree statement needs `γ ≥ 1` -/

example : ¬ (equilibriumPolyOne 1 1 0).Monic := by
  have : equilibriumPolyOne 1 1 0 = C 3 * X + C (-2) := by
    simp only [equilibriumPolyOne, pow_zero, zero_add, pow_one, mul_one, map_neg, map_add,
      map_one, map_ofNat]
    ring
  rw [this, Monic, leadingCoeff_linear (by norm_num)]
  norm_num

/-! ### `β = γ = 2`, `a = b = 5/2` -/

section BetaGammaTwo

example : IsEquilibrium (5 / 2) (5 / 2) 2 2 (1 / 2) 2 := by
  norm_num [IsEquilibrium, uDot, vDot, hill]

example : IsEquilibrium (5 / 2) (5 / 2) 2 2 2 (1 / 2) := by
  norm_num [IsEquilibrium, uDot, vDot, hill]

example : (equilibriumPolyTwo (5 / 2) (5 / 2)).IsRoot (1 / 2) := by
  norm_num [IsRoot, equilibriumPolyTwo]

example : (equilibriumPolyTwo (5 / 2) (5 / 2)).IsRoot 2 := by
  norm_num [IsRoot, equilibriumPolyTwo]

/-- The quintic has degree `5` here (computed directly). -/
example : (equilibriumPolyTwo (5 / 2) (5 / 2)).natDegree = 5 := by
  unfold equilibriumPolyTwo
  compute_degree!

/-- At least two equilibria, from the definitions; the `≤ 5` bound is the theorem. -/
example : 2 ≤ (equilibria (5 / 2) (5 / 2) 2 2).ncard ∧
    (equilibria (5 / 2) (5 / 2) 2 2).ncard ≤ 5 := by
  have hfin : (equilibria (5 / 2) (5 / 2) 2 2).Finite := by
    rw [equilibria_two_eq_image (by norm_num) (by norm_num)]
    refine Finite.image _ ?_
    have := finite_setOf_pos_isRoot (equilibriumPolyTwo_ne_zero (5 / 2) (5 / 2))
    exact this.subset fun u hu ↦ ⟨pos_of_isRoot_equilibriumPolyTwo (by norm_num) hu, hu⟩
  have hsub : ({(1 / 2, 2), (2, 1 / 2)} : Set (ℝ × ℝ)) ⊆ equilibria (5 / 2) (5 / 2) 2 2 := by
    rintro p (rfl | rfl) <;> norm_num [equilibria, IsEquilibrium, uDot, vDot, hill]
  refine ⟨?_, ncard_equilibria_two_le_five (by norm_num) (by norm_num)⟩
  have hle := ncard_le_ncard hsub hfin
  rwa [ncard_pair (by norm_num : ((1 / 2 : ℝ), (2 : ℝ)) ≠ (2, 1 / 2))] at hle

end BetaGammaTwo

end MathlibExtTest.Biology.Dynamics.ToggleSwitchGeneral
