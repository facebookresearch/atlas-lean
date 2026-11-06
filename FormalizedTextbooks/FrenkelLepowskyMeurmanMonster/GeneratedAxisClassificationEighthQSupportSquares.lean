/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQSupportExact

/-! The original rank-eleven spin support contains exactly one coordinate in each omega pair. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original support equation gives the exact square on every allowed coordinate. -/
theorem generatedEighth_spin_allowed_square (t : SpinIndex)
    (ht : spinDot (golayLabelCoefficients 3079) t = 0) :
    (generatedEighthSpinState t) ^ 2 = (1 / 1024 : ℝ) := by
  apply generatedEighth_spin_kernel_square_exact
  funext j
  exact ht

/-- A coordinate violating the original fixing modulation is zero. -/
theorem generatedEighth_spin_forbidden_zero (t : SpinIndex)
    (ht : spinDot (golayLabelCoefficients 3079) t ≠ 0) : generatedEighthSpinState t = 0 := by
  by_contra h
  have he := congrFun (generatedEighth_spin_support_equations t h) (0 : Fin 1)
  exact ht he

private theorem modulation_omega :
    spinDot (golayLabelCoefficients 3079) (Pi.single (11 : Fin 12) 1) = 1 := by
  decide +kernel

private theorem bit_cases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel

/-- Every original omega pair has one zero coordinate and the exact allowed magnitude. -/
theorem generatedEighth_spin_omega_difference_square (t : SpinIndex) :
    (generatedEighthSpinState t -
      generatedEighthSpinState (t + Pi.single (11 : Fin 12) 1)) ^ 2 =
        (1 / 1024 : ℝ) := by
  by_cases ht : spinDot (golayLabelCoefficients 3079) t = 0
  · have hu : spinDot (golayLabelCoefficients 3079)
        (t + Pi.single (11 : Fin 12) 1) ≠ 0 := by
      rw [spinDot_add_right, ht, modulation_omega, zero_add]
      exact one_ne_zero
    rw [generatedEighth_spin_forbidden_zero _ hu, sub_zero]
    exact generatedEighth_spin_allowed_square t ht
  · have he : spinDot (golayLabelCoefficients 3079) t = 1 :=
      (bit_cases _).resolve_left ht
    have hu : spinDot (golayLabelCoefficients 3079)
        (t + Pi.single (11 : Fin 12) 1) = 0 := by
      rw [spinDot_add_right, he, modulation_omega]
      decide +kernel
    rw [generatedEighth_spin_forbidden_zero t ht, zero_sub, neg_sq]
    exact generatedEighth_spin_allowed_square _ hu

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
