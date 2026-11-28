/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.HorocycleOrbits

open Matrix Set
open scoped MatrixGroups
open MathlibExt.Dynamics.UnipotentFlowsWanted

namespace MathlibExtTest.Dynamics.HorocycleOrbits

private abbrev project := Quotient.mk
  (QuotientGroup.rightRel (SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin 2)).range)

-- The orbit through the identity has exactly the integral periods.
example (s t : ℝ) :
    project (horocycle s) = project (horocycle t) ↔ ∃ n : ℤ, s = t + n := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := QuotientGroup.rightRel_apply.mp (Quotient.exact h.symm)
    have heq := congrArg (fun g : SL(2, ℝ) => g 1 0) hγ
    change (γ 1 0 : ℝ) =
      ((!![1, 0; s, 1] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1, 0; t, 1]).adjugate) 1 0 at heq
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at heq
    exact ⟨γ 1 0, by linarith⟩
  · rintro ⟨n, rfl⟩
    let γ : SL(2, ℤ) := ⟨!![1, 0; n, 1], by simp [Matrix.det_fin_two]⟩
    have h : horocycle (t + n) = SpecialLinearGroup.map (Int.castRingHom ℝ) γ * horocycle t := by
      apply SpecialLinearGroup.ext
      intro i j
      change !![1, 0; t + (n : ℝ), 1] i j =
        ((!![1, 0; n, 1].map (Int.castRingHom ℝ)) * !![1, 0; t, 1]) i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
    symm
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr ⟨γ, by simp [h, mul_assoc]⟩)

-- Apply the dichotomy to compute the two possible orbit closures.
example (x : SL(2, ℝ)) :
    let orbit := range fun t : ℝ => project (x * horocycle t)
    closure orbit = orbit ∨ closure orbit = univ := by
  rcases horocycle_orbit_isClosed_or_dense x with h | h
  · exact Or.inl h.closure_eq
  · exact Or.inr h.closure_eq

end MathlibExtTest.Dynamics.HorocycleOrbits
