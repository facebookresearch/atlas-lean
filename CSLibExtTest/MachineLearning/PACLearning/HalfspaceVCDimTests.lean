/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.PACLearning.HalfspaceVCDim

/-! # Tests for VC dimension of affine halfspaces

One-line corollaries of the main clauses plus membership checks for the two
constant concepts. The `#print axioms` commands check that the main proofs use
only the standard axioms.
-/

open scoped InnerProductSpace

namespace CSLibExtTest.MachineLearning.PACLearning

open Cslib.MachineLearning.PACLearning

/-- In dimension `0`, the VC dimension is `1`. -/
theorem vcDim_halfspace_zero : vcDim (halfspaceClass 0) = 1 := by
  simp [halfspaceClass_vcDim]

/-- In dimension `1`, the VC dimension is `2`. -/
theorem vcDim_halfspace_one : vcDim (halfspaceClass 1) = 2 := by
  simp [halfspaceClass_vcDim]

/-- In dimension `2`, the VC dimension is `3`. -/
theorem vcDim_halfspace_two : vcDim (halfspaceClass 2) = 3 := by
  simp [halfspaceClass_vcDim]

open scoped Classical in
/-- In dimension `1`, the two points `0` and `!₂[1]` are shattered. -/
theorem halfspace_shatters_zero_one :
    SetShatters (halfspaceClass 1)
      ↑({0, !₂[1]} : Finset (EuclideanSpace ℝ (Fin 1))) := by
  have h := halfspaceClass_shatters 1
  have hwit : halfspaceWitness 1 = {0, !₂[1]} := by
    rw [halfspaceWitness]
    ext x
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨j, rfl⟩)
      · exact Or.inl rfl
      · right
        ext k
        have hk0 : k = 0 := Subsingleton.elim k 0
        have hj0 : j = 0 := Subsingleton.elim j 0
        simp [hk0, hj0]
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨0, by
          ext k
          have hk0 : k = 0 := Subsingleton.elim k 0
          simp [hk0]⟩
  rw [hwit] at h
  exact h

/-- The constant-false concept is a halfspace (zero functional, negative bias). -/
theorem halfspace_const_false_mem (d : ℕ) :
    (fun _ => false) ∈ halfspaceClass d := by
  refine ⟨0, -1, ?_⟩
  funext x
  show false = decide (0 < ⟪(0 : EuclideanSpace ℝ (Fin d)), x⟫_ℝ + -1)
  rw [inner_zero_left, zero_add]
  cases hdec : decide (0 < (-1 : ℝ)) with
  | true => exact absurd (of_decide_eq_true hdec) (by norm_num)
  | false => rfl

/-- The constant-true concept is a halfspace (zero functional, positive bias). -/
theorem halfspace_const_true_mem (d : ℕ) :
    (fun _ => true) ∈ halfspaceClass d := by
  refine ⟨0, 1, ?_⟩
  funext x
  show true = decide (0 < ⟪(0 : EuclideanSpace ℝ (Fin d)), x⟫_ℝ + 1)
  rw [inner_zero_left, zero_add]
  have h1 : decide (0 < (1 : ℝ)) = true := by simp
  rw [h1]

/-- In dimension `0`, halfspaces have finite VC dimension. -/
theorem halfspace_hasFiniteVCDim_zero : HasFiniteVCDim (halfspaceClass 0) :=
  halfspaceClass_hasFiniteVCDim 0

/-- In dimension `2`, halfspaces have finite VC dimension. -/
theorem halfspace_hasFiniteVCDim_two : HasFiniteVCDim (halfspaceClass 2) :=
  halfspaceClass_hasFiniteVCDim 2

#print axioms halfspaceClass_shatters
#print axioms halfspaceClass_not_shatters
#print axioms halfspaceClass_vcDim
#print axioms halfspaceClass_hasFiniteVCDim

end CSLibExtTest.MachineLearning.PACLearning
