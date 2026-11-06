/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhPermutationMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXi

/-! Actual coordinate numerator for the original simultaneous Xi conjugate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Explicit inverse physical addresses of the checked original thirteen-letter permutation. -/
def generatedSeventhXiPlaneInverse : Fin 24 → Fin 24 :=
  ![4, 11, 21, 14, 15, 8, 6, 23, 12, 7, 22, 10, 3, 0, 2, 16, 19, 18, 1, 17, 5, 13, 9, 20]

/-- The numerator of the original spatial Xi conjugate, with denominator two. -/
def generatedSeventhXiPlaneMatrixNumerator : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  co1XiNumerator (generatedSeventhXiPlaneInverse i) (generatedSeventhXiPlaneInverse j)

/-- Every inverse address binds to the genuine original spatial permutation. -/
theorem generatedSeventhXiPlanePermutation_inverse (i : Fin 24) :
    generatedSeventhXiPlanePermutation.val.symm i = generatedSeventhXiPlaneInverse i := by
  apply generatedSeventhXiPlanePermutation.val.injective
  rw [Equiv.apply_symm_apply, generatedSeventhXiPlanePermutation_forward]
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
