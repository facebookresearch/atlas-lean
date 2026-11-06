/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorPairing

/-! Exact column formulas for the actual local tensor representation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every actual physical tensor is the sum of its twenty-four coordinate columns. -/
theorem generatedAxisGlobalTensor_columns (T : SpinIndex → Fin 24 → ℝ) :
    T = ∑ j : Fin 24, conwayTensorCoordinates
      ((fun t => T t j) ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ)) := by
  funext t i
  simp only [Finset.sum_apply, conwayTensorCoordinates_tmul, Pi.single_apply]
  simp

/-- The genuine local representation acts on a pure tensor by its defining two factors. -/
theorem generatedAxisGlobalTensor_local_tmul (f : localFiberSubgroup)
    (a : SpinSpace) (b : Fin 24 → ℝ) :
    localTensorRepresentation f (conwayTensorCoordinates (a ⊗ₜ[ℝ] b)) =
      conwayTensorCoordinates (f.val.1.val a ⊗ₜ[ℝ] f.val.2.val b) := by
  rw [localTensorRepresentation_coordinates]
  change conwayTensorCoordinates (TensorProduct.congr _ _ (a ⊗ₜ[ℝ] b)) = _
  rw [TensorProduct.congr_tmul]

/-- Each actual local output coordinate is the exact sum of its twenty-four spin columns. -/
theorem generatedAxisGlobalTensor_local_coordinate (f : localFiberSubgroup)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation f T t i =
      ∑ j : Fin 24, f.val.1.val (fun u => T u j) t *
        f.val.2.val (Pi.single j 1) i := by
  have h := congrArg (localTensorRepresentation f) (generatedAxisGlobalTensor_columns T)
  rw [map_sum] at h
  have ht := congrArg (fun U => U t i) h
  simp only [Finset.sum_apply, generatedAxisGlobalTensor_local_tmul,
    conwayTensorCoordinates_tmul] at ht
  exact ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
