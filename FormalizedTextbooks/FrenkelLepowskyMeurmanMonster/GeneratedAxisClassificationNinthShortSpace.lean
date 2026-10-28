/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthProjection
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The recovered real subspace has dimension eight and contains the original eight short lines. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual short-label catalogue entries underlying the recovered eight directions. -/
def generatedNinthLowShortIndex (r : Fin 8) : GriessShortIndex :=
  Sum.inl ((generatedNinthLowRootData r).1,
    griessPairIndex (generatedNinthLowRootData r).2.1 (generatedNinthLowRootData r).2.2
      (ne_of_lt (generatedNinthLowRootData_lt r)))

/-- Each recovered direction is an actual preferred shortest-vector line. -/
theorem generatedNinth_low_short_integral (r : Fin 8) :
    griessShortIntegral (generatedNinthLowShortIndex r) =
      fun i => 4 * generatedNinthLowRootCoordinates r i := by
  simp only [generatedNinthLowShortIndex, griessShortIntegral, griessPairIndex_coordinates,
    generatedNinthLowRootData_lt r, ite_true]
  funext i
  unfold generatedNinthLowRootCoordinates
  have hn := ne_of_lt (generatedNinthLowRootData_lt r)
  split_ifs <;> simp_all


/-- The actual real short vector is the displayed direction in Conway normalization. -/
theorem generatedNinth_low_short_vector (r : Fin 8) :
    griessShortVector (generatedNinthLowShortIndex r) =
      (4 / Real.sqrt 8 : ℝ) • generatedNinthLowRootMatrix r := by
  funext i
  simp only [griessShortVector, generatedNinth_low_short_integral, Int.cast_mul,
    Int.cast_ofNat, generatedNinthLowRootMatrix, Pi.smul_apply, smul_eq_mul]
  ring

/-- The recovered real subspace is the image of the eight original directions. -/
def generatedNinthLowSpace : Submodule ℝ (Fin 24 → ℝ) :=
  LinearMap.range (Matrix.toLin' generatedNinthLowRootMatrix.transpose)

/-- The original Gram certificate makes the eight-direction embedding injective. -/
theorem generatedNinth_low_space_map_injective :
    Function.Injective (Matrix.toLin' generatedNinthLowRootMatrix.transpose) := by
  intro v w h
  change generatedNinthLowRootMatrix.transpose *ᵥ v =
    generatedNinthLowRootMatrix.transpose *ᵥ w at h
  have he := congrArg (fun x => generatedNinthLowRootMatrix *ᵥ x) h
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    generatedNinth_low_root_real_gram] at he
  have hs : (2 : ℝ) • v = (2 : ℝ) • w := by
    simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using he
  exact (smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)) hs

/-- The original lower real subspace has dimension exactly eight. -/
theorem generatedNinth_low_space_finrank : Module.finrank ℝ generatedNinthLowSpace = 8 := by
  unfold generatedNinthLowSpace
  rw [LinearMap.finrank_range_of_inj generatedNinth_low_space_map_injective]
  simp

/-- Each original genuine short line lies in the actual recovered real subspace. -/
theorem generatedNinth_low_short_mem (r : Fin 8) :
    griessShortVector (generatedNinthLowShortIndex r) ∈ generatedNinthLowSpace := by
  refine ⟨(4 / Real.sqrt 8 : ℝ) • Pi.single r 1, ?_⟩
  change generatedNinthLowRootMatrix.transpose *ᵥ ((4 / Real.sqrt 8 : ℝ) • Pi.single r 1) = _
  rw [Matrix.mulVec_smul, Matrix.mulVec_single, generatedNinth_low_short_vector]
  simp [Matrix.col]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
