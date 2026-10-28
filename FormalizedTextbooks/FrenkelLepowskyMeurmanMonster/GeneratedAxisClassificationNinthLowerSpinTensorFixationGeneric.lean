/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompatibility

/-! Actual tensor fixation from an abstract complete circuit equation and whole source bindings. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every literal spatial denominator is positive. -/
theorem generatedNinth_lower_spin_tensor_generic_spatial_denominator_positive : ∀ i : Fin 11,
    0 < generatedNinthLowerSpinTensorSpatialDenominator i := by
  decide +kernel

/-- Two full source equalities turn the exact compact circuit into genuine local tensor fixation.
The input equality covers every actual spin coordinate and all 24 physical columns. -/
theorem generatedNinth_lower_spin_tensor_fix_of_circuit_and_source_caches (i : Fin 11)
    (T : SpinIndex → Fin 24 → ℝ)
    (hinput : ∀ t j, 64 * Real.sqrt 2 * T t j =
      (generatedNinthLowerSpinTensorInputInteger (nortonUIntegerLabel t) j : ℝ))
    (hspatial : ∀ j k, (generatedNinthLowerSpinTensorSpatialDenominator i : ℝ) *
      (generatedNinthLowerSpinDirectIsometry i).val (Pi.single k 1) j =
        (generatedNinthLowerSpinTensorSpatialNumerator i j k : ℝ))
    (hcircuit : ∀ j : Fin 24,
      (generatedNinthLowerSpinCompact i).val
        (nortonUIntegerEmbed (fun n => generatedNinthLowerSpinTensorSpatialInteger i n j)) =
      (generatedNinthLowerSpinTensorSpatialDenominator i : ℝ) •
        nortonUIntegerEmbed (fun n => generatedNinthLowerSpinTensorInputInteger n j)) :
    localTensorRepresentation (generatedNinthLowerSpinDirectFiber i) T = T := by
  let c : ℝ := 64 * Real.sqrt 2
  let d : ℝ := generatedNinthLowerSpinTensorSpatialDenominator i
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (ne_of_gt
      (generatedNinth_lower_spin_tensor_generic_spatial_denominator_positive i))
  have hcd : c * d ≠ 0 := mul_ne_zero (by dsimp [c]; positivity) hd
  funext t j
  let U : SpinSpace := fun u => ∑ k : Fin 24,
    (generatedNinthLowerSpinDirectIsometry i).val (Pi.single k 1) j * T u k
  have hscaled : (c * d) • U =
      nortonUIntegerEmbed (fun n => generatedNinthLowerSpinTensorSpatialInteger i n j) := by
    ext u
    simp only [U, Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed,
      generatedNinthLowerSpinTensorSpatialInteger, Int.cast_sum, Int.cast_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← hspatial j k, ← hinput u k]
    dsimp [c, d]
    ring
  have haction : (c * d) • (generatedNinthLowerSpinCompact i).val U =
      d • nortonUIntegerEmbed (fun n => generatedNinthLowerSpinTensorInputInteger n j) := by
    rw [← map_smul, hscaled, hcircuit j]
  have htarget : d • nortonUIntegerEmbed
      (fun n => generatedNinthLowerSpinTensorInputInteger n j) =
        (c * d) • (fun u => T u j) := by
    ext u
    simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed]
    rw [← hinput u j]
    dsimp [c]
    ring
  rw [htarget] at haction
  have hcoordinate : (generatedNinthLowerSpinCompact i).val U t = T t j := by
    have hh := congrArg (fun f : SpinSpace => f t) haction
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    exact mul_left_cancel₀ hcd hh
  have hlinear : (generatedNinthLowerSpinCompact i).val U t =
      ∑ k : Fin 24, (generatedNinthLowerSpinDirectIsometry i).val (Pi.single k 1) j *
        (generatedNinthLowerSpinCompact i).val (fun u => T u k) t := by
    have hU : U = ∑ k : Fin 24,
        (generatedNinthLowerSpinDirectIsometry i).val (Pi.single k 1) j •
          (fun u => T u k) := by
      funext u
      simp only [U, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hU]
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [generatedFourth_local_tensor_columns]
  change (∑ k : Fin 24,
    (generatedNinthLowerSpinDirectIsometry i).val (Pi.single k 1) j *
      (generatedNinthLowerSpinCompact i).val (fun u => T u k) t) = T t j
  rw [← hlinear]
  exact hcoordinate

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
