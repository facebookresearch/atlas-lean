/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual triality transport of the compact Norton tensor expansion into source XYZ vectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSparseTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTrialityTensorBasis

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The two genuine source vectors produced by actual extra on a physical spin delta column. -/
noncomputable def monsterNortonExtraTensorDelta (t : SpinIndex) (j : Fin 24) : GriessSpace :=
  (1 / Real.sqrt 2 : ℝ) •
    ((qSign (t 11) * (if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val then -1
      else 1)) • trialityXYZBasis 2 (finProdFinEquiv (spinDictionaryCode t,j)) +
      qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) •
        trialityXYZBasis 0 (finProdFinEquiv (spinDictionaryCode t,j)))

/-- The inverse triality produces the corresponding actual source X and Y vectors. -/
noncomputable def monsterNortonExtraInverseTensorDelta (t : SpinIndex) (j : Fin 24) :
    GriessSpace :=
  (1 / Real.sqrt 2 : ℝ) •
    ((qSign (t 11) * (if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val then -1
      else 1)) • trialityXYZBasis 0 (finProdFinEquiv (spinDictionaryCode t,j)) +
      qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) •
        trialityXYZBasis 1 (finProdFinEquiv (spinDictionaryCode t,j)))

/-- The displayed two-vector expression is the genuine extra action for every actual spin label. -/
theorem monsterNortonExtraTensorDelta_actual (t : SpinIndex) (j : Fin 24) :
    sExtra (monsterNortonTensorLift (conwaySpinColumn (Pi.single t 1) j)) =
      monsterNortonExtraTensorDelta t j := by
  rcases spinDictionaryIndex_cases t with ht | ht
  · have hx := congrArg (fun u : SpinIndex =>
      sExtra (monsterNortonTensorLift (conwaySpinColumn (Pi.single u 1) j))) ht
    simp only [monsterNortonTensorLift_apply] at hx
    rw [monsterNortonExtra_tensor_delta_low] at hx
    have h11 : t 11 = 0 := by
      have h := congrFun ht 11
      simpa only [golayLabel_low_last] using h
    rw [monsterNortonExtraTensorDelta, h11, qSign_zero, one_mul]
    exact hx
  · have hx := congrArg (fun u : SpinIndex =>
      sExtra (monsterNortonTensorLift (conwaySpinColumn (Pi.single u 1) j))) ht
    simp only [monsterNortonTensorLift_apply] at hx
    rw [monsterNortonExtra_tensor_delta_high] at hx
    have h11 : t 11 = 1 := by
      have h := congrFun ht 11
      simpa only [golayLabel_high_last] using h
    rw [monsterNortonExtraTensorDelta, h11, qSign_one, neg_one_mul]
    exact hx

/-- The inverse expression holds for every actual spin label with its true high-bit sign. -/
theorem monsterNortonExtraInverseTensorDelta_actual (t : SpinIndex) (j : Fin 24) :
    sExtra.symm (monsterNortonTensorLift (conwaySpinColumn (Pi.single t 1) j)) =
      monsterNortonExtraInverseTensorDelta t j := by
  rcases spinDictionaryIndex_cases t with ht | ht
  · have hx := congrArg (fun u : SpinIndex =>
      sExtra.symm (monsterNortonTensorLift (conwaySpinColumn (Pi.single u 1) j))) ht
    simp only [monsterNortonTensorLift_apply] at hx
    rw [monsterNortonExtraInverse_tensor_delta_low] at hx
    have h11 : t 11 = 0 := by
      have h := congrFun ht 11
      simpa only [golayLabel_low_last] using h
    rw [monsterNortonExtraInverseTensorDelta, h11, qSign_zero, one_mul]
    exact hx
  · have hx := congrArg (fun u : SpinIndex =>
      sExtra.symm (monsterNortonTensorLift (conwaySpinColumn (Pi.single u 1) j))) ht
    simp only [monsterNortonTensorLift_apply] at hx
    rw [monsterNortonExtraInverse_tensor_delta_high] at hx
    have h11 : t 11 = 1 := by
      have h := congrFun ht 11
      simpa only [golayLabel_high_last] using h
    rw [monsterNortonExtraInverseTensorDelta, h11, qSign_one, neg_one_mul]
    exact hx

/-- The actual extra after the actual Norton word is this finite sum of source XYZ vectors. -/
theorem monsterNortonUCompactSparseTriality (u : SpinIndex) (j : Fin 24) :
    sExtra (y555NortonActualU.val
      (monsterNortonTensorLift (conwaySpinColumn (Pi.single u 1) j))) =
      (1 / 8 : ℝ) • ∑ a : XiGrayIndex,
        (monsterNortonUCompactBasisSign u a : ℝ) •
          ∑ i : Fin 24, monsterNortonUFiber.val.2.val (Pi.single j 1) i •
            monsterNortonExtraTensorDelta (monsterNortonUCompactBasisIndex u a) i := by
  rw [monsterNortonUCompactSparseTensor, map_smul, map_sum]
  simp only [map_smul, map_sum, monsterNortonExtraTensorDelta_actual]

/-- Inverse extra after the actual Norton word has the corresponding exact finite source sum. -/
theorem monsterNortonUCompactSparseInverseTriality (u : SpinIndex) (j : Fin 24) :
    sExtra.symm (y555NortonActualU.val
      (monsterNortonTensorLift (conwaySpinColumn (Pi.single u 1) j))) =
      (1 / 8 : ℝ) • ∑ a : XiGrayIndex,
        (monsterNortonUCompactBasisSign u a : ℝ) •
          ∑ i : Fin 24, monsterNortonUFiber.val.2.val (Pi.single j 1) i •
            monsterNortonExtraInverseTensorDelta (monsterNortonUCompactBasisIndex u a) i := by
  rw [monsterNortonUCompactSparseTensor, map_smul, map_sum]
  simp only [map_smul, map_sum, monsterNortonExtraInverseTensorDelta_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
