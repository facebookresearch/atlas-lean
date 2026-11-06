/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceFactors

/-! Exact original eight-term source spin factors, with a genuine complete dictionary reindexing. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine original eight Y dictionary terms belonging to each physical source column. -/
def generatedTwelfthTensorSourceIndex : Fin 8 → Fin 8 → Fin 64 :=
  ![![17, 19, 21, 23, 32, 33, 36, 37],
    ![16, 18, 20, 22, 34, 35, 38, 39],
    ![24, 26, 29, 31, 56, 57, 58, 59],
    ![25, 27, 28, 30, 60, 61, 62, 63],
    ![1, 2, 5, 6, 41, 42, 44, 47],
    ![9, 10, 12, 15, 48, 50, 52, 54],
    ![8, 11, 13, 14, 49, 51, 53, 55],
    ![0, 3, 4, 7, 40, 43, 45, 46]]

/-- Every original source dictionary term has its distinct column and local term addresses. -/
theorem generatedTwelfth_tensor_source_index_bijective :
    Function.Bijective (fun p : Fin 8 × Fin 8 => generatedTwelfthTensorSourceIndex p.1 p.2) := by
  decide +kernel

/-- The complete original dictionary is genuinely equivalent to eight groups of eight terms. -/
def generatedTwelfthTensorSourceIndexEquiv : Fin 8 × Fin 8 ≃ Fin 64 :=
  Equiv.ofBijective _ generatedTwelfth_tensor_source_index_bijective

/-- Each original reindexed dictionary term has precisely its physical column. -/
theorem generatedTwelfth_tensor_source_index_coordinate : ∀ r n : Fin 8,
    (generatedFifthOddRootOutputData (generatedTwelfthTensorSourceIndex r n)).2 =
      generatedTwelfthTensorSourceCoordinate r := by
  decide +kernel

/-- The entire original integer summand, before selecting its physical column. -/
def generatedTwelfthTensorSourceSummand (j : Fin 64) (k : Fin 4096) (i : Fin 24) : ℤ :=
  generatedAxisGlobalIntSign
      (generatedFifthOddCoefficientPhaseData j + golayLabelCoefficients k 11) *
    (if (golayEncodedMask (generatedFifthOddRootOutputData j).1.val).testBit i.val then -1 else 1) *
    (if k.val % 2048 = (generatedFifthOddRootOutputData j).1.val ∧
      i = (generatedFifthOddRootOutputData j).2 then 1 else 0)

/-- Every complete canonical spin factor is the sum of only its eight original dictionary terms. -/
def generatedTwelfthTensorSourceSpinSmall (r : Fin 8) (k : Fin 4096) : ℤ :=
  ∑ n : Fin 8, generatedTwelfthTensorSourceSummand (generatedTwelfthTensorSourceIndex r n) k
    (generatedTwelfthTensorSourceCoordinate r)

/-- Original dictionary reindexing removes only the genuinely absent physical-column terms. -/
theorem generatedTwelfth_tensor_source_spin_small_actual (r : Fin 8) (k : Fin 4096) :
    generatedTwelfthTensorSourceSpin r k = generatedTwelfthTensorSourceSpinSmall r k := by
  unfold generatedTwelfthTensorSourceSpin generatedAxisGlobalFifthTensorInteger
  change (∑ j : Fin 64, generatedTwelfthTensorSourceSummand j k
    (generatedTwelfthTensorSourceCoordinate r)) = _
  rw [← generatedTwelfthTensorSourceIndexEquiv.sum_comp
    (fun j => generatedTwelfthTensorSourceSummand j k (generatedTwelfthTensorSourceCoordinate r)),
    Fintype.sum_prod_type]
  change (∑ c : Fin 8, ∑ n : Fin 8,
    generatedTwelfthTensorSourceSummand (generatedTwelfthTensorSourceIndex c n) k
      (generatedTwelfthTensorSourceCoordinate r)) = _
  rw [Finset.sum_eq_single r]
  · rfl
  · intro c _ hcr
    apply Finset.sum_eq_zero
    intro n _
    have hne : generatedTwelfthTensorSourceCoordinate r ≠
        generatedTwelfthTensorSourceCoordinate c :=
      fun h => hcr (generatedTwelfth_tensor_source_coordinate_injective h).symm
    simp [generatedTwelfthTensorSourceSummand, generatedTwelfth_tensor_source_index_coordinate, hne]
  · simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
