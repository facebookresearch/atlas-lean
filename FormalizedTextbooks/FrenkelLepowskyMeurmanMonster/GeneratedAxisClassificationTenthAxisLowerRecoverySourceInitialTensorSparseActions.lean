/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceInitialTensorSparseData

/-! Ungated proof drafts binding every sparse coordinate to the actual generatedFifthAxis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

/-- There are exactly 64 original paired atoms. This is a closed finite type computation. -/
theorem generatedTenth_source_initial_tensor_sparse_card :
    Fintype.card GeneratedTenthSourceInitialTensorSparseIndex = 64 := by
  decide +kernel

/-- The source label is exactly the original root dictionary label. -/
theorem generatedTenth_source_initial_tensor_sparse_original_label
    (p : GeneratedTenthSourceInitialTensorSparseIndex) :
    (generatedFifthOddRootOutputData (generatedTwelfthTensorSourceIndex p.1 p.2)).1.val =
      (generatedTenthSourceInitialTensorSparseLow p).val := by
  exact congrArg Fin.val (generatedTwelfth_tensor_source_initial_labels p.1 p.2)

/-- The physical coordinate is exactly the original root dictionary coordinate. -/
theorem generatedTenth_source_initial_tensor_sparse_original_coordinate
    (p : GeneratedTenthSourceInitialTensorSparseIndex) :
    (generatedFifthOddRootOutputData (generatedTwelfthTensorSourceIndex p.1 p.2)).2 =
      generatedTenthSourceInitialTensorSparseCoordinate p := by
  exact generatedTwelfth_tensor_source_index_coordinate p.1 p.2

/-- The displayed signs retain both original phase and physical code contributions. -/
theorem generatedTenth_source_initial_tensor_sparse_original_sign
    (p : GeneratedTenthSourceInitialTensorSparseIndex) :
    generatedAxisGlobalIntSign
        (generatedFifthOddCoefficientPhaseData (generatedTwelfthTensorSourceIndex p.1 p.2)) *
      (if (golayEncodedMask
        (generatedFifthOddRootOutputData (generatedTwelfthTensorSourceIndex p.1 p.2)).1.val).testBit
          (generatedTenthSourceInitialTensorSparseCoordinate p).val then -1 else 1) =
      generatedTenthSourceInitialTensorSparseSign p := by
  exact generatedTwelfth_tensor_source_initial_coefficients p.1 p.2

/-- Every original paired atom has a unit sign; this finite check is still uncompiled. -/
theorem generatedTenth_source_initial_tensor_sparse_sign_unit :
    ∀ p : GeneratedTenthSourceInitialTensorSparseIndex,
      generatedTenthSourceInitialTensorSparseSign p = 1 ∨
        generatedTenthSourceInitialTensorSparseSign p = -1 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
-- The64 by64 literal label comparison is a bounded kernel computation.
/-- Distinct original terms retain distinct low spin labels. This draft is uncompiled. -/
theorem generatedTenth_source_initial_tensor_sparse_low_injective :
    Function.Injective generatedTenthSourceInitialTensorSparseLow := by
  decide +kernel

/-- The top bit gives the exact difference of the lower and upper coordinate indicators. -/
theorem generatedTenth_source_initial_tensor_sparse_pair
    (d : Fin 2048) (k : Fin 4096) :
    generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
        (if k.val % 2048 = d.val then (1 : ℤ) else 0) =
      (if k.val = d.val then (1 : ℤ) else 0) -
        (if k.val = d.val + 2048 then (1 : ℤ) else 0) := by
  have hk := k.isLt
  have hd := d.isLt
  by_cases hlow : k.val < 2048
  · have hc := (golayLabel_last_zero k).mpr hlow
    have hm : k.val % 2048 = k.val := Nat.mod_eq_of_lt hlow
    have hhigh : k.val ≠ d.val + 2048 := by omega
    simp [generatedAxisGlobalIntSign, hc, hm, hhigh]
  · have hc : golayLabelCoefficients k 11 ≠ 0 := by
      intro h
      exact hlow ((golayLabel_last_zero k).mp h)
    have hm : k.val % 2048 = k.val - 2048 := by omega
    have hn : k.val ≠ d.val := by omega
    have he : k.val - 2048 = d.val ↔ k.val = d.val + 2048 := by omega
    simp [generatedAxisGlobalIntSign, hc, hm, hn, he]
    split_ifs <;> norm_num

/-- Every original spin column is the sum of its eight paired sparse atoms. -/
theorem generatedTenth_source_initial_tensor_sparse_spin (r : Fin 8) (k : Fin 4096) :
    generatedTwelfthTensorSourceSpin r k =
      ∑ n : Fin 8,
        generatedTenthSourceInitialTensorSparseSign (r, n) *
          ((if k = generatedTenthSourceInitialTensorSparseLow (r, n) then 1 else 0) -
            (if k = generatedTenthSourceInitialTensorSparseHigh (r, n) then 1 else 0)) := by
  rw [generatedTwelfth_tensor_source_spin_small_actual,
    generatedTwelfth_tensor_source_spin_fast_actual,
    generatedTwelfth_tensor_source_initial_sparse_actual]
  unfold generatedTwelfthTensorSourceInitialSparseSpin
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hp := generatedTenth_source_initial_tensor_sparse_pair
    (generatedTwelfthTensorSourceInitialLabel r n) k
  have hl : k = generatedTenthSourceInitialTensorSparseLow (r, n) ↔
      k.val = (generatedTwelfthTensorSourceInitialLabel r n).val := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  have hh : k = generatedTenthSourceInitialTensorSparseHigh (r, n) ↔
      k.val = (generatedTwelfthTensorSourceInitialLabel r n).val + 2048 := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  change generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
      (if k.val % 2048 = (generatedTwelfthTensorSourceInitialLabel r n).val
        then generatedTwelfthTensorSourceInitialCoefficient r n else 0) =
    generatedTwelfthTensorSourceInitialCoefficient r n *
      ((if k = generatedTenthSourceInitialTensorSparseLow (r, n) then 1 else 0) -
        (if k = generatedTenthSourceInitialTensorSparseHigh (r, n) then 1 else 0))
  simp only [hl, hh]
  have hi : (if k.val % 2048 = (generatedTwelfthTensorSourceInitialLabel r n).val
      then generatedTwelfthTensorSourceInitialCoefficient r n else 0) =
    generatedTwelfthTensorSourceInitialCoefficient r n *
      (if k.val % 2048 = (generatedTwelfthTensorSourceInitialLabel r n).val
        then (1 : ℤ) else 0) := by
    split_ifs <;> ring
  rw [hi]
  calc
    _ = generatedTwelfthTensorSourceInitialCoefficient r n *
        (generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
          (if k.val % 2048 = (generatedTwelfthTensorSourceInitialLabel r n).val
            then (1 : ℤ) else 0)) := by ring
    _ = _ := by rw [hp]

/-- The complete integer tensor equality includes all 4096 by 24 coordinates. -/
theorem generatedTenth_source_initial_tensor_sparse_integer (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalFifthTensorInteger k i =
      generatedTenthSourceInitialTensorSparseInteger k i := by
  rw [generatedTwelfth_tensor_source_integer_decomposition]
  unfold generatedTenthSourceInitialTensorSparseInteger
  apply Finset.sum_congr rfl
  intro r _
  rw [generatedTenth_source_initial_tensor_sparse_spin, Finset.sum_mul]
  rfl

/-- The normalization is inherited from the proved actual Fifth tensor, not numerical data. -/
theorem generatedTenth_source_initial_tensor_sparse_coordinate (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedFifthAxis).2.2 t i =
      (generatedTenthSourceInitialTensorSparseInteger
        (generatedAxisGlobalSpinLabel t) i : ℝ) / Real.sqrt 2 := by
  rw [generatedAxisGlobalFifthTensorInteger_eq]
  dsimp only
  rw [generatedTenth_source_initial_tensor_sparse_integer]

/-- The genuine actual initial tensor is the finite sum of all 64 normalized paired atoms. -/
theorem generatedTenth_source_initial_tensor_sparse_actual :
    (griessConwayEncode generatedFifthAxis).2.2 =
      ∑ r : Fin 8, ∑ n : Fin 8, generatedTenthSourceInitialTensorSparseAtom (r, n) := by
  funext (t : SpinIndex) (i : Fin 24)
  rw [generatedTenth_source_initial_tensor_sparse_coordinate]
  simp only [Finset.sum_apply, generatedTenthSourceInitialTensorSparseAtom]
  unfold generatedTenthSourceInitialTensorSparseInteger
  simp only [Int.cast_sum, Finset.sum_div]

/-- The same actual equality indexed directly by the finite type of exactly 64 atoms. -/
theorem generatedTenth_source_initial_tensor_sparse_actual_sum :
    (griessConwayEncode generatedFifthAxis).2.2 =
      ∑ p : GeneratedTenthSourceInitialTensorSparseIndex,
        generatedTenthSourceInitialTensorSparseAtom p := by
  rw [Fintype.sum_prod_type]
  exact generatedTenth_source_initial_tensor_sparse_actual

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

