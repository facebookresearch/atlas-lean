/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSignFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthTensorSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthTensorInteger

/-! Eight original physical spin columns give the entire genuine canonical Fifth source tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The eight actual physical columns supporting the entire original canonical Fifth tensor. -/
def generatedTwelfthTensorSourceCoordinate : Fin 8 → Fin 24 := ![0, 1, 2, 3, 16, 17, 18, 19]

/-- Every original canonical source column retains its distinct physical coordinate. -/
theorem generatedTwelfth_tensor_source_coordinate_injective :
    Function.Injective generatedTwelfthTensorSourceCoordinate := by
  decide +kernel

/-- All 64 genuine original Y dictionary terms lie in these eight actual physical columns. -/
theorem generatedTwelfth_tensor_source_dictionary_columns : ∀ j : Fin 64,
    ∃ r : Fin 8, generatedTwelfthTensorSourceCoordinate r =
      (generatedFifthOddRootOutputData j).2 := by
  decide +kernel

/-- Each original spin factor is the actual complete integer coefficient of its genuine column. -/
def generatedTwelfthTensorSourceSpin (r : Fin 8) (k : Fin 4096) : ℤ :=
  generatedAxisGlobalFifthTensorInteger k (generatedTwelfthTensorSourceCoordinate r)

/-- Each physical factor is the actual original coordinate unit vector. -/
def generatedTwelfthTensorSourceSpatial (r : Fin 8) : Fin 24 → ℤ :=
  Pi.single (generatedTwelfthTensorSourceCoordinate r) 1

/-- No original canonical tensor entry lies outside its eight actual physical source columns. -/
theorem generatedTwelfth_tensor_source_integer_zero (k : Fin 4096) (i : Fin 24)
    (hi : ¬∃ r, generatedTwelfthTensorSourceCoordinate r = i) :
    generatedAxisGlobalFifthTensorInteger k i = 0 := by
  have hz : (griessConwayEncode generatedFifthAxis).2.2 (golayLabelCoefficients k) i = 0 := by
    by_contra hn
    obtain ⟨j, hj⟩ := (generatedFifth_tensor_nonzero_iff (golayLabelCoefficients k) i).mp hn
    obtain ⟨r, hr⟩ := generatedTwelfth_tensor_source_dictionary_columns j
    apply hi
    exact ⟨r, hr.trans (congrArg Prod.snd hj)⟩
  have h := generatedAxisGlobalFifthTensorInteger_coefficient k i
  rw [hz, mul_zero] at h
  exact_mod_cast h.symm

/-- Eight complete original spin and physical factors equal every canonical integer tensor entry. -/
theorem generatedTwelfth_tensor_source_integer_decomposition (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalFifthTensorInteger k i =
      ∑ r : Fin 8, generatedTwelfthTensorSourceSpin r k *
        generatedTwelfthTensorSourceSpatial r i := by
  by_cases hi : ∃ r, generatedTwelfthTensorSourceCoordinate r = i
  · obtain ⟨r, hr⟩ := hi
    subst i
    rw [Finset.sum_eq_single r]
    · simp [generatedTwelfthTensorSourceSpin, generatedTwelfthTensorSourceSpatial]
    · intro j _ hj
      have hne : generatedTwelfthTensorSourceCoordinate r ≠
          generatedTwelfthTensorSourceCoordinate j := fun h =>
        hj (generatedTwelfth_tensor_source_coordinate_injective h).symm
      simp [generatedTwelfthTensorSourceSpatial, hne]
    · simp
  · rw [generatedTwelfth_tensor_source_integer_zero k i hi]
    symm
    apply Finset.sum_eq_zero
    intro r _
    have hne : i ≠ generatedTwelfthTensorSourceCoordinate r := fun h => hi ⟨r, h.symm⟩
    simp [generatedTwelfthTensorSourceSpatial, hne]

/-- The entire actual canonical Fifth tensor is the sum of its eight genuine source factors. -/
theorem generatedTwelfth_tensor_source_actual :
    (griessConwayEncode generatedFifthAxis).2.2 =
      ∑ r : Fin 8, generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor (generatedTwelfthTensorSourceSpin r)
          (generatedTwelfthTensorSourceSpatial r)) 1 := by
  rw [generatedAxisGlobalFifthTensorInteger_eq]
  ext t i
  simp only [Finset.sum_apply, generatedAxisGlobalTensorIntegerPacket,
    generatedAxisGlobalOddTensorFactor, Nat.cast_one, one_mul, Int.cast_mul]
  rw [generatedTwelfth_tensor_source_integer_decomposition, Int.cast_sum, Finset.sum_div]
  simp only [Int.cast_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
