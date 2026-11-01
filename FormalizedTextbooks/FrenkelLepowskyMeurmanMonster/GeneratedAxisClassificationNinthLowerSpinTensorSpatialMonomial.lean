/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData

/-! Complete signed monomial matrices for the first four original oriented spatial candidates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private theorem integer_monomial (N : Matrix (Fin 24) (Fin 24) ℤ)
    (p : Fin 24 → Fin 24) (s : Fin 24 → ℤ)
    (hN : ∀ i k, N i k = s i * if p i = k then 1 else 0)
    (v : Fin 24 → ℤ) (j : Fin 24) :
    ∑ k : Fin 24, N j k * v k = s j * v (p j) := by
  simp_rw [hN]
  simp

/-- Every original source coordinate pulled back by generator 0. -/
def generatedNinthLowerSpinTensorMonomialPermutation00 : Fin 24 → Fin 24 :=
  ![0, 16, 2, 18, 4, 20, 6, 22, 11, 12, 13, 8,
    9, 10, 15, 14, 1, 17, 3, 19, 5, 21, 7, 23]

/-- Every original signed row of the oriented generator 0. -/
def generatedNinthLowerSpinTensorMonomialSign00 : Fin 24 → ℤ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1,
    -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1]

private theorem complete_entries_00 : ∀ j k : Fin 24,
    generatedNinthLowerSpinTensorSpatialNumerator 0 j k =
      generatedNinthLowerSpinTensorMonomialSign00 j *
        if generatedNinthLowerSpinTensorMonomialPermutation00 j = k then 1 else 0 := by
  decide +kernel

/-- Original generator 0 spatial replay is the exact full signed single pullback. -/
theorem generatedNinth_lower_spin_tensor_spatial_monomial_00 (n : Fin 4096) (j : Fin 24) :
    generatedNinthLowerSpinTensorSpatialInteger 0 n j =
      generatedNinthLowerSpinTensorMonomialSign00 j *
        generatedNinthLowerSpinTensorInputInteger n
          (generatedNinthLowerSpinTensorMonomialPermutation00 j) := by
  unfold generatedNinthLowerSpinTensorSpatialInteger
  exact integer_monomial _ _ _ complete_entries_00 _ j

/-- Every original source coordinate pulled back by generator 1. -/
def generatedNinthLowerSpinTensorMonomialPermutation01 : Fin 24 → Fin 24 :=
  ![23, 16, 4, 3, 2, 5, 17, 22, 8, 9, 13, 11,
    12, 10, 15, 14, 1, 6, 18, 21, 20, 19, 7, 0]

/-- Every original signed row of the oriented generator 1. -/
def generatedNinthLowerSpinTensorMonomialSign01 : Fin 24 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, -1, 1, -1, -1, -1, -1,
    -1, -1, -1, -1, 1, -1, -1, 1, -1, 1, 1, -1]

private theorem complete_entries_01 : ∀ j k : Fin 24,
    generatedNinthLowerSpinTensorSpatialNumerator 1 j k =
      generatedNinthLowerSpinTensorMonomialSign01 j *
        if generatedNinthLowerSpinTensorMonomialPermutation01 j = k then 1 else 0 := by
  decide +kernel

/-- Original generator 1 spatial replay is the exact full signed single pullback. -/
theorem generatedNinth_lower_spin_tensor_spatial_monomial_01 (n : Fin 4096) (j : Fin 24) :
    generatedNinthLowerSpinTensorSpatialInteger 1 n j =
      generatedNinthLowerSpinTensorMonomialSign01 j *
        generatedNinthLowerSpinTensorInputInteger n
          (generatedNinthLowerSpinTensorMonomialPermutation01 j) := by
  unfold generatedNinthLowerSpinTensorSpatialInteger
  exact integer_monomial _ _ _ complete_entries_01 _ j

/-- Every original source coordinate pulled back by generator 2. -/
def generatedNinthLowerSpinTensorMonomialPermutation02 : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

/-- Every original signed row of the oriented generator 2. -/
def generatedNinthLowerSpinTensorMonomialSign02 : Fin 24 → ℤ :=
  ![1, 1, 1, -1, 1, -1, 1, 1, -1, -1, 1, -1,
    -1, 1, 1, 1, 1, 1, -1, 1, -1, 1, 1, 1]

private theorem complete_entries_02 : ∀ j k : Fin 24,
    generatedNinthLowerSpinTensorSpatialNumerator 2 j k =
      generatedNinthLowerSpinTensorMonomialSign02 j *
        if generatedNinthLowerSpinTensorMonomialPermutation02 j = k then 1 else 0 := by
  decide +kernel

/-- Original generator 2 spatial replay is the exact full signed single pullback. -/
theorem generatedNinth_lower_spin_tensor_spatial_monomial_02 (n : Fin 4096) (j : Fin 24) :
    generatedNinthLowerSpinTensorSpatialInteger 2 n j =
      generatedNinthLowerSpinTensorMonomialSign02 j *
        generatedNinthLowerSpinTensorInputInteger n
          (generatedNinthLowerSpinTensorMonomialPermutation02 j) := by
  unfold generatedNinthLowerSpinTensorSpatialInteger
  exact integer_monomial _ _ _ complete_entries_02 _ j

/-- Every original source coordinate pulled back by generator 3. -/
def generatedNinthLowerSpinTensorMonomialPermutation03 : Fin 24 → Fin 24 :=
  ![0, 16, 4, 8, 2, 9, 17, 7, 3, 5, 10, 18,
    20, 13, 15, 14, 1, 6, 11, 19, 12, 21, 22, 23]

/-- Every original signed row of the oriented generator 3. -/
def generatedNinthLowerSpinTensorMonomialSign03 : Fin 24 → ℤ :=
  ![1, 1, 1, -1, 1, 1, -1, 1, -1, 1, 1, 1,
    -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1]

private theorem complete_entries_03 : ∀ j k : Fin 24,
    generatedNinthLowerSpinTensorSpatialNumerator 3 j k =
      generatedNinthLowerSpinTensorMonomialSign03 j *
        if generatedNinthLowerSpinTensorMonomialPermutation03 j = k then 1 else 0 := by
  decide +kernel

/-- Original generator 3 spatial replay is the exact full signed single pullback. -/
theorem generatedNinth_lower_spin_tensor_spatial_monomial_03 (n : Fin 4096) (j : Fin 24) :
    generatedNinthLowerSpinTensorSpatialInteger 3 n j =
      generatedNinthLowerSpinTensorMonomialSign03 j *
        generatedNinthLowerSpinTensorInputInteger n
          (generatedNinthLowerSpinTensorMonomialPermutation03 j) := by
  unfold generatedNinthLowerSpinTensorSpatialInteger
  exact integer_monomial _ _ _ complete_entries_03 _ j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
