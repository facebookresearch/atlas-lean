/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineParameterCard
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineSum
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The sixteen ordinary spatial columns containing one affine state each. -/
def generatedFourthQAffineTensorSingleColumns : Fin 16 → Fin 24 :=
  ![0, 1, 2, 3, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

/-- The original packed-state indices of those sixteen singleton columns. -/
def generatedFourthQAffineTensorSingleIndices : Fin 16 → Fin 28 :=
  ![0, 1, 2, 3, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The six disjoint affine states occurring together in spatial column eight. -/
def generatedFourthQAffineTensorSixIndices (i : Fin 6) : Fin 28 := ⟨i.val + 4, by omega⟩

/-- Each ordinary column selects exactly its single displayed packed index. -/
theorem generatedFourthQAffineTensor_single_selector : ∀ j : Fin 16, ∀ k : Fin 28,
    generatedFourthQAffineTensorColumns k = generatedFourthQAffineTensorSingleColumns j ↔
      k = generatedFourthQAffineTensorSingleIndices j := by
  decide +kernel

/-- The six joint-column basepoints lie on pairwise disjoint cosets of the actual common plane. -/
theorem generatedFourthQAffineTensor_six_disjoint (i j : Fin 6) (hij : i ≠ j) :
    generatedAxisFourthQAffineParameterBases
        (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices i)) +
      generatedAxisFourthQAffineParameterBases
        (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices j)) ∉
      generatedAxisFourthQAffineParameterPlane := by
  rw [generatedAxisFourthQAffineParameter_plane_mem_four_iff]
  have h : ∀ i j : Fin 6, i ≠ j →
      ¬(generatedAxisFourthQAffineParameterBases
          (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices i)) +
        generatedAxisFourthQAffineParameterBases
          (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices j)) = 0 ∨
        generatedAxisFourthQAffineParameterBases
          (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices i)) +
        generatedAxisFourthQAffineParameterBases
          (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices j)) =
            golayLabelCoefficients 14 ∨
        generatedAxisFourthQAffineParameterBases
          (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices i)) +
        generatedAxisFourthQAffineParameterBases
          (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices j)) =
            golayLabelCoefficients 2048 ∨
        generatedAxisFourthQAffineParameterBases
          (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices i)) +
        generatedAxisFourthQAffineParameterBases
          (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices j)) =
            golayLabelCoefficients 14 + golayLabelCoefficients 2048) := by decide +kernel
  exact h i j hij

/-- Selecting spatial column eight selects exactly the six displayed packed terms. -/
theorem generatedFourthQAffineTensor_six_sum (f : Fin 28 → ℝ) :
    (∑ k : Fin 28, if (8 : Fin 24) = generatedFourthQAffineTensorColumns k then f k else 0) =
      ∑ i : Fin 6, f (generatedFourthQAffineTensorSixIndices i) := by
  simp [Fin.sum_univ_succ, generatedFourthQAffineTensorColumns,
    generatedFourthQAffineTensorSixIndices]

/-- Ordinary-column selection gives the literal singleton term. -/
theorem generatedFourthQAffineTensor_single_sum (f : Fin 28 → ℝ) (j : Fin 16) :
    (∑ k : Fin 28,
      if generatedFourthQAffineTensorSingleColumns j = generatedFourthQAffineTensorColumns k
      then f k else 0) = f (generatedFourthQAffineTensorSingleIndices j) := by
  classical
  have he (k : Fin 28) : generatedFourthQAffineTensorSingleColumns j =
      generatedFourthQAffineTensorColumns k ↔ k = generatedFourthQAffineTensorSingleIndices j :=
    eq_comm.trans (generatedFourthQAffineTensor_single_selector j k)
  simp only [he]
  simp

/-- Singleton and six-column terms together contain every one of the twenty-two family labels. -/
theorem generatedFourthQAffineTensor_family_coverage : ∀ j : Fin 22,
    (∃ i : Fin 16, generatedFourthQAffineTensorFamilyIndex
      (generatedFourthQAffineTensorSingleIndices i) = j) ∨
    (∃ i : Fin 6, generatedFourthQAffineTensorFamilyIndex
      (generatedFourthQAffineTensorSixIndices i) = j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
