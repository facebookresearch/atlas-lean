/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPermutationGenerationDefinitions

/-! Genuine four-generator words representing each step of the faithful seven-point base. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Evaluation of a word in the four frozen actual permutations. -/
def generatedFourthPermutationWord (w : List (Fin 4)) : golayAutomorphismSubgroup :=
  (w.map generatedFourthMonomialPermutation).prod

/-- Recursive coordinate evaluation of the same four actual permutation words. -/
def generatedFourthPermutationWordArray : List (Fin 4) → Fin 24 → Fin 24
  | [], i => i
  | t :: w, i => generatedFourthMonomialImages t (generatedFourthPermutationWordArray w i)

/-- The recursive array is exactly the genuine group-word action. -/
theorem generatedFourth_permutation_word_apply (w : List (Fin 4)) (i : Fin 24) :
    (generatedFourthPermutationWord w).val i = generatedFourthPermutationWordArray w i := by
  induction w generalizing i with
  | nil => rfl
  | cons t w ih =>
    change (generatedFourthMonomialPermutation t).val
      ((generatedFourthPermutationWord w).val i) = _
    rw [generatedFourth_monomial_images, ih]
    rfl

/-- Every genuine four-generator word lies in the actual four-generated subgroup. -/
theorem generatedFourth_permutation_word_mem (w : List (Fin 4)) :
    generatedFourthPermutationWord w ∈ generatedFourthPermutationFourSubgroup := by
  apply generatedFourthPermutationFourSubgroup.list_prod_mem
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure ⟨t, rfl⟩

/-- Prefix levels of the 45 orbit representatives. -/
def generatedFourthPermutationRepLevels : Fin 45 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      2, 2, 2, 2, 2, 2, 3, 4, 4, 4, 4, 5, 5, 6]

/-- Original four-generator words for all 45 representatives. -/
def generatedFourthPermutationRepWords : Fin 45 → List (Fin 4) :=
  ![[],
    [3],
    [3, 1],
    [1],
    [2, 3],
    [1, 0, 3],
    [0, 3],
    [3, 1, 0, 3],
    [1, 2, 3, 1],
    [1, 3, 0],
    [1, 0, 1, 0],
    [1, 0],
    [3, 0],
    [0],
    [2, 3, 1],
    [0, 1, 0],
    [],
    [3, 1, 3],
    [0, 1, 3, 2, 1, 2],
    [2],
    [1, 0, 1],
    [1, 2, 1, 0],
    [3, 1, 3, 2],
    [1, 0, 2, 1, 0],
    [1, 2, 3, 2, 1],
    [3, 2, 0, 2, 1, 3],
    [3, 2, 1, 2, 3],
    [0, 2, 0],
    [0, 3, 0, 3, 0, 2],
    [2, 3, 1, 3],
    [0, 1, 3, 2, 0, 1],
    [],
    [0, 3, 0, 3, 0],
    [2, 0, 1, 2, 1],
    [1, 2, 1, 0, 2],
    [3, 0, 3, 2, 3, 2],
    [2, 3, 0, 2, 3, 0],
    [],
    [],
    [1, 2, 3, 2, 0, 2, 3, 2, 1],
    [2, 3, 2, 0, 2, 3, 2],
    [3, 2, 3, 0, 3, 2],
    [],
    [1, 0, 3, 1, 0, 1, 3, 0],
    []]

/-- Literal physical-coordinate arrays of the 45 actual word products. -/
def generatedFourthPermutationRepImages : Fin 45 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![1, 0, 3, 2, 4, 5, 6, 7, 11, 10, 9, 8, 14, 15, 12, 13, 16, 17, 18, 19, 21, 20, 23, 22],
    ![2, 0, 3, 1, 4, 6, 5, 7, 8, 10, 9, 11, 14, 12, 15, 13, 23, 21, 22, 20, 17, 19, 16, 18],
    ![3, 1, 2, 0, 4, 6, 5, 7, 11, 9, 10, 8, 12, 14, 13, 15, 22, 20, 23, 21, 17, 19, 16, 18],
    ![12, 0, 19, 22, 4, 9, 7, 6, 11, 10, 5, 8, 20, 16, 1, 13, 15, 17, 23, 3, 21, 14, 18, 2],
    ![13, 19, 0, 20, 5, 6, 4, 10, 8, 7, 9, 11, 1, 22, 12, 16, 15, 2, 23, 18, 3, 17, 21, 14],
    ![14, 21, 3, 17, 6, 5, 4, 10, 11, 7, 9, 8, 1, 16, 12, 22, 15, 2, 18, 23, 0, 20, 19, 13],
    ![15, 19, 1, 21, 5, 6, 4, 9, 11, 7, 10, 8, 0, 23, 14, 16, 13, 3, 22, 18, 2, 17, 20, 12],
    ![16, 3, 21, 12, 4, 7, 9, 5, 11, 10, 6, 8, 17, 1, 22, 14, 23, 19, 2, 13, 20, 0, 15, 18],
    ![17, 12, 20, 2, 5, 6, 4, 9, 8, 10, 7, 11, 13, 18, 3, 22, 14, 0, 23, 16, 19, 1, 15, 21],
    ![18, 16, 17, 19, 6, 4, 5, 7, 8, 9, 10, 11, 12, 15, 13, 14, 22, 20, 21, 23, 2, 0, 1, 3],
    ![19, 13, 20, 0, 5, 6, 4, 10, 11, 9, 7, 8, 12, 16, 1, 22, 15, 2, 23, 18, 17, 3, 14, 21],
    ![20, 12, 17, 2, 6, 5, 4, 9, 11, 10, 7, 8, 14, 23, 0, 16, 13, 3, 18, 22, 21, 1, 15, 19],
    ![21, 14, 17, 3, 6, 5, 4, 10, 8, 9, 7, 11, 12, 22, 1, 16, 15, 2, 18, 23, 20, 0, 13, 19],
    ![22, 0, 19, 12, 4, 7, 9, 6, 8, 10, 5, 11, 20, 1, 16, 13, 18, 21, 2, 14, 17, 3, 15, 23],
    ![23, 22, 20, 21, 5, 4, 6, 7, 11, 9, 10, 8, 12, 15, 14, 13, 16, 17, 19, 18, 2, 3, 1, 0],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 2, 1, 3, 4, 6, 5, 7, 11, 9, 10, 8, 15, 13, 14, 12, 23, 21, 22, 20, 19, 17, 18, 16],
    ![0, 3, 1, 2, 6, 4, 5, 7, 11, 10, 9, 8, 22, 23, 20, 21, 13, 12, 15, 14, 16, 17, 18, 19],
    ![0, 12, 22, 19, 4, 9, 7, 6, 8, 5, 10, 11, 1, 13, 20, 16, 15, 17, 23, 3, 14, 21, 2, 18],
    ![0, 13, 20, 19, 5, 4, 6, 10, 8, 9, 7, 11, 12, 1, 16, 22, 14, 17, 21, 3, 2, 18, 15, 23],
    ![0, 14, 13, 3, 9, 7, 4, 10, 8, 6, 5, 11, 1, 15, 12, 2, 22, 16, 23, 18, 20, 21, 17, 19],
    ![0, 15, 18, 20, 4, 9, 7, 5, 11, 6, 10, 8, 2, 13, 19, 23, 12, 21, 16, 3, 14, 17, 1, 22],
    ![0, 16, 1, 19, 9, 10, 5, 7, 8, 6, 4, 11, 13, 22, 12, 20, 15, 14, 23, 21, 2, 18, 17, 3],
    ![0, 17, 23, 12, 4, 5, 10, 7, 11, 9, 6, 8, 3, 19, 22, 15, 21, 1, 18, 13, 20, 16, 14, 2],
    ![0, 18, 20, 15, 7, 9, 5, 4, 11, 6, 10, 8, 3, 16, 21, 12, 17, 14, 22, 1, 19, 23, 2, 13],
    ![0, 19, 20, 13, 4, 5, 6, 10, 11, 9, 7, 8, 17, 3, 14, 21, 16, 12, 22, 1, 2, 15, 18, 23],
    ![0, 20, 2, 23, 10, 9, 6, 7, 8, 5, 4, 11, 14, 17, 12, 16, 15, 13, 19, 18, 1, 21, 22, 3],
    ![0, 21, 15, 16, 6, 10, 7, 4, 8, 5, 9, 11, 1, 23, 14, 19, 22, 17, 13, 2, 20, 12, 3, 18],
    ![0, 22, 12, 19, 4, 7, 9, 6, 11, 5, 10, 8, 16, 13, 20, 1, 18, 21, 2, 14, 3, 17, 23, 15],
    ![0, 23, 20, 2, 10, 6, 7, 9, 11, 4, 5, 8, 3, 22, 21, 1, 16, 12, 17, 14, 18, 19, 13, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 3, 2, 6, 5, 4, 7, 8, 10, 9, 11, 21, 23, 20, 22, 19, 17, 18, 16, 14, 12, 15, 13],
    ![0, 1, 16, 19, 7, 10, 5, 9, 8, 4, 6, 11, 20, 22, 12, 13, 17, 2, 3, 18, 14, 21, 15, 23],
    ![0, 1, 17, 18, 9, 6, 10, 4, 8, 7, 5, 11, 14, 15, 20, 22, 2, 16, 19, 3, 12, 21, 13, 23],
    ![0, 1, 18, 17, 6, 10, 4, 9, 11, 7, 5, 8, 12, 13, 21, 23, 16, 3, 2, 19, 20, 14, 22, 15],
    ![0, 1, 19, 16, 5, 10, 7, 9, 8, 6, 4, 11, 21, 23, 14, 15, 18, 2, 3, 17, 12, 20, 13, 22],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 5, 4, 7, 6, 8, 9, 10, 11, 13, 12, 15, 14, 18, 19, 16, 17, 23, 22, 21, 20],
    ![0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 14, 15, 12, 13, 19, 18, 17, 16, 21, 20, 23, 22],
    ![0, 1, 2, 3, 7, 6, 5, 4, 11, 10, 9, 8, 12, 13, 14, 15, 18, 19, 16, 17, 21, 20, 23, 22],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]

set_option maxRecDepth 10000 in
-- These 45 bounded word arrays bind every representative to the original generators.
theorem generatedFourth_permutation_rep_words : ∀ r : Fin 45, ∀ i : Fin 24,
    generatedFourthPermutationWordArray (generatedFourthPermutationRepWords r) i =
      generatedFourthPermutationRepImages r i := by
  decide +kernel

/-- Actual group representatives, each a word in the original four permutations. -/
def generatedFourthPermutationRep (r : Fin 45) : golayAutomorphismSubgroup :=
  generatedFourthPermutationWord (generatedFourthPermutationRepWords r)

/-- The literal representative arrays equal their actual group action. -/
theorem generatedFourth_permutation_rep_apply (r : Fin 45) (i : Fin 24) :
    (generatedFourthPermutationRep r).val i = generatedFourthPermutationRepImages r i := by
  rw [generatedFourthPermutationRep, generatedFourth_permutation_word_apply,
    generatedFourth_permutation_rep_words]

/-- Each representative belongs to the actual four-generated subgroup. -/
theorem generatedFourth_permutation_rep_mem (r : Fin 45) :
    generatedFourthPermutationRep r ∈ generatedFourthPermutationFourSubgroup :=
  generatedFourth_permutation_word_mem _

/-- Each actual representative fixes the prefix at its specified level. -/
theorem generatedFourth_permutation_rep_prefix : ∀ r : Fin 45, ∀ j : Fin 7,
    j.val < generatedFourthPermutationRepLevels r →
      (generatedFourthPermutationRep r).val (golayBasePoints j) = golayBasePoints j := by
  intro r j hj
  rw [generatedFourth_permutation_rep_apply]
  have h : ∀ r : Fin 45, ∀ j : Fin 7,
      j.val < generatedFourthPermutationRepLevels r →
        generatedFourthPermutationRepImages r (golayBasePoints j) = golayBasePoints j := by
    decide +kernel
  exact h r j hj

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
