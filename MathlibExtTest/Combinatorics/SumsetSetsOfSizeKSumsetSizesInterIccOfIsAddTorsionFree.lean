/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SumsetSetsOfSizeKSumsetSizesInterIccOfIsAddTorsionFree

open scoped Pointwise

namespace MathlibExtTest.Combinatorics.SumsetSetsOfSizeKSumsetSizesInterIccOfIsAddTorsionFree

example :
    {n : ℕ | ∃ A : Finset ℤ, A.card = 4 ∧ (1 • A).card = n} ∩ Set.Icc 4 4 = {4} := by
  simpa using MetaMathlibExt.sumsetSizes_inter_Icc_of_isAddTorsionFree
    (G := ℤ) 1 4 (by decide) (by decide)

example :
    {n : ℕ | ∃ A : Finset ℤ, A.card = 4 ∧ (3 • A).card = n} ∩ Set.Icc 10 12 = {10, 12} := by
  simpa using MetaMathlibExt.sumsetSizes_inter_Icc_of_isAddTorsionFree
    (G := ℤ) 3 4 (by decide) (by decide)

example (A : Finset ℤ) (hA : A.card = 4) : (3 • A).card ≠ 11 := by
  intro hn
  have hmem : 11 ∈
      {n : ℕ | ∃ B : Finset ℤ, B.card = 4 ∧ (3 • B).card = n} ∩ Set.Icc 10 12 :=
    ⟨⟨A, hA, hn⟩, by decide, by decide⟩
  have he := MetaMathlibExt.sumsetSizes_inter_Icc_of_isAddTorsionFree
    (G := ℤ) 3 4 (by decide) (by decide)
  have he' :
      {n : ℕ | ∃ B : Finset ℤ, B.card = 4 ∧ (3 • B).card = n} ∩ Set.Icc 10 12 =
        {10, 12} := by simpa using he
  rw [he'] at hmem
  exact (by decide : (11 : ℕ) ∉ ({10, 12} : Set ℕ)) hmem

example : ∃ A : Finset (ℤ × ℤ), A.card = 4 ∧ (3 • A).card = 12 := by
  have he := MetaMathlibExt.sumsetSizes_inter_Icc_of_isAddTorsionFree
    (G := ℤ × ℤ) 3 4 (by decide) (by decide)
  have hmem : 12 ∈
      {n : ℕ | ∃ A : Finset (ℤ × ℤ), A.card = 4 ∧ (3 • A).card = n} ∩ Set.Icc 10 12 := by
    rw [show (10 : ℕ) = 3 * 4 - 3 + 1 by decide, show (12 : ℕ) = 3 * 4 by decide, he]
    simp
  exact hmem.1

#check @MetaMathlibExt.sumsetSizes_inter_Icc_of_isAddTorsionFree
#print axioms MetaMathlibExt.sumsetSizes_inter_Icc_of_isAddTorsionFree

end MathlibExtTest.Combinatorics.SumsetSetsOfSizeKSumsetSizesInterIccOfIsAddTorsionFree
