/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingLuckyDisplacement

open MetaMathlibExt

-- The empty word shows why the positive-order hypothesis is necessary.
example : IsAdmissibleLuckySet 0 ∅ :=
  ⟨Fin.elim0, by simp [IsStirlingPermutation], by decide⟩

example : 1 ∈ ({1} : Finset ℕ) ∧ 2 ∉ ({1} : Finset ℕ) := by
  apply IsAdmissibleLuckySet.one_mem_and_two_mul_not_mem 1 (by decide)
  exact ⟨![1, 1], by unfold IsStirlingPermutation; decide, by decide⟩

-- In 221133, car 2 takes spot 3 before either car preferring 3 arrives.
example : stirlingLuckySet (n := 3) ![2, 2, 1, 1, 3, 3] = {1, 3} := by decide

-- The first position has an empty prefix.
example : Odd 1 :=
  stirling_odd_of_lt_all_before 1 ![1, 1] (by unfold IsStirlingPermutation; decide) 0 (by decide)

-- In 233211 the new minimum at position five follows two nested pairs.
example : Odd 5 :=
  stirling_odd_of_lt_all_before 3 ![2, 3, 3, 2, 1, 1] (by unfold IsStirlingPermutation; decide)
    4 (by decide)

-- The formula includes the empty parking lot.
example : stirlingTotalDisplacement (n := 0) Fin.elim0 = 0 :=
  stirlingTotalDisplacement_eq 0 Fin.elim0 (by simp [IsStirlingPermutation])

-- In 332211 the first car takes spot 3 and the last car travels from spot 1 to spot 6.
example : stirlingTotalDisplacement (n := 3) ![3, 3, 2, 2, 1, 1] = 9 := by decide

-- Swapping the middle cars of 1122 gives 1212, which is not a Stirling permutation.
example :
    let w : Fin (2 * 2) → ℕ := ![1, 1, 2, 2]
    let σ : Equiv.Perm (Fin (2 * 2)) := Equiv.swap 1 2
    ¬ IsStirlingPermutation 2 (w ∘ σ) ∧
      stirlingTotalDisplacement (w ∘ σ) = stirlingTotalDisplacement w := by
  dsimp only
  exact ⟨by unfold IsStirlingPermutation; decide,
    stirlingTotalDisplacement_comp_perm 2 _ (by unfold IsStirlingPermutation; decide) _⟩

-- There is also a rearrangement of the empty parking lot.
example :
    stirlingTotalDisplacement (n := 0) (Fin.elim0 ∘ Equiv.refl _) =
      stirlingTotalDisplacement (n := 0) Fin.elim0 :=
  stirlingTotalDisplacement_comp_perm 0 Fin.elim0 (by simp [IsStirlingPermutation]) _

-- At order one the two bounds coincide.
example : (Finset.univ.filter fun i => stirlingDisplacement (n := 1) ![1, 1] i = 0).card = 1 := by
  have h := stirling_card_zero_displacement 1 (by decide) ![1, 1]
    (by unfold IsStirlingPermutation; decide)
  exact le_antisymm h.2 h.1

-- At order two the two bounds are distinct and both are attained.
example :
    (Finset.univ.filter fun i => stirlingDisplacement (n := 2) ![1, 1, 2, 2] i = 0).card = 1 ∧
      (Finset.univ.filter fun i => stirlingDisplacement (n := 2) ![1, 2, 2, 1] i = 0).card = 2 :=
  by decide
