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

-- At order one the two lucky-set bounds coincide.
example : (stirlingLuckySet (n := 1) ![1, 1]).card = 1 := by
  have h := stirlingLuckySet_basic 1 (by decide) ![1, 1] (by unfold IsStirlingPermutation; decide)
  exact le_antisymm h.2.2.2 h.2.2.1

-- In 2211, car 3 is the first to prefer spot 1.
example : 1 ∈ stirlingLuckySet (n := 2) ![2, 2, 1, 1] ∧
    3 ∈ stirlingLuckySet (n := 2) ![2, 2, 1, 1] := by
  have h := stirlingLuckySet_basic 2 (by decide) ![2, 2, 1, 1]
    (by unfold IsStirlingPermutation; decide)
  exact ⟨h.1, h.2.1 2 (by decide) (by decide)⟩

-- Both lucky-set bounds are attained at order two.
example : (stirlingLuckySet (n := 2) ![1, 1, 2, 2]).card = 1 ∧
    (stirlingLuckySet (n := 2) ![2, 2, 1, 1]).card = 2 := by decide

-- An extremely lucky word with a nested pair and nonconsecutive lucky positions.
example (v : Fin (2 * 3) → ℕ) (hv : IsStirlingPermutation 3 v)
    (hd : ∀ i, stirlingDisplacement v i = (![0, 0, 1, 0, 3, 5] : Fin (2 * 3) → ℕ) i) :
    v = ![1, 3, 3, 2, 2, 1] := by
  have hvec : (fun i => stirlingDisplacement (n := 3) ![1, 3, 3, 2, 2, 1] i) =
      ![0, 0, 1, 0, 3, 5] := by decide
  exact extremely_lucky_eq_of_displacement_eq (n := 3) (w := ![1, 3, 3, 2, 2, 1]) (w' := v)
    (hw := by unfold IsStirlingPermutation; decide) (hw' := hv) (hl := by decide)
    (hd := fun i => (hd i).trans (congrFun hvec i).symm)

-- Distinct presentations of the empty word satisfy all the hypotheses.
example : (fun _ : Fin (2 * 0) => 7) = (Fin.elim0 : Fin (2 * 0) → ℕ) :=
  extremely_lucky_eq_of_displacement_eq 0 Fin.elim0 (fun _ => 7)
    (by simp [IsStirlingPermutation]) (by simp [IsStirlingPermutation]) (by decide)
    (fun i => Fin.elim0 i)

-- The paper's collision: dropping maximal luck would destroy uniqueness.
example :
    let u : Fin (2 * 3) → ℕ := ![1, 1, 3, 3, 2, 2]
    let v : Fin (2 * 3) → ℕ := ![3, 3, 1, 1, 2, 2]
    IsStirlingPermutation 3 u ∧ IsStirlingPermutation 3 v ∧ u ≠ v ∧
      (stirlingLuckySet u).card < 3 ∧ (stirlingLuckySet v).card < 3 ∧
      ∀ i, stirlingDisplacement v i = stirlingDisplacement u i := by
  dsimp only
  refine ⟨by unfold IsStirlingPermutation; decide, by unfold IsStirlingPermutation; decide,
    ?_, by decide, by decide, by decide⟩
  intro h
  have hzero := congrFun h (0 : Fin (2 * 3))
  change (1 : ℕ) = 3 at hzero
  omega
