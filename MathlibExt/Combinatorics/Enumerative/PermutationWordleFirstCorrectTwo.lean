/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PermutationWordleDerangements
public import MathlibExt.Combinatorics.Enumerative.PermutationWordleFirstCorrectThree
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Three-guess permutation Wordle solves first correct at guess two

A three-guess solve of a derangement either has a correct position on the second guess or
first has one on the third guess. For cyclic shift, the second class is a singleton.

## References

* Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
  (2026), Article 26.1.7, pp. 1–16, Section 4.2, Lemma 9 and Theorems 11–12.
-/

namespace MetaMathlibExt

/-- **Three-guess solves of cyclic shift first correct at guess two.** For $n \ge 4$, the number
of permutations $\pi$ of $\{0, \dots, n-1\}$ that the cyclic shift strategy guesses in exactly
three guesses, with the second guess being the first guess that has a correct position, is
$2^n - 2n - 2$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 12 (`jis-2026-26.1.7-thm-12`). -/
public theorem card_solvedIn_three_firstCorrectAt_two_cyclicShift (n : ℕ) (hn : 4 ≤ n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn cyclicShiftStrategy π 3 ∧
        PermWordleFirstCorrectAt cyclicShiftStrategy π 2} = 2 ^ n - 2 * n - 2 := by
  classical
  let D := {π : Equiv.Perm (Fin n) //
    (∀ i, π i ≠ i) ∧ PermWordleSolvedIn cyclicShiftStrategy π 3}
  let C (r : ℕ) := {π : Equiv.Perm (Fin n) //
    PermWordleSolvedIn cyclicShiftStrategy π 3 ∧ PermWordleFirstCorrectAt cyclicShiftStrategy π r}
  let P (π : D) := ∃ i, permWordleGuess cyclicShiftStrategy π.val 1 i = π.val i
  let e₂ : {π : D // P π} ≃ C 2 := {
    toFun := fun ⟨⟨π, hπ, hsolve⟩, hmatch⟩ => ⟨π, hsolve, by
      refine ⟨by decide, hmatch, fun j hj i => ?_⟩
      have : j = 0 := by omega
      subst j
      exact (hπ i).symm⟩
    invFun := fun ⟨π, hsolve, hfirst⟩ =>
      ⟨⟨π, fun i => (hfirst.2.2 0 (by decide) i).symm, hsolve⟩, hfirst.2.1⟩
    left_inv := by rintro ⟨⟨π, hπ, hsolve⟩, hmatch⟩; rfl
    right_inv := by rintro ⟨π, hsolve, hfirst⟩; rfl }
  let e₃ : {π : D // ¬ P π} ≃ C 3 := {
    toFun := fun ⟨⟨π, hπ, hsolve⟩, hmiss⟩ => ⟨π, hsolve, by
      let i₀ : Fin n := ⟨0, by omega⟩
      refine ⟨by decide, ⟨i₀, congrFun hsolve.2.1 i₀⟩, fun j hj i => ?_⟩
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl
      · exact (hπ i).symm
      · exact fun hi => hmiss ⟨i, hi⟩⟩
    invFun := fun ⟨π, hsolve, hfirst⟩ =>
      ⟨⟨π, fun i => (hfirst.2.2 0 (by decide) i).symm, hsolve⟩,
        fun ⟨i, hi⟩ => hfirst.2.2 1 (by decide) i hi⟩
    left_inv := by rintro ⟨⟨π, hπ, hsolve⟩, hmatch⟩; rfl
    right_inv := by rintro ⟨π, hsolve, hfirst⟩; rfl }
  have hpartition : Nat.card D = Nat.card (C 2) + Nat.card (C 3) := by
    rw [← Nat.card_sum]
    exact Nat.card_congr ((Equiv.sumCompl P).symm.trans (Equiv.sumCongr e₂ e₃))
  have hD : Nat.card D = 2 ^ n - (2 * n + 1) :=
    card_derangements_solvedIn_three_cyclicShift n (by omega)
  have h₃ : Nat.card (C 3) = 1 :=
    card_solvedIn_three_firstCorrectAt_three n hn cyclicShiftStrategy
      (isCycle_finRotate_of_le (by omega)) (support_finRotate_of_le (by omega))
  change Nat.card (C 2) = _
  omega

end MetaMathlibExt
