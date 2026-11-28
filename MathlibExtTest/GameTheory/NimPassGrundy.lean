/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.NimPassGrundy
import MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtFoldlXor

namespace MathlibExtTest.GameTheory.NimPassGrundy

open MetaMathlibExt

local notation "onePile" m:max a:max p:max =>
  heightChocolateBarGrundy (nimPassIndicator (fun _ : Fin 1 ↦ m)) (fun _ ↦ a) p

private theorem onePile_mex (m a p : ℕ) :
    onePile m a p = sInf {c | (∀ u < a, onePile m u (min (if m ≤ u then 1 else 0) p) ≠ c) ∧
      ∀ v < p, onePile m a v ≠ c} := by
  have hupdate (i : Fin 1) (u : ℕ) : Function.update (fun _ : Fin 1 ↦ a) i u = fun _ ↦ u := by
    funext j
    rw [Subsingleton.elim j i, Function.update_self]
  have hbit (u : ℕ) : nimPassIndicator (fun _ : Fin 1 ↦ m) (fun _ ↦ u) =
      if m ≤ u then 1 else 0 := by
    split_ifs with h
    · exact nimPassIndicator_eq_one_iff.mpr ⟨0, h⟩
    · exact nimPassIndicator_eq_zero_iff.mpr (fun _ ↦ Nat.lt_of_not_ge h)
  rw [heightChocolateBarGrundy_eq]
  simp only [hupdate, hbit, Fin.forall_fin_one]

private theorem noPass_zero (m : ℕ) : onePile m 0 0 = 0 := by
  rw [onePile_mex]
  exact Nat.sInf_eq_zero.mpr (Or.inl (by simp))

private theorem noPass_one (m : ℕ) : onePile m 1 0 = 1 := by
  rw [onePile_mex]
  simp [Nat.lt_one_iff, noPass_zero]
  refine le_antisymm (Nat.sInf_le (show 0 ≠ 1 by decide)) (le_csInf ⟨1, by decide⟩ ?_)
  intro n hn
  change 0 ≠ n at hn
  omega

private theorem noPass_two (m : ℕ) : onePile m 2 0 = 2 := by
  rw [onePile_mex]
  simp [show (2 : ℕ) = 1 + 1 by decide, Nat.forall_lt_succ_right, Nat.lt_one_iff,
    noPass_zero, noPass_one]
  refine le_antisymm (Nat.sInf_le (show 0 ≠ 2 ∧ 1 ≠ 2 by decide)) (le_csInf ⟨2, by decide⟩ ?_)
  intro n hn
  change 0 ≠ n ∧ 1 ≠ n at hn
  omega

-- Both pile cuts lose the pass and the pass move keeps the pile. Their values are 0, 1, and 2.
private theorem evenThreshold_two : onePile 2 2 1 = 3 := by
  rw [onePile_mex]
  simp [show (2 : ℕ) = 1 + 1 by decide, Nat.forall_lt_succ_right, Nat.lt_one_iff,
    noPass_zero, noPass_one, noPass_two]
  refine le_antisymm (Nat.sInf_le (show (0 ≠ 3 ∧ 1 ≠ 3) ∧ 2 ≠ 3 by decide))
    (le_csInf ⟨3, by decide⟩ ?_)
  intro n hn
  change (0 ≠ n ∧ 1 ≠ n) ∧ 2 ≠ n at hn
  omega

example : onePile 2 2 1 = 3 ∧ 3 = (2 : ℕ) ^^^ 1 := ⟨evenThreshold_two, by decide⟩

-- Cutting from three to two keeps the pass. The other pile cuts lose it.
example : onePile 2 3 1 = 2 ∧ 2 = (3 : ℕ) ^^^ 1 := by
  have hthree : onePile 2 3 0 = 3 := by
    rw [onePile_mex]
    simp [show (3 : ℕ) = 2 + 1 by decide, show (2 : ℕ) = 1 + 1 by decide,
      Nat.forall_lt_succ_right, Nat.lt_one_iff, noPass_zero, noPass_one, noPass_two]
    refine le_antisymm (Nat.sInf_le (show (0 ≠ 3 ∧ 1 ≠ 3) ∧ 2 ≠ 3 by decide))
      (le_csInf ⟨3, by decide⟩ ?_)
    intro n hn
    change (0 ≠ n ∧ 1 ≠ n) ∧ 2 ≠ n at hn
    omega
  refine ⟨?_, by decide⟩
  rw [onePile_mex]
  simp [show (3 : ℕ) = 2 + 1 by decide, show (2 : ℕ) = 1 + 1 by decide,
    Nat.forall_lt_succ_right, Nat.lt_one_iff, noPass_zero, noPass_one, evenThreshold_two, hthree]
  refine le_antisymm (Nat.sInf_le (show (0 ≠ 2 ∧ 1 ≠ 2) ∧ 3 ≠ 2 by decide))
    (le_csInf ⟨2, by decide⟩ ?_)
  intro n hn
  change (0 ≠ n ∧ 1 ≠ n) ∧ 3 ≠ n at hn
  omega

-- At the odd threshold, the pile cut loses the pass and the mex is not the nim-sum.
example : onePile 1 1 1 = 2 ∧ 2 ≠ (1 : ℕ) ^^^ 1 := by
  refine ⟨?_, by decide⟩
  rw [onePile_mex]
  simp [Nat.lt_one_iff, noPass_zero, noPass_one]
  refine le_antisymm (Nat.sInf_le (show 0 ≠ 2 ∧ 1 ≠ 2 by decide)) (le_csInf ⟨2, by decide⟩ ?_)
  intro n hn
  change 0 ≠ n ∧ 1 ≠ n at hn
  omega

-- Compute the two-coordinate mask identity without the promoted lemma.
example :
    (List.ofFn (Function.update (fun _ : Fin 2 ↦ 3) 0 (3 ^^^ 1))).foldl (· ^^^ ·) 0 =
      (List.ofFn (fun _ : Fin 2 ↦ 3)).foldl (· ^^^ ·) 0 ^^^ 1 := by decide

-- A client can obtain the even-threshold value directly from the public characterization.
example : onePile 2 2 1 = 3 := by
  have hlegal : 1 ≤ nimPassIndicator (fun _ : Fin 1 ↦ 2) (fun _ ↦ 2) :=
    (nimPassIndicator_eq_one_iff.mpr ⟨0, le_rfl⟩).ge
  have hvalue := (nimPassGrundy_eq_xor_iff (m := fun _ : Fin 1 ↦ 2) (fun _ ↦ by decide)).mpr
    (fun _ ↦ ⟨1, rfl⟩) (fun _ ↦ 2) 1 hlegal
  exact hvalue.trans (by decide)

end MathlibExtTest.GameTheory.NimPassGrundy
