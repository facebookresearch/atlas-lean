/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Hash counting over F2

Summing over all linear hashes `x ↦ a ⬝ᵥ x` the number of annihilated
elements of a finite set: each nonzero element is counted
half the time and the zero element always. The Stockmeyer
oracle protocol is not included here.
-/

@[expose] public section

namespace MathlibExt.Complexity.HashCounting

/-- For a nonzero `x`, exactly half of all `a` satisfy `a ⬝ᵥ x = 0`, stated in doubled form:
adding `Pi.single i 1` to `a`, where `x i = 1`, flips `a ⬝ᵥ x`. -/
private lemma two_mul_card_dotProduct_eq_zero {n : ℕ} (x : Fin n → ZMod 2) (hx : x ≠ 0) :
    2 * (Finset.univ.filter (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card = 2 ^ n := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hxi : x i = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hi
  have hswap : (Finset.univ.filter (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card =
      (Finset.univ.filter (fun a : Fin n → ZMod 2 => ¬a ⬝ᵥ x = 0)).card := by
    refine Finset.card_equiv (Equiv.addRight (Pi.single i 1)) fun a ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight,
      add_dotProduct, single_one_dotProduct, hxi]
    generalize a ⬝ᵥ x = c
    revert c
    decide
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → ZMod 2))) (fun a ↦ a ⬝ᵥ x = 0)
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hsum
  omega

private lemma card_zero_annihilator {n : ℕ} :
    (Finset.univ.filter (fun a : Fin n → ZMod 2 => a ⬝ᵥ 0 = 0)).card = 2 ^ n := by
  rw [Finset.filter_true_of_mem (fun a _ => dotProduct_zero a), Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- Hash-count identity: summing, over all linear hashes
`x ↦ a ⬝ᵥ x`, the number of set elements annihilated by `a`, counts
each nonzero element `2^(n-1)` times (in doubled form) and
the zero element, if present, `2^n` times (doubled:
`2^(n+1)`). -/
theorem hash_count_identity {n : ℕ} (S : Finset (Fin n → ZMod 2)) :
    2 * (∑ a : Fin n → ZMod 2,
        (S.filter (fun x => a ⬝ᵥ x = 0)).card)
      = (S.card - (if (0 : Fin n → ZMod 2) ∈ S then 1 else 0)) * 2 ^ n
        + (if (0 : Fin n → ZMod 2) ∈ S then 2 ^ (n + 1) else 0) := by
  classical
  have hswap : (∑ a : Fin n → ZMod 2, (S.filter (fun x => a ⬝ᵥ x = 0)).card)
      = ∑ x ∈ S, (Finset.univ.filter (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  by_cases h0 : (0 : Fin n → ZMod 2) ∈ S
  · have hsum_split : (∑ x ∈ S, (Finset.univ.filter
        (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card)
        = (Finset.univ.filter (fun a : Fin n → ZMod 2 => a ⬝ᵥ 0 = 0)).card
          + ∑ x ∈ S.erase 0, (Finset.univ.filter
            (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card := by
      rw [← Finset.add_sum_erase _ _ h0]
    rw [hsum_split, card_zero_annihilator]
    have hrest : 2 * (∑ x ∈ S.erase 0, (Finset.univ.filter
        (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card)
        = ((S.erase 0).card) * 2 ^ n := by
      rw [Finset.mul_sum]
      have heq : (∑ x ∈ S.erase 0, 2 * (Finset.univ.filter
          (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card)
          = ∑ x ∈ S.erase (0 : Fin n → ZMod 2), 2 ^ n := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_erase] at hx
        exact two_mul_card_dotProduct_eq_zero x hx.1
      rw [heq, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    have hcard_erase : (S.erase 0).card = S.card - 1 :=
      Finset.card_erase_of_mem h0
    have hpow : 2 * 2 ^ n = 2 ^ (n + 1) := by
      rw [pow_succ]
      ring
    simp only [h0, ↓reduceIte]
    rw [hcard_erase] at hrest
    have hmul : 2 * (2 ^ n + ∑ x ∈ S.erase 0, (Finset.univ.filter
        (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card)
        = 2 * 2 ^ n + 2 * (∑ x ∈ S.erase 0, (Finset.univ.filter
          (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card) := by
      ring
    rw [hmul, hrest, hpow]
    ring
  · have hall : 2 * (∑ x ∈ S, (Finset.univ.filter
        (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card)
        = S.card * 2 ^ n := by
      rw [Finset.mul_sum]
      have heq : (∑ x ∈ S, 2 * (Finset.univ.filter
          (fun a : Fin n → ZMod 2 => a ⬝ᵥ x = 0)).card)
          = ∑ x ∈ S, 2 ^ n := by
        apply Finset.sum_congr rfl
        intro x hx
        have hne : x ≠ 0 := fun heq => h0 (heq ▸ hx)
        exact two_mul_card_dotProduct_eq_zero x hne
      rw [heq, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    simp only [h0, ↓reduceIte]
    rw [Nat.sub_zero, add_zero]
    exact hall

end MathlibExt.Complexity.HashCounting

end
