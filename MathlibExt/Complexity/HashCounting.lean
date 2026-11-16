/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Hash counting over F2

Summing over all linear hashes the number of annihilated
elements of a finite set: each nonzero element is counted
half the time and the zero element always. The Stockmeyer
oracle protocol is not included here.
-/

@[expose] public section

/-- Pairing over `F2` (MOD-103 counting core). -/
def dotF2 {n : ℕ} (a v : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, a i * v i

private lemma zmod2_zero_or_one (y : ZMod 2) : y = 0 ∨ y = 1 := by
  have hall : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  exact hall y

private lemma zmod2_add_one_add_one (y : ZMod 2) : (y + 1) + 1 = y := by
  have hall : ∀ z : ZMod 2, (z + 1) + 1 = z := by decide
  exact hall y

private lemma flip_dotF2 {n : ℕ} (a x : Fin n → ZMod 2) (i₀ : Fin n)
    (hx : x i₀ = 1) :
    dotF2 (Function.update a i₀ (a i₀ + 1)) x = dotF2 a x + 1 := by
  unfold dotF2
  classical
  set f : Fin n → ZMod 2 := fun i => a i * x i with hf
  set b : ZMod 2 := (a i₀ + 1) * x i₀ with hb
  have hg : (fun i => (Function.update a i₀ (a i₀ + 1)) i * x i)
      = Function.update f i₀ b := by
    funext i
    by_cases hi : i = i₀
    · subst hi
      simp [f, b, Function.update_self]
    · simp [f, b, Function.update_of_ne hi]
  rw [hg]
  have hmem : i₀ ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i₀
  rw [Finset.sum_update_of_mem hmem f b]
  have h2 : (∑ x_1 ∈ Finset.univ, f x_1)
      = f i₀ + ∑ x_1 ∈ Finset.univ \ {i₀}, f x_1 := by
    rw [Finset.sdiff_singleton_eq_erase]
    rw [← Finset.add_sum_erase _ _ hmem]
  rw [h2]
  have hbi : b = a i₀ + 1 := by simp [b, hx]
  have hfi : f i₀ = a i₀ := by simp [f, hx]
  rw [hbi, hfi]
  abel

private lemma card_fun_fin_zmod2 (n : ℕ) :
    Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

private lemma exists_ne_zero_of_ne_zero {n : ℕ} {x : Fin n → ZMod 2} (hx : x ≠ 0) :
    ∃ i₀, x i₀ ≠ 0 := by
  by_contra h
  apply hx
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

private lemma halving {n : ℕ} (x : Fin n → ZMod 2) (hx : x ≠ 0) :
    2 * (Finset.univ.filter (fun a : Fin n → ZMod 2 => dotF2 a x = 0)).card
      = 2 ^ n := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_ne_zero_of_ne_zero hx
  have hxi1 : x i₀ = 1 := by
    rcases zmod2_zero_or_one (x i₀) with h | h
    · contradiction
    · exact h
  set e : (Fin n → ZMod 2) → (Fin n → ZMod 2) :=
    fun a => Function.update a i₀ (a i₀ + 1) with he
  have hinv : ∀ a, e (e a) = a := by
    intro a
    simp only [he]
    have hval : (Function.update a i₀ (a i₀ + 1)) i₀ + 1 = a i₀ := by
      rw [Function.update_self]
      exact zmod2_add_one_add_one (a i₀)
    rw [hval]
    rw [Function.update_idem]
    exact Function.update_eq_self i₀ a
  have hflip : ∀ a, dotF2 (e a) x = dotF2 a x + 1 := fun a => flip_dotF2 a x i₀ hxi1
  set A : Finset (Fin n → ZMod 2) :=
    Finset.univ.filter (fun a => dotF2 a x = 0) with hA
  set B : Finset (Fin n → ZMod 2) :=
    Finset.univ.filter (fun a => ¬ dotF2 a x = 0) with hB
  have hcard_eq : A.card = B.card := by
    apply Finset.card_bij (fun a _ => e a)
    · intro a ha
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
      have hfa := hflip a
      rw [ha] at hfa
      have h01 : (0 : ZMod 2) + 1 = 1 := by decide
      rw [h01] at hfa
      rw [hfa]
      decide
    · intro a₁ ha₁ a₂ ha₂ heq
      have h1 : e (e a₁) = e (e a₂) := by rw [heq]
      rw [hinv, hinv] at h1
      exact h1
    · intro b hb
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      refine ⟨e b, ?_, hinv b⟩
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
      have hfb := hflip b
      have hb1 : dotF2 b x = 1 := by
        rcases zmod2_zero_or_one (dotF2 b x) with h | h
        · contradiction
        · exact h
      rw [hb1] at hfb
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [h11] at hfb
      exact hfb
  have hsum : A.card + B.card = (Finset.univ : Finset (Fin n → ZMod 2)).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n → ZMod 2))) (fun a => dotF2 a x = 0)
    simpa [hA, hB] using h
  have hcard_univ : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by
    rw [Finset.card_univ, card_fun_fin_zmod2]
  omega

private lemma dotF2_zero_right {n : ℕ} (a : Fin n → ZMod 2) : dotF2 a 0 = 0 := by
  simp [dotF2]

private lemma card_zero_annihilator {n : ℕ} :
    (Finset.univ.filter (fun a : Fin n → ZMod 2 => dotF2 a 0 = 0)).card = 2 ^ n := by
  have h : Finset.univ.filter (fun a : Fin n → ZMod 2 => dotF2 a 0 = 0) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro a _
    exact dotF2_zero_right a
  rw [h, Finset.card_univ, card_fun_fin_zmod2]

/-- Hash-count identity: summing, over all linear hashes
`a`, the number of set elements annihilated by `a`, counts
each nonzero element `2^(n-1)` times (in doubled form) and
the zero element, if present, `2^n` times (doubled:
`2^(n+1)`). -/
theorem hash_count_identity {n : ℕ} (S : Finset (Fin n → ZMod 2)) :
    2 * (∑ a : Fin n → ZMod 2,
        (S.filter (fun x => dotF2 a x = 0)).card)
      = (S.card - (if (0 : Fin n → ZMod 2) ∈ S then 1 else 0)) * 2 ^ n
        + (if (0 : Fin n → ZMod 2) ∈ S then 2 ^ (n + 1) else 0) := by
  classical
  have hswap : (∑ a : Fin n → ZMod 2, (S.filter (fun x => dotF2 a x = 0)).card)
      = ∑ x ∈ S, (Finset.univ.filter (fun a : Fin n → ZMod 2 => dotF2 a x = 0)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  by_cases h0 : (0 : Fin n → ZMod 2) ∈ S
  · have hsum_split : (∑ x ∈ S, (Finset.univ.filter
        (fun a : Fin n → ZMod 2 => dotF2 a x = 0)).card)
        = (Finset.univ.filter (fun a : Fin n → ZMod 2 => dotF2 a 0 = 0)).card
          + ∑ x ∈ S.erase 0, (Finset.univ.filter
            (fun a : Fin n → ZMod 2 => dotF2 a x = 0)).card := by
      rw [← Finset.add_sum_erase _ _ h0]
    rw [hsum_split, card_zero_annihilator]
    have hrest : 2 * (∑ x ∈ S.erase 0, (Finset.univ.filter
        (fun a : Fin n → ZMod 2 => dotF2 a x = 0)).card)
        = ((S.erase 0).card) * 2 ^ n := by
      rw [Finset.mul_sum]
      have heq : (∑ x ∈ S.erase 0, 2 * (Finset.univ.filter
          (fun a : Fin n → ZMod 2 => dotF2 a x = 0)).card)
          = ∑ x ∈ S.erase (0 : Fin n → ZMod 2), 2 ^ n := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_erase] at hx
        exact halving x hx.1
      rw [heq, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    have hcard_erase : (S.erase 0).card = S.card - 1 :=
      Finset.card_erase_of_mem h0
    have hpow : 2 * 2 ^ n = 2 ^ (n + 1) := by
      rw [pow_succ]
      ring
    simp only [h0, ↓reduceIte]
    rw [hcard_erase] at hrest
    have hmul : 2 * (2 ^ n + ∑ x ∈ S.erase 0, (Finset.univ.filter
        (fun a : Fin n → ZMod 2 => dotF2 a x = 0)).card)
        = 2 * 2 ^ n + 2 * (∑ x ∈ S.erase 0, (Finset.univ.filter
          (fun a : Fin n → ZMod 2 => dotF2 a x = 0)).card) := by
      ring
    rw [hmul, hrest, hpow]
    ring
  · have hall : 2 * (∑ x ∈ S, (Finset.univ.filter
        (fun a : Fin n → ZMod 2 => dotF2 a x = 0)).card)
        = S.card * 2 ^ n := by
      rw [Finset.mul_sum]
      have heq : (∑ x ∈ S, 2 * (Finset.univ.filter
          (fun a : Fin n → ZMod 2 => dotF2 a x = 0)).card)
          = ∑ x ∈ S, 2 ^ n := by
        apply Finset.sum_congr rfl
        intro x hx
        have hne : x ≠ 0 := fun heq => h0 (heq ▸ hx)
        exact halving x hne
      rw [heq, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    simp only [h0, ↓reduceIte]
    rw [Nat.sub_zero, add_zero]
    exact hall

end
