/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSymmetricFunctions

import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Additive.VanDerWaerdenAP

/-!
# Vanishing classification for the sum-plus-product family

The family is vanishing modulo 2, 3, 4 and 8, only 1-vanishing modulo 6,
and fails to be 1-vanishing at every other modulus greater than 1.
-/

namespace MetaMathlibExt
namespace sumAddMulProd_one_classification

private def blockSum {n : ℕ} (a : ℕ → ZMod n) (s l : ℕ) : ZMod n :=
  ∑ i ∈ Finset.range l, a (s + i)

private def blockProd {n : ℕ} (a : ℕ → ZMod n) (s l : ℕ) : ZMod n :=
  ∏ i ∈ Finset.range l, a (s + i)

private theorem blockSum_add {n : ℕ} (a : ℕ → ZMod n) (s l k : ℕ) :
    blockSum a s (l + k) = blockSum a s l + blockSum a (s + l) k := by
  simp [blockSum, Finset.sum_range_add, Nat.add_assoc]

private theorem blockProd_add {n : ℕ} (a : ℕ → ZMod n) (s l k : ℕ) :
    blockProd a s (l + k) = blockProd a s l * blockProd a (s + l) k := by
  simp [blockProd, Finset.prod_range_add, Nat.add_assoc]

private def blockValue {n : ℕ} (a : ℕ → ZMod n) (s l : ℕ) : ZMod n :=
  blockSum a s l + blockProd a s l

private theorem family_eq_blockValue {n : ℕ} (a : ℕ → ZMod n) (s l : ℕ) :
    sumAddMulProdFamily 1 l (fun i => a (s + i)) = blockValue a s l := by
  unfold sumAddMulProdFamily blockValue blockSum blockProd
  rw [one_mul, Fin.sum_univ_eq_sum_range (fun i => a (s + i)),
    Fin.prod_univ_eq_prod_range (fun i => a (s + i))]

private theorem not_one_of_word {n : ℕ} (a : ℕ → ZMod n)
    (h : ∀ s l, 2 ≤ l → blockValue a s l ≠ 0) :
    ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod n)) := by
  intro ha
  obtain ⟨l, hl, s, hs⟩ := ha a
  exact h s l hl (by simpa [family_eq_blockValue] using hs 0 Nat.zero_lt_one)

private theorem not_one_of_dvd {d n : ℕ} (hd : d ∣ n)
    (h : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod d))) :
    ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod n)) := by
  let f := ZMod.castHom hd (ZMod d)
  intro hn
  apply h
  intro a
  let b (i : ℕ) := (ZMod.castHom_surjective hd (a i)).choose
  have hb (i : ℕ) : f (b i) = a i := (ZMod.castHom_surjective hd (a i)).choose_spec
  obtain ⟨l, hl, s, hs⟩ := hn b
  refine ⟨l, hl, s, fun j hj => ?_⟩
  simpa [sumAddMulProdFamily, map_sum, map_prod, hb] using congrArg f (hs j hj)

private def repeatWord {n p : ℕ} [NeZero p] (w : Fin p → ZMod n) (i : ℕ) : ZMod n :=
  w (Fin.ofNat p i)

private theorem repeatWord_add {n p : ℕ} [NeZero p] (w : Fin p → ZMod n) (s i : ℕ) :
    repeatWord w (s + i) = repeatWord w (s % p + i) := by
  unfold repeatWord
  congr 1
  apply Fin.ext
  change (s + i) % p = (s % p + i) % p
  rw [Nat.mod_add_mod]

private theorem repeatWord_add_period {n p : ℕ} [NeZero p]
    (w : Fin p → ZMod n) (s i : ℕ) :
    repeatWord w (s + p + i) = repeatWord w (s + i) := by
  rw [repeatWord_add w (s + p) i, repeatWord_add w s i, Nat.add_mod_right]

private theorem blockValue_mod_start {n p : ℕ} [NeZero p] (w : Fin p → ZMod n) (s l : ℕ) :
    blockValue (repeatWord w) s l = blockValue (repeatWord w) (s % p) l := by
  simp only [blockValue, blockSum, blockProd, repeatWord_add w s]

-- A period acts as the identity on block values once the block has at least b terms.
private theorem blockValue_add_period {n p : ℕ} [NeZero p] (w : Fin p → ZMod n)
    (b : ℕ) (hsum : ∀ i : Fin p, blockSum (repeatWord w) i p = 0)
    (hprod : ∀ i : Fin p,
      blockProd (repeatWord w) i p * blockProd (repeatWord w) i b =
        blockProd (repeatWord w) i b) (s l : ℕ) (hl : b ≤ l) :
    blockValue (repeatWord w) s (l + p) = blockValue (repeatWord w) s l := by
  have hsum' : blockSum (repeatWord w) s p = 0 := by
    have h := hsum (Fin.ofNat p s)
    change blockSum (repeatWord w) (s % p) p = 0 at h
    simpa only [blockSum, repeatWord_add w s] using h
  have hprod' : blockProd (repeatWord w) s p * blockProd (repeatWord w) s b =
      blockProd (repeatWord w) s b := by
    have h := hprod (Fin.ofNat p s)
    change blockProd (repeatWord w) (s % p) p * blockProd (repeatWord w) (s % p) b =
      blockProd (repeatWord w) (s % p) b at h
    simpa only [blockProd, repeatWord_add w s] using h
  rw [Nat.add_comm l p]
  simp only [blockValue, blockSum_add _ _ p l, blockProd_add _ _ p l, hsum', zero_add]
  have hS : blockSum (repeatWord w) (s + p) l = blockSum (repeatWord w) s l := by
    simp only [blockSum, repeatWord_add_period]
  have hP : blockProd (repeatWord w) (s + p) l = blockProd (repeatWord w) s l := by
    simp only [blockProd, repeatWord_add_period]
  rw [hS, hP]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [blockProd_add, ← mul_assoc, hprod']

private theorem reduce_block_length {n p b : ℕ} [NeZero p] (a : ℕ → ZMod n)
    (h : ∀ s l, b ≤ l → blockValue a s (l + p) = blockValue a s l) {s l : ℕ} (hl : b ≤ l) :
    blockValue a s l = blockValue a s ((l - b) % p + b) := by
  have aux (q r : ℕ) :
      blockValue a s (r + b + q * p) = blockValue a s (r + b) := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, h s _ (by omega), ih]
  conv_lhs => rw [← Nat.sub_add_cancel hl, ← Nat.mod_add_div (l - b) p]
  simpa [Nat.mul_comm, Nat.add_right_comm] using aux ((l - b) / p) ((l - b) % p)

private theorem not_one_of_period {n p b : ℕ} [NeZero p] (w : Fin p → ZMod n)
    (hb : b ≤ 2) (hsum : ∀ i : Fin p, blockSum (repeatWord w) i p = 0)
    (hprod : ∀ i : Fin p,
      blockProd (repeatWord w) i p * blockProd (repeatWord w) i b =
        blockProd (repeatWord w) i b)
    (hne : ∀ i j : Fin p, blockValue (repeatWord w) i (j.val + b) ≠ 0) :
    ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod n)) := by
  apply not_one_of_word (repeatWord w)
  intro s l hl
  rw [reduce_block_length (repeatWord w) (blockValue_add_period w b hsum hprod)
    (hb.trans hl), blockValue_mod_start w]
  exact hne (Fin.ofNat p s) (Fin.ofNat p (l - b))

private theorem not_one_five : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 5)) := by
  apply not_one_of_period ![(2 : ZMod 5), 3] (b := 0) (by decide) <;> decide +kernel

private theorem not_one_seven : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 7)) := by
  apply not_one_of_period ![(2 : ZMod 7), 3, 3, 3, 3] (b := 0) (by decide) <;> decide +kernel

private theorem not_one_nine : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 9)) := by
  apply not_one_of_period ![(7 : ZMod 9), 4, 4, 7, 4, 4, 7, 4, 4] (b := 0) (by decide) <;>
    decide +kernel

private theorem not_one_twelve : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 12)) := by
  apply not_one_of_period ![(2 : ZMod 12), -2, 2, -2] (b := 2) (by decide) <;> decide +kernel

private theorem not_one_sixteen : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 16)) := by
  apply not_one_of_period ![(3 : ZMod 16), -3, 3, -3] (b := 0) (by decide) <;> decide +kernel

private theorem not_two_six : ¬ IsMVanishingFamily 2 (sumAddMulProdFamily (1 : ZMod 6)) := by
  let w : Fin 4 → ZMod 6 := ![1, 3, 5, 3]
  let a := repeatWord w
  have hperiod := blockValue_add_period w 2 (by decide +kernel) (by decide +kernel)
  have htable : ∀ i j : Fin 4,
      blockValue a i (j.val + 2) = 0 → blockValue a (i.val + j.val + 2) (j.val + 2) ≠ 0 := by
    decide +kernel
  intro h
  obtain ⟨l, hl, s, hs⟩ := h a
  have h0 : blockValue a s l = 0 := by simpa [family_eq_blockValue] using hs 0 (by decide)
  have h1 : blockValue a (s + l) l = 0 := by simpa [family_eq_blockValue] using hs 1 (by decide)
  let r := (l - 2) % 4 + 2
  have hr : l % 4 = r % 4 := by
    dsimp [r]
    rw [Nat.mod_add_mod, Nat.sub_add_cancel hl]
  rw [reduce_block_length a hperiod hl, blockValue_mod_start w] at h0 h1
  have hstart : (s + l) % 4 = (s % 4 + r) % 4 := by
    rw [Nat.mod_add_mod]
    simp [Nat.add_mod, hr]
  have h1' : blockValue a (s % 4 + r) r = 0 := by
    rw [blockValue_mod_start w, ← hstart]
    exact h1
  exact htable (Fin.ofNat 4 s) (Fin.ofNat 4 (l - 2)) h0 (by simpa [Nat.add_assoc] using h1')

-- The period (2, 1/2, -2, -1/2) has sum 0 and product 1.
-- Twice the block value for every remaining starting point and length is a small nonzero integer.
private theorem not_one_prime_gt_seven {p : ℕ} (hp : p.Prime) (h7 : 7 < p) :
    ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod p)) := by
  have hp8 : 8 < p := by
    by_contra! h
    have heq : p = 8 := by omega
    exact (by decide : ¬ Nat.Prime 8) (heq ▸ hp)
  have h2 : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact fun h => (Nat.not_le_of_gt (by omega)) (Nat.le_of_dvd (by decide : 0 < 2) h)
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime 2 p).2 h2
  let y : ZMod p := ↑u⁻¹
  have hy : (2 : ZMod p) * y = 1 := by
    change (↑(2 : ℕ) : ZMod p) * y = 1
    rw [← hu]
    exact u.mul_inv
  let w : Fin 4 → ZMod p := ![2, y, -2, -y]
  apply not_one_of_period w (b := 0) (by decide)
  · intro i
    fin_cases i <;>
      norm_num [w, blockSum, Finset.sum_range_succ, repeatWord, Fin.ofNat]
  · intro i
    fin_cases i <;>
      norm_num [w, blockProd, Finset.prod_range_succ, repeatWord, Fin.ofNat] <;>
      linear_combination (2 * y + 1) * hy
  · let table : Fin 4 → Fin 4 → ℤ :=
      ![![2, 8, 7, -3], ![2, 2, -5, -3], ![2, -8, -3, 3], ![2, -2, 1, 3]]
    have htable (i j : Fin 4) :
        2 * blockValue (repeatWord w) i (j.val + 0) = (table i j : ZMod p) := by
      fin_cases i <;> fin_cases j <;>
        norm_num [w, table, blockValue, blockSum, blockProd, Finset.sum_range_succ,
          Finset.prod_range_succ, repeatWord, Fin.ofNat] <;> grind
    have hnz (k : ℕ) (hk : 0 < k) (hk' : k ≤ 8) : (k : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact fun h => (Nat.not_le_of_gt (hk'.trans_lt hp8)) (Nat.le_of_dvd hk h)
    intro i j h
    have heq := htable i j
    rw [h, mul_zero, eq_comm] at heq
    fin_cases i <;> fin_cases j <;> norm_num [table] at heq <;>
      first
      | exact hnz 1 (by decide) (by decide) (Nat.cast_one.trans heq)
      | exact hnz 2 (by decide) (by decide) heq
      | exact hnz 3 (by decide) (by decide) heq
      | exact hnz 5 (by decide) (by decide) heq
      | exact hnz 7 (by decide) (by decide) heq
      | exact hnz 8 (by decide) (by decide) heq

private theorem not_one_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod p)) := by
  by_cases h7 : 7 < p
  · exact not_one_prime_gt_seven hp h7
  have heq : p = 5 ∨ p = 7 := by
    have h4 : p ≠ 4 := fun h => (by decide : ¬ Nat.Prime 4) (h ▸ hp)
    have h6 : p ≠ 6 := fun h => (by decide : ¬ Nat.Prime 6) (h ▸ hp)
    omega
  rcases heq with rfl | rfl
  · exact not_one_five
  · exact not_one_seven

private theorem small_modulus (n : ℕ) :
    ¬ (9 ∣ n) → ¬ (12 ∣ n) → ¬ (16 ∣ n) →
      (∀ p, p.Prime → p ∣ n → p ≤ 3) →
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro h9 h12 h16 hp
    have hn : n ≠ 0 := fun h => h9 (h ▸ dvd_zero 9)
    by_cases h1 : n = 1
    · exact Or.inl h1
    have hmin := Nat.minFac_prime h1
    have hd := Nat.minFac_dvd n
    have hle := hp _ hmin hd
    have hge := hmin.two_le
    obtain ⟨k, hk⟩ := hd
    have hkpos : 0 < k := by
      by_contra! hz
      have : k = 0 := by omega
      subst k
      rw [mul_zero] at hk
      exact hn hk
    have hklt : k < n := by
      rw [hk]
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hmin.one_lt hkpos
    have hkn : k ∣ n := by rw [hk]; exact dvd_mul_left _ _
    have hclass := ih k hklt (fun h => h9 (h.trans hkn)) (fun h => h12 (h.trans hkn))
      (fun h => h16 (h.trans hkn)) (fun q hq hqk => hp q hq (hqk.trans hkn))
    have hfac : n.minFac = 2 ∨ n.minFac = 3 := by omega
    rcases hclass with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hfac with h | h <;> rw [h] at hk <;> subst n <;>
      first
      | exact False.elim (h9 (by decide))
      | exact False.elim (h12 (by decide))
      | exact False.elim (h16 (by decide))
      | decide

private theorem not_one_other {n : ℕ} (hn : 1 < n)
    (h : n ∉ ({2, 3, 4, 6, 8} : Finset ℕ)) :
    ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod n)) := by
  by_cases h9 : 9 ∣ n
  · exact not_one_of_dvd h9 not_one_nine
  by_cases h12 : 12 ∣ n
  · exact not_one_of_dvd h12 not_one_twelve
  by_cases h16 : 16 ∣ n
  · exact not_one_of_dvd h16 not_one_sixteen
  by_cases hp : ∃ p, p.Prime ∧ p ∣ n ∧ 3 < p
  · obtain ⟨p, hprime, hd, h3⟩ := hp
    exact not_one_of_dvd hd (not_one_prime hprime h3)
  have hclass := small_modulus n h9 h12 h16
    (fun p hprime hd => Nat.le_of_not_gt (fun h3 => hp ⟨p, hprime, hd, h3⟩))
  rcases hclass with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  all_goals exact False.elim (h (by decide))

private theorem finite_progression (κ : Type) [Finite κ] [Nonempty κ] (m : ℕ) :
    ∃ N, ∀ c : ℕ → κ, ∃ s d, 0 < d ∧ s + m * d ≤ N ∧
      ∀ j ≤ m, c (s + j * d) = c s := by
  let _ := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  obtain ⟨N, hN⟩ := vanDerWaerden (Fintype.card κ) (m + 1) Fintype.card_pos (by omega)
  refine ⟨N, fun c => ?_⟩
  obtain ⟨s, d, hs, hd, hbound, hmono⟩ := hN (fun k => e (c k.val))
  simp only [Nat.add_sub_cancel] at hbound
  refine ⟨s, d, hd, hbound, fun j hj => e.injective (hmono j (by omega) (by omega) ?_ ?_)⟩
  · exact (Nat.add_le_add_left (Nat.mul_le_mul_right d hj) s).trans hbound
  · exact ⟨hs, (Nat.le_add_right s (m * d)).trans hbound⟩

private theorem square_eq_one_blockProd {n : ℕ} (a : ℕ → ZMod n) (s l : ℕ)
    (h : ∀ i < l, a (s + i) * a (s + i) = 1) :
    blockProd a s l * blockProd a s l = 1 := by
  unfold blockProd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i hi => h i (Finset.mem_range.mp hi)

private theorem blockValue_drop_last {n : ℕ} (a : ℕ → ZMod n) (s l : ℕ)
    (hsum : blockSum a s (l + 1) = 0) (hprod : blockProd a s (l + 1) = 1)
    (hlast : a (s + l) * a (s + l) = 1) : blockValue a s l = 0 := by
  have hS : blockSum a s l + a (s + l) = 0 := by
    simpa only [blockSum, Finset.sum_range_succ] using hsum
  have hP : blockProd a s l * a (s + l) = 1 := by
    simpa only [blockProd, Finset.prod_range_succ] using hprod
  have h : blockProd a s l = a (s + l) := by
    calc
      _ = (blockProd a s l * a (s + l)) * a (s + l) := by rw [mul_assoc, hlast, mul_one]
      _ = _ := by rw [hP, one_mul]
  simpa only [blockValue, h] using hS

-- Inside a window of self-inverse units, match both prefix values and the next m entries.
-- Shift successive blocks by offsets m, m-1, ... so that deleting the last entry of
-- each shifted block leaves consecutive blocks of the same length.
private theorem vanishing_of_unit_window {n m N : ℕ} (a : ℕ → ZMod n) (u : ℕ)
    (hN : ∀ c : ℕ → ZMod n × ZMod n × (Fin m → ZMod n), ∃ s d, 0 < d ∧ s + m * d ≤ N ∧
      ∀ j ≤ m, c (s + j * d) = c s)
    (hu : ∀ i < 3 * N + m, a (u + i) * a (u + i) = 1) :
    ∃ l, 1 < l ∧ ∃ s, ∀ j < m, blockValue a (s + j * l) l = 0 := by
  let b (i : ℕ) := a (u + i)
  let c (k : ℕ) := (blockSum b 0 (3 * k), blockProd b 0 (3 * k), fun i : Fin m => b (3 * k + i))
  obtain ⟨s, d, hd, hbound, hmono⟩ := hN c
  let D := 3 * d
  let t (j : ℕ) := 3 * s + j * D
  have ht (j : ℕ) : t j = 3 * (s + j * d) := by dsimp [t, D]; ring
  have hD : 3 ≤ D := by dsimp [D]; omega
  refine ⟨D - 1, by omega, u + (3 * s + m), fun j hj => ?_⟩
  let r := m - j
  let k := t j + r
  have hend : t (j + 1) + r = k + D := by simp only [t, k, Nat.succ_mul]; omega
  have hstart : k = 3 * s + m + j * (D - 1) := by
    have h : j * (D - 1) + j = j * D := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    dsimp [k, t, r]
    omega
  have hk : k + D ≤ 3 * N + m := by
    rw [← hend, ht]
    have hj' : j + 1 ≤ m := by omega
    have h := (Nat.add_le_add_left (Nat.mul_le_mul_right d hj') s).trans hbound
    dsimp [r]
    omega
  have hcolor : c (s + j * d) = c (s + (j + 1) * d) :=
    (hmono j hj.le).trans (hmono (j + 1) hj).symm
  have hS : blockSum b 0 (t j) = blockSum b 0 (t (j + 1)) := by
    simpa only [ht, c] using congrArg Prod.fst hcolor
  have hP : blockProd b 0 (t j) = blockProd b 0 (t (j + 1)) := by
    simpa only [ht, c] using congrArg (fun x => x.2.1) hcolor
  have htail (i : ℕ) (hi : i < r) : b (t j + i) = b (t (j + 1) + i) := by
    let i' : Fin m := ⟨i, by dsimp [r] at hi; omega⟩
    simpa only [c, ht] using congrFun (congrArg (fun x => x.2.2) hcolor) i'
  have hsum : blockSum b k D = 0 := by
    have heq : blockSum b 0 k = blockSum b 0 (k + D) := by
      rw [← hend, show k = t j + r from rfl, blockSum_add b 0 (t j) r,
        blockSum_add b 0 (t (j + 1)) r, hS, zero_add, zero_add]
      congr 1
      exact Finset.sum_congr rfl fun i hi => htail i (Finset.mem_range.mp hi)
    rw [blockSum_add b 0 k D, zero_add] at heq
    exact add_left_cancel (heq.symm.trans (add_zero _).symm)
  have hprod : blockProd b k D = 1 := by
    have heq : blockProd b 0 k = blockProd b 0 (k + D) := by
      rw [← hend, show k = t j + r from rfl, blockProd_add b 0 (t j) r,
        blockProd_add b 0 (t (j + 1)) r, hP, zero_add, zero_add]
      congr 1
      exact Finset.prod_congr rfl fun i hi => htail i (Finset.mem_range.mp hi)
    rw [blockProd_add b 0 k D, zero_add] at heq
    have hsq := square_eq_one_blockProd b 0 k (fun i hi => by
      simpa only [zero_add] using hu i (by omega))
    calc
      _ = blockProd b 0 k * (blockProd b 0 k * blockProd b k D) := by
        rw [← mul_assoc, hsq, one_mul]
      _ = 1 := by rw [← heq, hsq]
  have hz := blockValue_drop_last b k (D - 1)
    (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ D)])
    (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ D)])
    (hu (k + (D - 1)) (by omega))
  simpa only [blockValue, blockSum, blockProd, b, hstart, Nat.add_assoc] using hz

-- If every short window contains a nonunit, a longer block contains three of them.
-- Their product is zero at each of the four vanishing moduli.
private theorem vanishing_of_nonunit_windows {n m W : ℕ} [NeZero n] (a : ℕ → ZMod n)
    (hw : ∀ s, ∃ i < W, a (s + i) * a (s + i) ≠ 1)
    (hmul : ∀ x y : ZMod n, x * x ≠ 1 → (x * y) * (x * y) ≠ 1)
    (hzero : ∀ x y z : ZMod n, x * x ≠ 1 → y * y ≠ 1 → z * z ≠ 1 → x * y * z = 0) :
    ∃ l, 1 < l ∧ ∃ s, ∀ j < m, blockValue a (s + j * l) l = 0 := by
  have hbad (s : ℕ) : blockProd a s W * blockProd a s W ≠ 1 := by
    obtain ⟨i, hi, hne⟩ := hw s
    unfold blockProd
    rw [← Finset.mul_prod_erase (Finset.range W) (fun i => a (s + i)) (Finset.mem_range.mpr hi)]
    exact hmul _ _ hne
  have hlong (s l : ℕ) (hl : W + W + W ≤ l) : blockProd a s l = 0 := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hl
    rw [blockProd_add, blockProd_add _ _ (W + W) W, blockProd_add _ _ W W,
      hzero _ _ _ (hbad _) (hbad _) (hbad _), zero_mul]
  let L := W + W + W + 2
  obtain ⟨d, hd, s, c, hc⟩ := Combinatorics.exists_mono_homothetic_copy
    (Finset.range (m + 1)) (fun k => blockSum a 0 (k * L))
  have hmono (j : ℕ) (hj : j ≤ m) : blockSum a 0 (s * L + j * (d * L)) = c := by
    simpa [nsmul_eq_mul, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.add_comm] using hc j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hL : L ≤ d * L := by simpa using Nat.mul_le_mul_right L (Nat.one_le_iff_ne_zero.mpr hd.ne')
  have hLtwo : 1 < L := by dsimp [L]; omega
  have hLW : W + W + W ≤ L := by dsimp [L]; omega
  refine ⟨d * L, hLtwo.trans_le hL, s * L, fun j hj => ?_⟩
  have hsum := hmono (j + 1) hj
  rw [Nat.succ_mul, ← Nat.add_assoc, blockSum_add, zero_add, hmono j hj.le] at hsum
  have hz : blockSum a (s * L + j * (d * L)) (d * L) = 0 :=
    add_left_cancel (hsum.trans (add_zero _).symm)
  rw [blockValue, hz, hlong _ _ (hLW.trans hL), zero_add]

private theorem vanishing_of_unit_arithmetic {n : ℕ} [NeZero n]
    (hmul : ∀ x y : ZMod n, x * x ≠ 1 → (x * y) * (x * y) ≠ 1)
    (hzero : ∀ x y z : ZMod n, x * x ≠ 1 → y * y ≠ 1 → z * z ≠ 1 → x * y * z = 0) :
    IsVanishingFamily (sumAddMulProdFamily (1 : ZMod n)) := by
  classical
  intro m _ a
  obtain ⟨N, hN⟩ := finite_progression (ZMod n × ZMod n × (Fin m → ZMod n)) m
  let W := 3 * N + m
  suffices h : ∃ l, 1 < l ∧ ∃ s, ∀ j < m, blockValue a (s + j * l) l = 0 by
    simpa only [family_eq_blockValue] using h
  by_cases hex : ∃ u, ∀ i < W, a (u + i) * a (u + i) = 1
  · obtain ⟨u, hu⟩ := hex
    exact vanishing_of_unit_window a u hN hu
  · push Not at hex
    exact vanishing_of_nonunit_windows a hex hmul hzero

end sumAddMulProd_one_classification

open sumAddMulProd_one_classification in
/-- **Classification of vanishing for the sum-plus-product family $F_1$.** Let $n > 1$ and let
$F_1$ be the family over $\mathbb{Z}/n$ given by
$F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$. If $n \notin \{2, 3, 4, 6, 8\}$,
then $F_1$ is not $m$-vanishing for any $m > 0$. If $n \in \{2, 3, 4, 8\}$, then $F_1$ is
vanishing. If $n = 6$, then $F_1$ is $1$-vanishing but not $m$-vanishing for any $m > 1$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 3
(`integers-2026-A25-thm-3`). -/
public theorem sumAddMulProd_one_classification {n : ℕ} (hn : 1 < n) :
    (n ∉ ({2, 3, 4, 6, 8} : Finset ℕ) →
      ∀ m, 0 < m → ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n))) ∧
    (n ∈ ({2, 3, 4, 8} : Finset ℕ) → IsVanishingFamily (sumAddMulProdFamily (1 : ZMod n))) ∧
    (n = 6 → IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod n)) ∧
      ∀ m, 1 < m → ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n))) := by
  refine ⟨fun h m hm hmvanish => not_one_other hn h (hmvanish.mono hm), ?_, ?_⟩
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl <;>
      exact vanishing_of_unit_arithmetic (by decide +kernel) (by decide +kernel)
  · rintro rfl
    exact ⟨isMVanishingFamily_one_sumAddMulProd_one_six,
      fun m hm h => not_two_six (h.mono hm)⟩

end MetaMathlibExt
