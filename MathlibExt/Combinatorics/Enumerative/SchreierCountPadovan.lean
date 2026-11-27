/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GeneralizedSchreierPadovan
import Mathlib.Order.Interval.Finset.Nat

/-!
# Schreier counts as Padovan-like sequences

The number of $(p, q)$-Schreier sets, and the number of maximal $(p, q)$-Schreier sets, with a
given maximum are the values of the Padovan-like sequences of Chu and Vasseur at multiples of
$q$.
-/

namespace MetaMathlibExt.schreierCount_eq_schreierPadovan

open Finset

/-- Count with an offset in the cardinality constraint, to track finite differences. -/
private def family (p q t n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter fun F =>
    n ∈ F ∧ ∃ a ∈ F, F ⊆ Icc a n ∧ p * (F.card + t) ≤ q * a

private theorem mem_family {p q t n : ℕ} {F : Finset ℕ} :
    F ∈ family p q t n ↔
      n ∈ F ∧ ∃ a ∈ F, 0 < a ∧ F ⊆ Icc a n ∧ p * (F.card + t) ≤ q * a := by
  simp only [family, mem_filter, mem_powerset, subset_iff, mem_Icc]
  grind

private theorem card_family_zero {p q : ℕ} (n : ℕ) :
    (family p q 0 n).card = schreierCount p q n := by
  unfold schreierCount
  congr 1
  ext F
  simp only [mem_family, mem_filter, mem_powerset, subset_iff, mem_Icc, Nat.add_zero]
  constructor
  · rintro ⟨hn, a, ha, hpos, hb, he⟩
    refine ⟨fun x hx => ⟨hpos.trans_le (hb hx).1, (hb hx).2⟩, hn, ?_⟩
    intro x hx
    exact le_trans he (Nat.mul_le_mul_left q (hb hx).1)
  · rintro ⟨hb, hn, hmin⟩
    have hne : F.Nonempty := ⟨n, hn⟩
    classical
    refine ⟨hn, F.min' hne, F.min'_mem hne, (hb (F.min'_mem hne)).1,
      fun x hx => ⟨by
        have h1 := (hb (F.min'_mem hne)).1
        have h2 := F.min'_le x hx
        omega, (hb hx).2⟩,
      hmin _ (F.min'_mem hne)⟩

/-- Moving the maximum past no other element preserves the cardinality and the minimum. -/
private theorem replace_max {p q t n m : ℕ} {F : Finset ℕ} (hp : 0 < p)
    (h : p * (t + 1) ≤ q * m) (hF : F ∈ family p q t n)
    (hbelow : ∀ x ∈ F, x ≠ n → x < m) :
    insert m (F.erase n) ∈ family p q t m := by
  obtain ⟨hn, a, ha, hpos, hsub, he⟩ := mem_family.mp hF
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hmpos
    · subst h0
      simp only [Nat.mul_zero] at h
      have hpos : 0 < p * (t + 1) := Nat.mul_pos hp (Nat.succ_pos t)
      exact absurd h (Nat.not_le_of_gt hpos)
    · exact hmpos
  by_cases ha_eq : a = n
  · have hFeq : F = {n} := by
      ext x
      simp only [subset_iff, mem_Icc, mem_singleton] at *
      grind
    rw [hFeq]
    simp only [erase_singleton, insert_empty]
    refine mem_family.mpr ⟨mem_singleton_self m, m, mem_singleton_self m, hmpos, ?_, ?_⟩
    · simp
    · rw [card_singleton, show (1 : ℕ) + t = t + 1 from Nat.add_comm 1 t]
      exact h
  · have ham : a < m := hbelow a ha ha_eq
    have hmerase : m ∉ F.erase n := fun h =>
      (hbelow m (mem_erase.mp h).2 (mem_erase.mp h).1).false
    have hcard : 1 ≤ F.card := card_pos.mpr ⟨n, hn⟩
    refine mem_family.mpr ⟨mem_insert_self .., a,
      mem_insert_of_mem (mem_erase.mpr ⟨ha_eq, ha⟩), hpos, ?_, ?_⟩
    · intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact mem_Icc.mpr ⟨ham.le, le_rfl⟩
      · obtain ⟨hyn, hyF⟩ := mem_erase.mp hy
        exact mem_Icc.mpr ⟨(mem_Icc.mp (hsub hyF)).1, (hbelow y hyF hyn).le⟩
    · rw [card_insert_of_notMem hmerase, card_erase_of_mem hn, Nat.sub_add_cancel hcard]
      exact he

private theorem difference_step {p q t m : ℕ} (hp : 0 < p)
    (h : p * (t + 1) ≤ q * m) :
    (family p q t (m + 1)).card = (family p q t m).card + (family p q (t + 1) m).card := by
  let S := family p q t (m + 1)
  have withPrev : (S.filter fun F => m ∈ F).card = (family p q (t + 1) m).card := by
    apply card_nbij' (fun F => F.erase (m + 1)) (insert (m + 1))
    · intro F hF
      obtain ⟨hF, hmF⟩ := mem_filter.mp hF
      obtain ⟨hn, a, ha, hpos, hsub, he⟩ := mem_family.mp hF
      have han : a ≠ m + 1 := by
        have hle := (mem_Icc.mp (hsub hmF)).1
        omega
      have hcard := card_pos.mpr ⟨m, hmF⟩
      refine mem_family.mpr ⟨mem_erase.mpr ⟨by omega, hmF⟩, a,
        mem_erase.mpr ⟨han, ha⟩, hpos, ?_, ?_⟩
      · simp only [subset_iff, mem_erase, mem_Icc] at *
        grind
      · rw [card_erase_of_mem hn, show F.card - 1 + (t + 1) = F.card + t by omega]
        exact he
    · intro F hF
      obtain ⟨hmF, a, ha, hpos, hsub, he⟩ := mem_family.mp hF
      have hnew : m + 1 ∉ F := fun h => (Nat.not_succ_le_self m) (mem_Icc.mp (hsub h)).2
      refine mem_filter.mpr ⟨mem_family.mpr ⟨mem_insert_self .., a, mem_insert_of_mem ha,
        hpos, ?_, ?_⟩, mem_insert_of_mem hmF⟩
      · simp only [subset_iff, mem_insert, mem_Icc] at *
        grind
      · rwa [card_insert_of_notMem hnew, show F.card + 1 + t = F.card + (t + 1) by omega]
    · intro F hF
      exact insert_erase (mem_family.mp (mem_filter.mp hF).1).1
    · intro F hF
      obtain ⟨-, a, -, -, hsub, -⟩ := mem_family.mp hF
      apply erase_insert
      intro h
      have := (mem_Icc.mp (hsub h)).2
      omega
  have withoutPrev : (S.filter fun F => m ∉ F).card = (family p q t m).card := by
    apply card_nbij' (fun F => insert m (F.erase (m + 1)))
      (fun F => insert (m + 1) (F.erase m))
    · intro F hF
      obtain ⟨hF, hmF⟩ := mem_filter.mp hF
      apply replace_max hp h hF
      obtain ⟨-, a, -, -, hsub, -⟩ := mem_family.mp hF
      intro x hx hxn
      have hxm : x ≠ m := fun h => hmF (h ▸ hx)
      have hle := (mem_Icc.mp (hsub hx)).2
      omega
    · intro F hF
      refine mem_filter.mpr ⟨replace_max hp ?_ hF ?_, by simp⟩
      · calc p * (t + 1) ≤ q * m := h
        _ ≤ q * (m + 1) := Nat.mul_le_mul_left q (Nat.le_succ m)
      · obtain ⟨-, a, -, -, hsub, -⟩ := mem_family.mp hF
        intro x hx _
        exact Nat.lt_succ_of_le (mem_Icc.mp (hsub hx)).2
    · intro F hF
      obtain ⟨hF, hmF⟩ := mem_filter.mp hF
      have hnF := (mem_family.mp hF).1
      ext x
      simp only [mem_insert, mem_erase]
      grind
    · intro F hF
      obtain ⟨hmF, a, -, -, hsub, -⟩ := mem_family.mp hF
      ext x
      simp only [subset_iff, mem_insert, mem_Icc, mem_erase] at *
      grind
  rw [← withPrev, ← withoutPrev, add_comm (card _), card_filter_add_card_filter_not]

/-- In the initial range the family has at most two members: the singleton and the pair. -/
private theorem mem_family_of_base {p q t n : ℕ} (hp : 0 < p)
    (hK : t * p + q ≤ n * q) (hlt : n * q - t * p - q < p + q) (hn : 1 ≤ n)
    {F : Finset ℕ} :
    F ∈ family p q t n ↔
      (F = {n} ∧ p * (1 + t) ≤ q * n) ∨
        (F = insert (n - 1) {n} ∧ p * (2 + t) ≤ q * (n - 1)) := by
  constructor
  · intro hF
    obtain ⟨hnF, a, ha, hpos, hsub, he⟩ := mem_family.mp hF
    have hsub1n : F ⊆ Icc 1 n := fun x hx => mem_Icc.mpr
      ⟨le_trans hpos (mem_Icc.mp (hsub hx)).1, (mem_Icc.mp (hsub hx)).2⟩
    have hcard_le : F.card ≤ n := by
      have h := card_le_card hsub1n
      rwa [Nat.card_Icc] at h
    have ha_le : a ≤ n + 1 - F.card := by
      have h := card_le_card hsub
      rw [Nat.card_Icc] at h
      have hle : a ≤ n := (mem_Icc.mp (hsub ha)).2
      omega
    have hk2 : F.card ≤ 2 := by
      by_contra hk
      have hk : 2 < F.card := Nat.not_le.mp hk
      have h1 : p * F.card + t * p ≤ q * a := by
        have hmul := he
        rw [Nat.mul_add, Nat.mul_comm p t] at hmul
        exact hmul
      have h2 : q * a + q * F.card ≤ q * n + q := by
        have haq : q * a ≤ q * (n + 1 - F.card) := Nat.mul_le_mul_left q ha_le
        have hsum : q * (n + 1 - F.card) + q * F.card = q * n + q := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (by omega : F.card ≤ n + 1)]
          rw [Nat.mul_succ]
        omega
      have hlt' : q * n < t * p + p + 2 * q := by
        have hcomm : n * q = q * n := Nat.mul_comm n q
        omega
      have hp3 : 3 * p ≤ p * F.card := by
        calc 3 * p = p * 3 := by ring
        _ ≤ p * F.card := Nat.mul_le_mul_left p (by omega)
      have hq3 : 3 * q ≤ q * F.card := by
        calc 3 * q = q * 3 := by ring
        _ ≤ q * F.card := Nat.mul_le_mul_left q (by omega)
      omega
    have hposcard : 1 ≤ F.card := card_pos.mpr ⟨n, hnF⟩
    rcases Nat.lt_or_ge F.card 2 with hk1 | hk2'
    · -- The family member is a singleton, hence `{n}`.
      have hcard1 : F.card = 1 := by omega
      have hFeq : F = {n} := by
        obtain ⟨x, hx⟩ := card_eq_one.mp hcard1
        have hmem : n ∈ ({x} : Finset ℕ) := by rw [← hx]; exact hnF
        have hxeq : x = n := (mem_singleton.mp hmem).symm
        rw [hx, hxeq]
      refine Or.inl ⟨hFeq, ?_⟩
      have ha_eq : a = n := mem_singleton.mp (hFeq ▸ ha)
      rw [hcard1, ha_eq] at he
      exact he
    · have hcard2 : F.card = 2 := by omega
      -- The minimum must be `n - 1`; any smaller minimum is impossible here.
      have han : a ≤ n - 1 := by
        have hle : a ≤ n := (mem_Icc.mp (hsub ha)).2
        by_contra hcon
        have hlt : n - 1 < a := Nat.not_le.mp hcon
        have ha_eq : a = n := by omega
        have hFeq : F = {n} := by
          ext x
          simp only [subset_iff, mem_Icc, mem_singleton] at *
          grind
        rw [hFeq, card_singleton] at hcard2
        omega
      have ha_eq : a = n - 1 := by
        by_contra hne
        have hle : a ≤ n - 2 := by omega
        have h1 : p * 2 + t * p ≤ q * a := by
          have hmul := he
          rw [hcard2, Nat.mul_add, Nat.mul_comm p t] at hmul
          exact hmul
        have h2 : q * a + 2 * q ≤ q * n := by
          have haq : q * a ≤ q * (n - 2) := Nat.mul_le_mul_left q hle
          have hsum : q * (n - 2) + 2 * q = q * n := by
            rw [Nat.mul_comm 2 q, ← Nat.mul_add]
            congr 1
            omega
          omega
        have hlt' : q * n < t * p + p + 2 * q := by
          have hcomm : n * q = q * n := Nat.mul_comm n q
          omega
        omega
      have hFeq : F = insert (n - 1) {n} := by
        apply Finset.eq_of_subset_of_card_le (s := F) (t := insert (n - 1) {n})
        · intro x hx
          have hxI := mem_Icc.mp (hsub hx)
          rw [ha_eq] at hxI
          simp only [mem_insert, mem_singleton]
          omega
        · rw [card_insert_of_notMem (by simp [show n - 1 ≠ n by omega]), card_singleton,
            hcard2]
      refine Or.inr ⟨hFeq, ?_⟩
      rw [hcard2, ha_eq] at he
      exact he
  · rintro (⟨rfl, hS1⟩ | ⟨rfl, hS2⟩)
    · refine mem_family.mpr ⟨mem_singleton_self n, n, mem_singleton_self n, hn, ?_, ?_⟩
      · simp
      · rw [card_singleton]
        exact hS1
    · have hn2 : 2 ≤ n := by
        by_contra hcon
        have hcon : n < 2 := Nat.not_le.mp hcon
        have h0 : n - 1 = 0 := by omega
        rw [h0, Nat.mul_zero] at hS2
        have hpos2 : 0 < p * (2 + t) := Nat.mul_pos hp (by omega)
        omega
      refine mem_family.mpr ⟨mem_insert_of_mem (mem_singleton_self n), n - 1,
        mem_insert_self _ _, by omega, ?_, ?_⟩
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp only [mem_Icc] <;> omega
      · rw [card_insert_of_notMem (by simp [show n - 1 ≠ n by omega]), card_singleton]
        exact hS2

private theorem card_family_base {p q t n : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hK : t * p + q ≤ n * q) (hlt : n * q - t * p - q < p + q) (hn : 1 ≤ n) :
    (family p q t n).card = schreierPadovan p q (n * q - t * p - q) := by
  have hmul1 : p * (1 + t) = t * p + p := by ring
  have hmul2 : p * (2 + t) = t * p + 2 * p := by ring
  have hS1iff : (p * (1 + t) ≤ q * n) ↔ ¬(n * q - t * p - q + q < p) := by
    have hcomm : q * n = n * q := Nat.mul_comm q n
    rw [hmul1]
    constructor
    · intro hS1 hcon
      omega
    · intro hcon
      omega
  have hS2iff : (p * (2 + t) ≤ q * (n - 1)) ↔ ¬(n * q - t * p - q < 2 * p) := by
    have hcomm : q * (n - 1) = n * q - q := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm q n]
    rw [hmul2, hcomm]
    constructor
    · intro hS2 hcon
      omega
    · intro hcon
      omega
  have hPad : schreierPadovan p q (n * q - t * p - q) =
      (if q ≤ p then (if (n * q - t * p - q) + q < p then 0 else 1)
        else (if n * q - t * p - q < 2 * p then 1 else 2)) := by
    rw [schreierPadovan]
    simp only [show ¬(p + q ≤ n * q - t * p - q ∧ 0 < q) by
      rintro ⟨h1, -⟩
      omega, ↓reduceDIte]
  have hneAB : ({n} : Finset ℕ) ≠ insert (n - 1) {n} := by
    intro hcon
    have : n - 1 ∈ ({n} : Finset ℕ) := hcon ▸ mem_insert_self _ _
    simp only [mem_singleton] at this
    omega
  have hfamily_eq : family p q t n =
      (if p * (1 + t) ≤ q * n then {{n}} else ∅) ∪
        (if p * (2 + t) ≤ q * (n - 1) then {insert (n - 1) {n}} else ∅) := by
    ext F
    rw [mem_family_of_base hp hK hlt hn]
    by_cases h1 : p * (1 + t) ≤ q * n <;> by_cases h2 : p * (2 + t) ≤ q * (n - 1) <;>
      simp [h1, h2]
  have hcard : (family p q t n).card =
      (if p * (1 + t) ≤ q * n then 1 else 0) +
        (if p * (2 + t) ≤ q * (n - 1) then 1 else 0) := by
    rw [hfamily_eq]
    by_cases h1 : p * (1 + t) ≤ q * n <;> by_cases h2 : p * (2 + t) ≤ q * (n - 1) <;>
      simp [h1, h2, hneAB]
  have hcond1 : (n * q - t * p - q + q < p) ↔ ¬(p * (1 + t) ≤ q * n) := by
    have hcomm : q * n = n * q := Nat.mul_comm q n
    rw [hmul1]
    omega
  have hcond2 : (n * q - t * p - q < 2 * p) ↔ ¬(p * (2 + t) ≤ q * (n - 1)) := by
    have hcomm : q * (n - 1) = n * q - q := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm q n]
    rw [hmul2, hcomm]
    omega
  rw [hcard, hPad]
  by_cases hqp : q ≤ p
  · have hS2false : ¬(p * (2 + t) ≤ q * (n - 1)) := by
      rw [hS2iff]
      omega
    by_cases h1 : p * (1 + t) ≤ q * n <;> simp [h1, hcond1, hS2false, hqp]
  · have hS1true : p * (1 + t) ≤ q * n := by
      rw [hmul1]
      have hcomm : q * n = n * q := Nat.mul_comm q n
      omega
    by_cases h2 : p * (2 + t) ≤ q * (n - 1) <;> simp [h2, hS1true, hcond2, hqp]

/-- Translating every element by `p` adds `p * q` to the minimum constraint. -/
private theorem translate {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (m : ℕ) :
    (family p q 0 m).card = (family p q q (m + p)).card := by
  let lift (F : Finset ℕ) := F.image (· + p)
  have hinj : Function.Injective (fun x : ℕ => x + p) := fun _ _ h => Nat.add_right_cancel h
  have hcard (F : Finset ℕ) : (lift F).card = F.card := card_image_of_injective _ hinj
  have hlift (F : Finset ℕ) : lift F ∈ family p q q (m + p) ↔ F ∈ family p q 0 m := by
    simp only [mem_family, hcard, lift, mem_image, Nat.add_zero]
    constructor
    · rintro ⟨⟨x, hx, hxm⟩, a', ⟨a, ha, ha'⟩, hpos, hsub, he⟩
      have hmax : m ∈ F := by rw [hinj hxm] at hx; exact hx
      have hap : a + p = a' := ha'
      have hcardpos : 1 ≤ F.card := card_pos.mpr ⟨m, hmax⟩
      have hposa : 0 < a := by
        have hexp : p * F.card + p * q ≤ q * a + q * p := by
          have h1 : p * (F.card + q) = p * F.card + p * q := by ring
          have h2 : q * a' = q * a + q * p := by rw [← hap]; ring
          omega
        have hqp : p * q = q * p := Nat.mul_comm p q
        have hle : p * F.card ≤ q * a := by omega
        rcases Nat.eq_zero_or_pos a with h0 | hposa
        · subst h0
          simp only [Nat.mul_zero] at hle
          have hposcard : 0 < p * F.card := Nat.mul_pos hp hcardpos
          omega
        · exact hposa
      have hsub' : F ⊆ Icc a m := by
        intro y hy
        obtain ⟨hlo, hhi⟩ := mem_Icc.mp (hsub (mem_image_of_mem (fun x : ℕ => x + p) hy))
        rw [← hap] at hlo
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      refine ⟨hmax, a, ha, hposa, hsub', ?_⟩
      have hexp : p * F.card + p * q ≤ q * a + q * p := by
        have h1 : p * (F.card + q) = p * F.card + p * q := by ring
        have h2 : q * a' = q * a + q * p := by rw [← hap]; ring
        omega
      have hqp : p * q = q * p := Nat.mul_comm p q
      omega
    · rintro ⟨hm, a, ha, hpos, hsub, he⟩
      refine ⟨⟨m, hm, rfl⟩, a + p, ⟨a, ha, rfl⟩, by omega, ?_, ?_⟩
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
        obtain ⟨hlo, hhi⟩ := mem_Icc.mp (hsub hx)
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · have h1 : p * (F.card + q) = p * F.card + p * q := by ring
        have h2 : q * (a + p) = q * a + q * p := by ring
        have hqp : p * q = q * p := Nat.mul_comm p q
        omega
  apply card_nbij lift (fun F hF => (hlift F).mpr hF)
  · intro F _ G _ h
    exact Finset.image_injective hinj h
  · intro G hG
    obtain ⟨-, a, ha, -, hsub, he⟩ := mem_family.mp hG
    have hcardpos : 1 ≤ G.card := card_pos.mpr ⟨a, ha⟩
    have hnonneg : q * p < q * a := by
      have h1 : p * (G.card + q) = p * G.card + p * q := by ring
      have hqp : p * q = q * p := Nat.mul_comm p q
      have hX : p ≤ p * G.card := by
        calc p = p * 1 := by ring
        _ ≤ p * G.card := Nat.mul_le_mul_left p hcardpos
      omega
    have hpa : p < a := (Nat.mul_lt_mul_left hq).mp hnonneg
    let F := G.image (· - p)
    have hFG : lift F = G := by
      ext y
      simp only [lift, F, mem_image, subset_iff, mem_Icc] at *
      grind
    exact ⟨F, (hlift F).mp (hFG ▸ hG), hFG⟩

private theorem card_family_eq_padovan {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∀ m t : ℕ, t ≤ q → t * p + q ≤ (m + 1) * q →
      (family p q t (m + 1)).card = schreierPadovan p q ((m + 1) * q - t * p - q) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t ht hK
    by_cases hlt : (m + 1) * q - t * p - q < p + q
    · exact card_family_base hp hq hK hlt (by omega)
    · have hge : p + q ≤ (m + 1) * q - t * p - q := by omega
      rcases eq_or_lt_of_le ht with htq | hltq
      · obtain rfl : q = t := htq.symm
        -- The offset `q` is handled by translation.
        have hmp : p < m + 1 := by
          by_contra hcon
          have hcon' : m + 1 ≤ p := Nat.not_lt.mp hcon
          have hle : (m + 1) * q ≤ q * p := by
            rw [Nat.mul_comm q p]
            exact Nat.mul_le_mul_right q hcon'
          omega
        have htr := translate hp hq (m + 1 - p)
        rw [show m + 1 - p + p = m + 1 by omega] at htr
        have hs : m + 1 - p = (m - p) + 1 := by omega
        rw [← htr, hs]
        have hih := ih (m - p) (by omega) 0 (Nat.zero_le q) (by
          have hle : q ≤ ((m - p) + 1) * q := by
            calc q = q * 1 := by ring
            _ ≤ q * ((m - p) + 1) := Nat.mul_le_mul_left q (by omega)
            _ = ((m - p) + 1) * q := Nat.mul_comm q ((m - p) + 1)
          omega)
        have hdist : ((m - p) + 1) * q = (m + 1) * q - p * q := by
          rw [← hs, Nat.sub_mul]
        have hidx : ((m - p) + 1) * q - 0 * p - q = (m + 1) * q - q * p - q := by
          rw [hdist]
          simp only [Nat.zero_mul, Nat.sub_zero, Nat.mul_comm p q]
        rw [hih, hidx]
      · have hm0 : m ≠ 0 := by
          rintro rfl
          have hzero : (0 + 1) * q - t * p - q = 0 := by omega
          rw [hzero] at hge
          omega
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, (Nat.sub_add_cancel hm1).symm⟩
        have hmul : (s + 1 + 1) * q = (s + 1) * q + q := by ring
        have hdiff : p * (t + 1) ≤ q * (s + 1) := by
          have hcomm : q * (s + 1) = (s + 1) * q := Nat.mul_comm q (s + 1)
          have hmul2 : p * (t + 1) = t * p + p := by ring
          omega
        rw [difference_step hp hdiff, schreierPadovan_rec hq hge]
        have hK1 : t * p + q ≤ (s + 1) * q := by omega
        have hK2 : (t + 1) * p + q ≤ (s + 1) * q := by
          have hmul2 : (t + 1) * p = t * p + p := by ring
          omega
        have hidx1 : (s + 1) * q - t * p - q = (s + 1 + 1) * q - t * p - q - q := by omega
        have hidx2 : (s + 1) * q - (t + 1) * p - q =
            (s + 1 + 1) * q - t * p - q - p - q := by
          have hmul2 : (t + 1) * p = t * p + p := by ring
          omega
        congr 1
        · rw [← hidx1]
          exact ih s (by omega) t ht hK1
        · rw [← hidx2]
          exact ih s (by omega) (t + 1) (by omega) hK2

/-- Count with an offset in the cardinality constraint, for maximal sets. -/
private def maxFamily (p q t n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter fun F =>
    n ∈ F ∧ ∃ a ∈ F, F ⊆ Icc a n ∧ q * a = p * (F.card + t)

private theorem mem_maxFamily {p q t n : ℕ} {F : Finset ℕ} :
    F ∈ maxFamily p q t n ↔
      n ∈ F ∧ ∃ a ∈ F, 0 < a ∧ F ⊆ Icc a n ∧ q * a = p * (F.card + t) := by
  simp only [maxFamily, mem_filter, mem_powerset, subset_iff, mem_Icc]
  grind

private theorem card_maxFamily_zero {p q : ℕ} (hq : 0 < q) (n : ℕ) :
    (maxFamily p q 0 n).card = maximalSchreierCount p q n := by
  unfold maximalSchreierCount
  congr 1
  ext F
  simp only [mem_maxFamily, mem_filter, mem_powerset, subset_iff, mem_Icc, Nat.add_zero]
  constructor
  · rintro ⟨hn, a, ha, hpos, hb, he⟩
    exact ⟨fun x hx => ⟨hpos.trans_le (hb hx).1, (hb hx).2⟩, hn,
      fun x hx => he ▸ Nat.mul_le_mul_left q (hb hx).1, a, ha, he⟩
  · rintro ⟨hb, hn, hmin, a, ha, he⟩
    refine ⟨hn, a, ha, (hb ha).1, fun x hx => ⟨?_, (hb hx).2⟩, he⟩
    exact (Nat.le_of_mul_le_mul_left (he.symm ▸ hmin x hx) hq)

/-- Moving the maximum past no other element preserves the maximality constraint. -/
private theorem maxReplace_max {p q t n m : ℕ} {F : Finset ℕ}
    (hne : q * n ≠ p * (1 + t)) (hF : F ∈ maxFamily p q t n)
    (hbelow : ∀ x ∈ F, x ≠ n → x < m) :
    insert m (F.erase n) ∈ maxFamily p q t m := by
  obtain ⟨hn, a, ha, hpos, hsub, he⟩ := mem_maxFamily.mp hF
  have han : a ≠ n := by
    rintro rfl
    have hone : F = {a} := by
      ext x
      simp only [subset_iff, mem_Icc, mem_singleton] at *
      grind
    rw [hone, card_singleton] at he
    exact hne he
  have hm : m ∉ F.erase n := fun h =>
    (hbelow m (mem_erase.mp h).2 (mem_erase.mp h).1).false
  have hcard := card_pos.mpr ⟨n, hn⟩
  apply mem_maxFamily.mpr
  refine ⟨mem_insert_self .., a, mem_insert_of_mem (mem_erase.mpr ⟨han, ha⟩), hpos, ?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_Icc.mpr ⟨(hbelow a ha han).le, le_rfl⟩
    · obtain ⟨hxn, hx⟩ := mem_erase.mp hx
      exact mem_Icc.mpr ⟨(mem_Icc.mp (hsub hx)).1, (hbelow x hx hxn).le⟩
  · rwa [card_insert_of_notMem hm, card_erase_of_mem hn, Nat.sub_add_cancel hcard]

private theorem maxDifference_step {p q t m : ℕ}
    (hne1 : q * (m + 1) ≠ p * (1 + t)) (hne2 : q * m ≠ p * (1 + t)) :
    (maxFamily p q t (m + 1)).card =
      (maxFamily p q t m).card + (maxFamily p q (t + 1) m).card := by
  let S := maxFamily p q t (m + 1)
  have withPrev : (S.filter fun F => m ∈ F).card = (maxFamily p q (t + 1) m).card := by
    apply card_nbij' (fun F => F.erase (m + 1)) (insert (m + 1))
    · intro F hF
      obtain ⟨hF, hmF⟩ := mem_filter.mp hF
      obtain ⟨hn, a, ha, hpos, hsub, he⟩ := mem_maxFamily.mp hF
      have han : a ≠ m + 1 := by
        have hle := (mem_Icc.mp (hsub hmF)).1
        omega
      have hcard := card_pos.mpr ⟨m, hmF⟩
      refine mem_maxFamily.mpr ⟨mem_erase.mpr ⟨by omega, hmF⟩, a,
        mem_erase.mpr ⟨han, ha⟩, hpos, ?_, ?_⟩
      · simp only [subset_iff, mem_erase, mem_Icc] at *
        grind
      · rw [card_erase_of_mem hn, show F.card - 1 + (t + 1) = F.card + t by omega]
        exact he
    · intro F hF
      obtain ⟨hmF, a, ha, hpos, hsub, he⟩ := mem_maxFamily.mp hF
      have hnew : m + 1 ∉ F := fun h => (Nat.not_succ_le_self m) (mem_Icc.mp (hsub h)).2
      refine mem_filter.mpr ⟨mem_maxFamily.mpr ⟨mem_insert_self .., a, mem_insert_of_mem ha,
        hpos, ?_, ?_⟩, mem_insert_of_mem hmF⟩
      · simp only [subset_iff, mem_insert, mem_Icc] at *
        grind
      · rwa [card_insert_of_notMem hnew, show F.card + 1 + t = F.card + (t + 1) by omega]
    · intro F hF
      exact insert_erase (mem_maxFamily.mp (mem_filter.mp hF).1).1
    · intro F hF
      obtain ⟨-, a, -, -, hsub, -⟩ := mem_maxFamily.mp hF
      apply erase_insert
      intro h
      have := (mem_Icc.mp (hsub h)).2
      omega
  have withoutPrev : (S.filter fun F => m ∉ F).card = (maxFamily p q t m).card := by
    apply card_nbij' (fun F => insert m (F.erase (m + 1)))
      (fun F => insert (m + 1) (F.erase m))
    · intro F hF
      obtain ⟨hF, hmF⟩ := mem_filter.mp hF
      apply maxReplace_max hne1 hF
      obtain ⟨-, a, -, -, hsub, -⟩ := mem_maxFamily.mp hF
      intro x hx hxn
      have hxm : x ≠ m := fun h => hmF (h ▸ hx)
      have hle := (mem_Icc.mp (hsub hx)).2
      omega
    · intro F hF
      refine mem_filter.mpr ⟨maxReplace_max hne2 hF ?_, by simp⟩
      obtain ⟨-, a, -, -, hsub, -⟩ := mem_maxFamily.mp hF
      intro x hx _
      exact Nat.lt_succ_of_le (mem_Icc.mp (hsub hx)).2
    · intro F hF
      obtain ⟨hF, hmF⟩ := mem_filter.mp hF
      have hnF := (mem_maxFamily.mp hF).1
      ext x
      simp only [mem_insert, mem_erase]
      grind
    · intro F hF
      obtain ⟨hmF, a, -, -, hsub, -⟩ := mem_maxFamily.mp hF
      ext x
      simp only [subset_iff, mem_insert, mem_Icc, mem_erase] at *
      grind
  rw [← withPrev, ← withoutPrev, add_comm (card _), card_filter_add_card_filter_not]

/-- Translating every element by `p` adds `p * q` to the minimum constraint. -/
private theorem maxTranslate {p q : ℕ} (hp : 0 < p) (m : ℕ) :
    (maxFamily p q 0 m).card = (maxFamily p q q (m + p)).card := by
  let lift (F : Finset ℕ) := F.image (· + p)
  have hinj : Function.Injective (fun x : ℕ => x + p) := fun _ _ h => Nat.add_right_cancel h
  have hcard (F : Finset ℕ) : (lift F).card = F.card := card_image_of_injective _ hinj
  have hlift (F : Finset ℕ) : lift F ∈ maxFamily p q q (m + p) ↔ F ∈ maxFamily p q 0 m := by
    simp only [mem_maxFamily, hcard, lift, mem_image, Nat.add_zero]
    constructor
    · rintro ⟨⟨_, hm, heqm⟩, _, ⟨a, ha, rfl⟩, -, hsub, he⟩
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm q p] at he
      have he' : q * a = p * F.card := Nat.add_right_cancel he
      have hpos := Nat.mul_pos hp (card_pos.mpr ⟨a, ha⟩)
      refine ⟨hinj heqm ▸ hm, a, ha, ?_, ?_, he'⟩
      · exact Nat.pos_of_mul_pos_left (he'.symm ▸ hpos)
      · intro x hx
        have := mem_Icc.mp (hsub (mem_image_of_mem (fun x : ℕ => x + p) hx))
        exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rintro ⟨hm, a, ha, hpos, hsub, he⟩
      refine ⟨⟨m, hm, rfl⟩, a + p, ⟨a, ha, rfl⟩, by omega, ?_, ?_⟩
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
        have := mem_Icc.mp (hsub hx)
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · rw [Nat.mul_add, Nat.mul_add, he, Nat.mul_comm q p]
  apply card_nbij lift (fun F hF => (hlift F).mpr hF)
  · intro F _ G _ h
    exact Finset.image_injective hinj h
  · intro G hG
    obtain ⟨-, a, ha, -, hsub, he⟩ := mem_maxFamily.mp hG
    have hnonneg : q * p < q * a := by
      have hpos := Nat.mul_pos hp (card_pos.mpr ⟨a, ha⟩)
      rw [he, Nat.mul_add, Nat.mul_comm q p]
      omega
    have hpa : p < a := Nat.lt_of_mul_lt_mul_left hnonneg
    let F := G.image (· - p)
    have hFG : lift F = G := by
      ext y
      simp only [lift, F, mem_image, subset_iff, mem_Icc] at *
      grind
    exact ⟨F, (hlift F).mp (hFG ▸ hG), hFG⟩

/-- In the initial range the maximal family has at most two members. -/
private theorem mem_maxFamily_of_base {p q t n : ℕ} (hp : 0 < p)
    (hK : t * p + q ≤ n * q) (hlt : n * q - t * p - q < p + q) (hn : 1 ≤ n)
    {F : Finset ℕ} :
    F ∈ maxFamily p q t n ↔
      (F = {n} ∧ q * n = p * (1 + t)) ∨
        (F = insert (n - 1) {n} ∧ q * (n - 1) = p * (2 + t)) := by
  constructor
  · intro hF
    obtain ⟨hnF, a, ha, hpos, hsub, he⟩ := mem_maxFamily.mp hF
    have hsub1n : F ⊆ Icc 1 n := fun x hx => mem_Icc.mpr
      ⟨le_trans hpos (mem_Icc.mp (hsub hx)).1, (mem_Icc.mp (hsub hx)).2⟩
    have hcard_le : F.card ≤ n := by
      have h := card_le_card hsub1n
      rwa [Nat.card_Icc] at h
    have ha_le : a ≤ n + 1 - F.card := by
      have h := card_le_card hsub
      rw [Nat.card_Icc] at h
      have hle : a ≤ n := (mem_Icc.mp (hsub ha)).2
      omega
    have hk2 : F.card ≤ 2 := by
      by_contra hk
      have hk : 2 < F.card := Nat.not_le.mp hk
      have h1 : p * F.card + t * p ≤ q * a := by
        have hmul := he
        rw [Nat.mul_add, Nat.mul_comm p t] at hmul
        omega
      have h2 : q * a + q * F.card ≤ q * n + q := by
        have haq : q * a ≤ q * (n + 1 - F.card) := Nat.mul_le_mul_left q ha_le
        have hsum : q * (n + 1 - F.card) + q * F.card = q * n + q := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (by omega : F.card ≤ n + 1)]
          rw [Nat.mul_succ]
        omega
      have hlt' : q * n < t * p + p + 2 * q := by
        have hcomm : n * q = q * n := Nat.mul_comm n q
        omega
      have hp3 : 3 * p ≤ p * F.card := by
        calc 3 * p = p * 3 := by ring
        _ ≤ p * F.card := Nat.mul_le_mul_left p (by omega)
      have hq3 : 3 * q ≤ q * F.card := by
        calc 3 * q = q * 3 := by ring
        _ ≤ q * F.card := Nat.mul_le_mul_left q (by omega)
      omega
    have hposcard : 1 ≤ F.card := card_pos.mpr ⟨n, hnF⟩
    rcases Nat.lt_or_ge F.card 2 with hk1 | hk2'
    · have hcard1 : F.card = 1 := by omega
      have hFeq : F = {n} := by
        obtain ⟨x, hx⟩ := card_eq_one.mp hcard1
        have hmem : n ∈ ({x} : Finset ℕ) := by rw [← hx]; exact hnF
        have hxeq : x = n := (mem_singleton.mp hmem).symm
        rw [hx, hxeq]
      refine Or.inl ⟨hFeq, ?_⟩
      have ha_eq : a = n := mem_singleton.mp (hFeq ▸ ha)
      rw [hcard1, ha_eq] at he
      exact he
    · have hcard2 : F.card = 2 := by omega
      have han : a ≤ n - 1 := by
        have hle : a ≤ n := (mem_Icc.mp (hsub ha)).2
        by_contra hcon
        have hlt : n - 1 < a := Nat.not_le.mp hcon
        have ha_eq : a = n := by omega
        have hFeq : F = {n} := by
          ext x
          simp only [subset_iff, mem_Icc, mem_singleton] at *
          grind
        rw [hFeq, card_singleton] at hcard2
        omega
      have ha_eq : a = n - 1 := by
        by_contra hne
        have hle : a ≤ n - 2 := by omega
        have h1 : p * 2 + t * p ≤ q * a := by
          have hmul := he
          rw [hcard2, Nat.mul_add, Nat.mul_comm p t] at hmul
          omega
        have h2 : q * a + 2 * q ≤ q * n := by
          have haq : q * a ≤ q * (n - 2) := Nat.mul_le_mul_left q hle
          have hsum : q * (n - 2) + 2 * q = q * n := by
            rw [Nat.mul_comm 2 q, ← Nat.mul_add]
            congr 1
            omega
          omega
        have hlt' : q * n < t * p + p + 2 * q := by
          have hcomm : n * q = q * n := Nat.mul_comm n q
          omega
        omega
      have hFeq : F = insert (n - 1) {n} := by
        apply Finset.eq_of_subset_of_card_le (s := F) (t := insert (n - 1) {n})
        · intro x hx
          have hxI := mem_Icc.mp (hsub hx)
          rw [ha_eq] at hxI
          simp only [mem_insert, mem_singleton]
          omega
        · rw [card_insert_of_notMem (by simp [show n - 1 ≠ n by omega]), card_singleton,
            hcard2]
      refine Or.inr ⟨hFeq, ?_⟩
      rw [hcard2, ha_eq] at he
      exact he
  · rintro (⟨rfl, hS1⟩ | ⟨rfl, hS2⟩)
    · refine mem_maxFamily.mpr ⟨mem_singleton_self n, n, mem_singleton_self n, hn, ?_, ?_⟩
      · simp
      · rw [card_singleton]
        exact hS1
    · have hn2 : 2 ≤ n := by
        by_contra hcon
        have hcon : n < 2 := Nat.not_le.mp hcon
        have h0 : n - 1 = 0 := by omega
        rw [h0, Nat.mul_zero] at hS2
        have hpos2 : 0 < p * (2 + t) := Nat.mul_pos hp (by omega)
        omega
      refine mem_maxFamily.mpr ⟨mem_insert_of_mem (mem_singleton_self n), n - 1,
        mem_insert_self _ _, by omega, ?_, ?_⟩
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp only [mem_Icc] <;> omega
      · rw [card_insert_of_notMem (by simp [show n - 1 ≠ n by omega]), card_singleton]
        exact hS2

private theorem card_maxFamily_base {p q t n : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hK : t * p + q ≤ n * q) (hlt : n * q - t * p - q < p + q) (hn : 1 ≤ n) :
    (maxFamily p q t n).card = maximalSchreierPadovan p q (n * q - t * p - q) := by
  have hmul1 : p * (1 + t) = t * p + p := by ring
  have hmul2 : p * (2 + t) = t * p + 2 * p := by ring
  have hS1iff : (q * n = p * (1 + t)) ↔ (n * q - t * p - q + q = p) := by
    have hcomm : q * n = n * q := Nat.mul_comm q n
    rw [hmul1]
    omega
  have hS2iff : (q * (n - 1) = p * (2 + t)) ↔ (n * q - t * p - q = 2 * p) := by
    have hcomm : q * (n - 1) = n * q - q := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm q n]
    rw [hmul2, hcomm]
    omega
  have hPad : maximalSchreierPadovan p q (n * q - t * p - q) =
      (if q ≤ p then (if (n * q - t * p - q) + q = p then 1 else 0)
        else (if n * q - t * p - q = 2 * p then 1 else 0)) := by
    rw [maximalSchreierPadovan]
    simp only [show ¬(p + q ≤ n * q - t * p - q ∧ 0 < q) by
      rintro ⟨h1, -⟩
      omega, ↓reduceDIte]
  have hneAB : ({n} : Finset ℕ) ≠ insert (n - 1) {n} := by
    intro hcon
    have : n - 1 ∈ ({n} : Finset ℕ) := hcon ▸ mem_insert_self _ _
    simp only [mem_singleton] at this
    omega
  have hfamily_eq : maxFamily p q t n =
      (if q * n = p * (1 + t) then {{n}} else ∅) ∪
        (if q * (n - 1) = p * (2 + t) then {insert (n - 1) {n}} else ∅) := by
    ext F
    rw [mem_maxFamily_of_base hp hK hlt hn]
    by_cases h1 : q * n = p * (1 + t) <;> by_cases h2 : q * (n - 1) = p * (2 + t) <;>
      simp [h1, h2]
  have hcard : (maxFamily p q t n).card =
      (if q * n = p * (1 + t) then 1 else 0) +
        (if q * (n - 1) = p * (2 + t) then 1 else 0) := by
    rw [hfamily_eq]
    by_cases h1 : q * n = p * (1 + t) <;> by_cases h2 : q * (n - 1) = p * (2 + t) <;>
      simp [h1, h2, hneAB]
  rw [hcard, hPad]
  have hcond1 : (n * q - t * p - q + q = p) ↔ (q * n = p * (1 + t)) := hS1iff.symm
  have hcond2 : (n * q - t * p - q = 2 * p) ↔ (q * (n - 1) = p * (2 + t)) := hS2iff.symm
  by_cases hqp : q ≤ p
  · have hS2false : ¬(q * (n - 1) = p * (2 + t)) := by
      rw [hS2iff]
      omega
    by_cases h1 : q * n = p * (1 + t) <;> simp [h1, hcond1, hS2false, hqp]
  · have hS1false : ¬(q * n = p * (1 + t)) := by
      rw [hS1iff]
      omega
    by_cases h2 : q * (n - 1) = p * (2 + t) <;> simp [h2, hS1false, hcond2, hqp]

private theorem card_maxFamily_eq_padovan {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∀ m t : ℕ, t ≤ q → t * p + q ≤ (m + 1) * q →
      (maxFamily p q t (m + 1)).card =
        maximalSchreierPadovan p q ((m + 1) * q - t * p - q) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t ht hK
    by_cases hlt : (m + 1) * q - t * p - q < p + q
    · exact card_maxFamily_base hp hq hK hlt (by omega)
    · have hge : p + q ≤ (m + 1) * q - t * p - q := by omega
      rcases eq_or_lt_of_le ht with htq | hltq
      · obtain rfl : q = t := htq.symm
        -- The offset `q` is handled by translation.
        have hmp : p < m + 1 := by
          by_contra hcon
          have hcon' : m + 1 ≤ p := Nat.not_lt.mp hcon
          have hle : (m + 1) * q ≤ q * p := by
            rw [Nat.mul_comm q p]
            exact Nat.mul_le_mul_right q hcon'
          omega
        have htr := maxTranslate (q := q) hp (m + 1 - p)
        rw [show m + 1 - p + p = m + 1 by omega] at htr
        have hs : m + 1 - p = (m - p) + 1 := by omega
        rw [← htr, hs]
        have hih := ih (m - p) (by omega) 0 (Nat.zero_le q) (by
          have hle : q ≤ ((m - p) + 1) * q := by
            calc q = q * 1 := by ring
            _ ≤ q * ((m - p) + 1) := Nat.mul_le_mul_left q (by omega)
            _ = ((m - p) + 1) * q := Nat.mul_comm q ((m - p) + 1)
          omega)
        have hdist : ((m - p) + 1) * q = (m + 1) * q - p * q := by
          rw [← hs, Nat.sub_mul]
        have hidx : ((m - p) + 1) * q - 0 * p - q = (m + 1) * q - q * p - q := by
          rw [hdist]
          simp only [Nat.zero_mul, Nat.sub_zero, Nat.mul_comm p q]
        rw [hih, hidx]
      · have hm0 : m ≠ 0 := by
          rintro rfl
          have hzero : (0 + 1) * q - t * p - q = 0 := by omega
          rw [hzero] at hge
          omega
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, (Nat.sub_add_cancel hm1).symm⟩
        have hmul : (s + 1 + 1) * q = (s + 1) * q + q := by ring
        have hne1 : q * (s + 1 + 1) ≠ p * (1 + t) := by
          intro hEq
          have hmul1 : p * (1 + t) = t * p + p := by ring
          have hcomm : q * (s + 1 + 1) = (s + 1 + 1) * q := Nat.mul_comm q (s + 1 + 1)
          omega
        have hne2 : q * (s + 1) ≠ p * (1 + t) := by
          intro hEq
          have hmul1 : p * (1 + t) = t * p + p := by ring
          have hcomm : q * (s + 1) = (s + 1) * q := Nat.mul_comm q (s + 1)
          omega
        rw [maxDifference_step hne1 hne2, maximalSchreierPadovan_rec hq hge]
        have hK1 : t * p + q ≤ (s + 1) * q := by omega
        have hK2 : (t + 1) * p + q ≤ (s + 1) * q := by
          have hmul2 : (t + 1) * p = t * p + p := by ring
          omega
        have hidx1 : (s + 1) * q - t * p - q = (s + 1 + 1) * q - t * p - q - q := by omega
        have hidx2 : (s + 1) * q - (t + 1) * p - q =
            (s + 1 + 1) * q - t * p - q - p - q := by
          have hmul2 : (t + 1) * p = t * p + p := by ring
          omega
        congr 1
        · rw [← hidx1]
          exact ih s (by omega) t ht hK1
        · rw [← hidx2]
          exact ih s (by omega) (t + 1) (by omega) hK2

end MetaMathlibExt.schreierCount_eq_schreierPadovan

namespace MetaMathlibExt

/-- **Schreier counts as Padovan-like sequences.** Write $a_{p,q,k}$ and $a^{(m)}_{p,q,k}$ for the
Padovan-like sequences for Schreier sets and for maximal Schreier sets. For positive integers $p$,
$q$ and $n$, the number $|S^{p/q}_n|$ of $(p, q)$-Schreier sets with maximum $n$ equals
$a_{p,q,(n-1)q}$, and the number $|M^{p/q}_n|$ of maximal $(p, q)$-Schreier sets with maximum $n$
equals $a^{(m)}_{p,q,(n-1)q}$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Theorem 1
(`jis-2026-26.2.2-thm-1`). -/
public theorem schreierCount_eq_schreierPadovan {p q n : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hn : 1 ≤ n) :
    schreierCount p q n = schreierPadovan p q ((n - 1) * q) ∧
      maximalSchreierCount p q n = maximalSchreierPadovan p q ((n - 1) * q) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hp' : 0 < p := by omega
  have hq' : 0 < q := by omega
  have hex0 : 0 * p + q ≤ (m + 1) * q := by
    have hle : q ≤ (m + 1) * q := by
      calc q = q * 1 := by ring
      _ ≤ q * (m + 1) := Nat.mul_le_mul_left q (by omega)
      _ = (m + 1) * q := Nat.mul_comm q (m + 1)
    omega
  have hidx : (m + 1 - 1) * q = (m + 1) * q - 0 * p - q := by
    rw [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
    omega
  refine ⟨?_, ?_⟩
  · have h := schreierCount_eq_schreierPadovan.card_family_eq_padovan hp' hq' m 0
      (Nat.zero_le q) hex0
    rw [schreierCount_eq_schreierPadovan.card_family_zero] at h
    rw [hidx]
    exact h
  · have h := schreierCount_eq_schreierPadovan.card_maxFamily_eq_padovan hp' hq' m 0
      (Nat.zero_le q) hex0
    rw [schreierCount_eq_schreierPadovan.card_maxFamily_zero hq'] at h
    rw [hidx]
    exact h

end MetaMathlibExt
