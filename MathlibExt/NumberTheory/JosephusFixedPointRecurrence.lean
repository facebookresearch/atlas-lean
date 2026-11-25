/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.JosephusThreeHighExtremalRecurrences

/-!
# A recurrence formula for the fixed points of the Josephus function `J₃`

`josephusThree_fixedPoint_recurrence` counts the pure high extremal points between consecutive
fixed points and gives a formula for the next fixed point.
-/

namespace MetaMathlibExt

namespace josephusThree_fixedPoint_recurrence

-- Two indices past the end of a finite enumeration would violate the survivor recurrence.
private theorem infinite_highExtremal : (Set.ofPred IsJosephusThreeHighExtremal).Infinite := by
  intro h
  let i := h.toFinset.card
  have h₀ : Nat.nth IsJosephusThreeHighExtremal i = 0 := Nat.nth_of_card_le h le_rfl
  have h₁ : Nat.nth IsJosephusThreeHighExtremal (i + 1) = 0 :=
    Nat.nth_of_card_le h (Nat.le_succ _)
  have hrec := josephusThree_highExtremal_recurrences i
  dsimp only at hrec
  rw [h₀, h₁] at hrec
  simpa [josephus] using hrec.2.1

private def stepWeight (a : ℕ) : ℕ := 3 * a + 2 + (a - josephus 3 a)

-- Adding the size and gap recurrences eliminates their common parity term.
private theorem exists_next_highExtremal {a : ℕ} (ha : IsJosephusThreeHighExtremal a) :
    ∃ b, IsLeast {n | a < n ∧ IsJosephusThreeHighExtremal n} b ∧
      2 * b + 1 + (b - josephus 3 b) = stepWeight a := by
  obtain ⟨i, hi⟩ := Nat.subset_range_nth (p := IsJosephusThreeHighExtremal) ha
  let b := Nat.nth IsJosephusThreeHighExtremal (i + 1)
  have hb := Nat.nth_mem_of_infinite infinite_highExtremal (i + 1)
  refine ⟨b, ⟨⟨?_, hb⟩, ?_⟩, ?_⟩
  · rw [← hi]
    exact Nat.nth_strictMono infinite_highExtremal (Nat.lt_succ_self i)
  · intro n hn
    exact (Nat.nth_add_one_le_iff infinite_highExtremal hn.2).2 (hi.symm ▸ hn.1)
  · have hrec := josephusThree_highExtremal_recurrences i
    dsimp only at hrec
    rw [hi] at hrec
    have hsum : 2 * (b : ℤ) + 1 + ((b : ℤ) - josephus 3 b) =
        3 * (a : ℤ) + 2 + ((a : ℤ) - josephus 3 a) := by
      have hsize := hrec.1
      have hgap := hrec.2.2.1
      change 2 * (b : ℤ) = _ at hsize
      change (b : ℤ) - josephus 3 b = _ at hgap
      omega
    have haJ := (josephus_range 3 a (by decide) ha.1).2
    have hbJ := (josephus_range 3 b (by decide) hb.1).2
    rw [← Int.natCast_sub haJ, ← Int.natCast_sub hbJ] at hsum
    unfold stepWeight
    exact_mod_cast hsum

-- A pure successor consumes one factor of two, and a fixed successor ends the count.
private theorem exists_next_fixed {a : ℕ} (ha : IsJosephusThreeHighExtremal a) :
    let m := multiplicity 2 (stepWeight a)
    ∃ b, IsLeast {n | a < n ∧ IsJosephusThreeFixedPoint n} b ∧
      ((Finset.Ioo a b).filter (fun n => josephus 3 n + 1 = n)).card = m ∧
      2 ^ m * (2 * b + 1) = 3 ^ m * stepWeight a := by
  dsimp only
  generalize hm : multiplicity 2 (stepWeight a) = m
  induction m using Nat.strong_induction_on generalizing a with
  | ind m ih =>
    obtain ⟨c, hc, hstep⟩ := exists_next_highExtremal ha
    have hac := hc.1.1
    have hle (n : ℕ) (han : a < n) (hn : josephus 3 n = n ∨ josephus 3 n + 1 = n) :
        c ≤ n :=
      hc.2 ⟨han, by omega, hn⟩
    rcases hc.1.2.2 with hfix | hpure
    · have hweight : stepWeight a = 2 * c + 1 := by
        simpa [hfix] using hstep.symm
      have hm₀ : m = 0 := by
        rw [← hm, hweight]
        exact multiplicity_eq_zero_of_not_dvd (by omega)
      rw [hm₀]
      refine ⟨c, ⟨⟨hac, hc.1.2.1, hfix⟩, fun n hn => hle n hn.1 (Or.inl hn.2.2)⟩, ?_, ?_⟩
      · apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Ioo] at hn
        exact hn.1.2.not_ge (hle n hn.1.1 (Or.inr hn.2))
      · simp [hweight]
    · have hweighta : stepWeight a = 2 * (c + 1) := by omega
      have hweightc : stepWeight c = 3 * (c + 1) := by unfold stepWeight; omega
      have hval : multiplicity 2 (stepWeight a) =
          multiplicity 2 (stepWeight c) + 1 := by
        let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hthree : multiplicity 2 3 = 0 := multiplicity_eq_zero_of_not_dvd (by decide)
        rw [hweighta, hweightc, Nat.multiplicity_mul (by decide : 2 ≠ 0) (Nat.succ_ne_zero c),
          Nat.multiplicity_mul (by decide : 3 ≠ 0) (Nat.succ_ne_zero c),
          Nat.Prime.multiplicity_self, hthree, zero_add, add_comm]
      let k := multiplicity 2 (stepWeight c)
      have hmk : m = k + 1 := hm.symm.trans hval
      obtain ⟨b, hb, hcard, hrec⟩ := ih k (hmk ▸ Nat.lt_succ_self k) hc.1.2 rfl
      refine ⟨b, ⟨⟨hac.trans hb.1.1, hb.1.2⟩, ?_⟩, ?_, ?_⟩
      · intro n hn
        have hcn : c < n := (hle n hn.1 (Or.inl hn.2.2)).lt_of_ne (by
          intro e
          have hnfix := hn.2.2
          subst n
          omega)
        exact hb.2 ⟨hcn, hn.2⟩
      · have hfilter :
            ((Finset.Ioo a b).filter (fun n => josephus 3 n + 1 = n)) =
              insert c ((Finset.Ioo c b).filter (fun n => josephus 3 n + 1 = n)) := by
          ext n
          simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Ioo]
          constructor
          · rintro ⟨⟨han, hnb⟩, hn⟩
            rcases (hle n han (Or.inr hn)).eq_or_lt with h | h
            · exact Or.inl h.symm
            · exact Or.inr ⟨⟨h, hnb⟩, hn⟩
          · rintro (rfl | ⟨⟨hcn, hnb⟩, hn⟩)
            · exact ⟨⟨hac, hb.1.1⟩, hpure⟩
            · exact ⟨⟨hac.trans hcn, hnb⟩, hn⟩
        rw [hfilter, Finset.card_insert_of_notMem (by simp), hcard, hmk]
      · rw [hmk]
        calc
          2 ^ (k + 1) * (2 * b + 1) = 2 * (2 ^ k * (2 * b + 1)) := by
            rw [pow_succ', mul_assoc]
          _ = 2 * (3 ^ k * stepWeight c) := by rw [hrec]
          _ = 3 ^ k * (2 * stepWeight c) := by ac_rfl
          _ = 3 ^ k * (3 * stepWeight a) := by rw [hweighta, hweightc]; ac_rfl
          _ = 3 ^ (k + 1) * stepWeight a := by rw [pow_succ, mul_assoc]

private theorem infinite_fixedPoint : (Set.ofPred IsJosephusThreeFixedPoint).Infinite := by
  intro h
  obtain ⟨a, ha, hmax⟩ := h.exists_maximal
    ⟨1, (show IsJosephusThreeFixedPoint 1 from ⟨le_rfl, josephus_one 3 (by decide)⟩)⟩
  obtain ⟨b, hb, _, _⟩ := exists_next_fixed ⟨ha.1, Or.inl ha.2⟩
  exact hb.1.1.not_ge (hmax hb.1.2 hb.1.1.le)

end josephusThree_fixedPoint_recurrence

open josephusThree_fixedPoint_recurrence in
/-- **Recurrence for consecutive fixed points of $J_3$.** For every natural number $\ell$, let $a$
and $b$ be the $(\ell+1)$-th and $(\ell+2)$-th smallest fixed points of the Josephus function
$J_3$, and let $m = \nu_2(3a + 2)$ be the $2$-adic valuation of $3a + 2$. Then exactly $m$
natural numbers $n$ with $a < n < b$ satisfy $J_3(n) = n - 1$ (the pure high extremal points
between $a$ and $b$), and $2^{m+1} b + 2^m = 3^m (3a + 2)$, that is,
$b = (3^m (3a + 2) - 2^m) / 2^{m+1}$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Theorem 2
(`integers-2024-A115-thm-2`). -/
public theorem josephusThree_fixedPoint_recurrence (ℓ : ℕ) :
    let a := Nat.nth IsJosephusThreeFixedPoint ℓ
    let b := Nat.nth IsJosephusThreeFixedPoint (ℓ + 1)
    ((Finset.Ioo a b).filter (fun n => josephus 3 n + 1 = n)).card =
        padicValNat 2 (3 * a + 2) ∧
      2 ^ (padicValNat 2 (3 * a + 2) + 1) * b + 2 ^ padicValNat 2 (3 * a + 2) =
        3 ^ padicValNat 2 (3 * a + 2) * (3 * a + 2) := by
  intro a b
  have ha : IsJosephusThreeFixedPoint a := Nat.nth_mem_of_infinite infinite_fixedPoint ℓ
  have hb : IsJosephusThreeFixedPoint b := Nat.nth_mem_of_infinite infinite_fixedPoint (ℓ + 1)
  obtain ⟨c, hc, hcard, hrec⟩ := exists_next_fixed ⟨ha.1, Or.inl ha.2⟩
  have hbc : b = c := le_antisymm
    ((Nat.nth_add_one_le_iff infinite_fixedPoint hc.1.2).2 hc.1.1)
    (hc.2 ⟨Nat.nth_strictMono infinite_fixedPoint (Nat.lt_succ_self ℓ), hb⟩)
  subst c
  simp only [stepWeight, ha.2, Nat.sub_self, add_zero] at hcard hrec
  simp only [Nat.padicValNat_def]
  refine ⟨hcard, ?_⟩
  simpa only [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← pow_succ] using hrec

end MetaMathlibExt
