/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.NumberTheory.DivRunCountFour
public import MathlibExt.NumberTheory.DivisibilityRuns
public import MathlibExt.NumberTheory.GeneralizedTribonacciBasis
public import MathlibExt.NumberTheory.DivisibilityRunsGibonacciNumberEqFib

/-!
# Exact formula for the length-three run count

The length-three run count `divRunCount B 3` equals a divisor sum over the pairs
$(x, y)$ with $x$, $y$ and $x + y$ all nonzero, and also equals the symmetrized
form with doubled sums over positive $m$ and $n$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 6
(`integers-2026-A122-prop-6`).
-/

@[expose] public section

namespace MetaMathlibExt

namespace divRunCount_three

private theorem mem_Icc_iff_natAbs_le (a : ℤ) (B : ℕ) :
    a ∈ Finset.Icc (-(B : ℤ)) B ↔ a.natAbs ≤ B := by
  simp only [Finset.mem_Icc]
  omega

private theorem card_Icc_neg_self (M : ℕ) :
    (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
  rw [Int.card_Icc]
  have h : (M : ℤ) + 1 - -(M : ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h, Int.toNat_natCast]

private theorem card_filter_dvd_Icc (B : ℕ) (x : ℤ) (hx : x ≠ 0) :
    ((Finset.Icc (-(B : ℤ)) B).filter (fun a => x ∣ a)).card =
      2 * (B / x.natAbs) + 1 := by
  have hbij : ((Finset.Icc (-(B : ℤ)) B).filter (fun a => x ∣ a)).card =
      (Finset.Icc (-(((B / x.natAbs : ℕ)) : ℤ)) ((B / x.natAbs : ℕ))).card := by
    apply Finset.card_bij' (fun a _ => a / x) (fun k _ => x * k)
    · intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨haC, hdvd⟩ := ha
      have hb : a.natAbs ≤ B := (mem_Icc_iff_natAbs_le a B).mp haC
      exact (mem_Icc_iff_natAbs_le (a / x) (B / x.natAbs)).mpr
        (by rw [Int.natAbs_ediv_of_dvd hdvd]; exact Nat.div_le_div_right hb)
    · intro k hk
      rw [Finset.mem_filter]
      have hkC : k ∈ Finset.Icc (-(((B / x.natAbs : ℕ)) : ℤ)) ((B / x.natAbs : ℕ)) := hk
      have hc : k.natAbs ≤ B / x.natAbs :=
        (mem_Icc_iff_natAbs_le k (B / x.natAbs)).mp hkC
      refine ⟨(mem_Icc_iff_natAbs_le (x * k) B).mpr (by
        rw [Int.natAbs_mul]
        calc x.natAbs * k.natAbs ≤ x.natAbs * (B / x.natAbs) :=
              Nat.mul_le_mul le_rfl hc
          _ = B / x.natAbs * x.natAbs := by rw [mul_comm]
          _ ≤ B := Nat.div_mul_le_self B x.natAbs), dvd_mul_right x k⟩
    · intro a ha
      rw [Finset.mem_filter] at ha
      exact Int.mul_ediv_cancel' ha.2
    · intro k _
      exact Int.mul_ediv_cancel_left k hx
  rw [hbij, card_Icc_neg_self]

private theorem card_filter_triple (B : ℕ) (x y : ℤ) :
    ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B).filter
        fun t => x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2).card =
      (((Finset.Icc (-(B : ℤ)) B).filter (fun a => x ∣ a)).card *
        (((Finset.Icc (-(B : ℤ)) B).filter (fun b => y ∣ b)).card *
          ((Finset.Icc (-(B : ℤ)) B).filter (fun c => x + y ∣ c)).card)) := by
  have h : (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
      Finset.Icc (-(B : ℤ)) B).filter
        (fun t => x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2) =
      (Finset.Icc (-(B : ℤ)) B).filter (fun a => x ∣ a) ×ˢ
        ((Finset.Icc (-(B : ℤ)) B).filter (fun b => y ∣ b) ×ˢ
          (Finset.Icc (-(B : ℤ)) B).filter (fun c => x + y ∣ c)) := by
    ext t
    obtain ⟨a, b, c⟩ := t
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [h, Finset.card_product, Finset.card_product]

private theorem sum_triple (B : ℕ) (x y : ℤ) :
    (∑ t ∈ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B,
      if (x, y) ≠ (0, 0) ∧ (t.1, t.2.1, t.2.2) ≠ (0, 0, 0) ∧
          IsDivRunUpTo x y t.1 t.2.1 t.2.2 3 then (1 : ℤ) else 0) =
    if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
      ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
        (2 * (B / (x + y).natAbs) + 1) - 1 : ℕ) : ℤ))
    else 0 := by
  by_cases hc : x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0
  · obtain ⟨hx, hy, hxy⟩ := hc
    have hc' : x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 := ⟨hx, hy, hxy⟩
    rw [ite_eq_left hc']
    have hmem : (0, 0, 0) ∈ (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B).filter fun t =>
          x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2 := by
      simp [dvd_zero]
    have hfilter : (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B).filter (fun t =>
          (x, y) ≠ (0, 0) ∧ (t.1, t.2.1, t.2.2) ≠ (0, 0, 0) ∧
            IsDivRunUpTo x y t.1 t.2.1 t.2.2 3) =
        ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
          Finset.Icc (-(B : ℤ)) B).filter fun t =>
            x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2).erase (0, 0, 0) := by
      ext t
      obtain ⟨a, b, c⟩ := t
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨ht, -, htne, hrun⟩
        obtain ⟨⟨-, hqa⟩, ⟨-, hqb⟩, -, hqc⟩ :=
          (isDivRunUpTo_small x y a b c).2.2.mp hrun
        exact ⟨htne, ht, hqa, hqb, hqc⟩
      · rintro ⟨htne, ht, hq⟩
        exact ⟨ht, fun h => hx (Prod.ext_iff.mp h).1, htne,
          (isDivRunUpTo_small x y a b c).2.2.mpr
            ⟨⟨hx, hq.1⟩, ⟨hy, hq.2.1⟩, hxy, hq.2.2⟩⟩
    rw [← Finset.natCast_card_filter, hfilter, Finset.card_erase_of_mem hmem]
    have hpos : 1 ≤ ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B).filter fun t =>
          x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2).card :=
      Finset.card_pos.mpr ⟨(0, 0, 0), hmem⟩
    rw [Nat.cast_sub hpos]
    simp only [Nat.cast_one]
    rw [card_filter_triple, card_filter_dvd_Icc B x hx, card_filter_dvd_Icc B y hy,
      card_filter_dvd_Icc B (x + y) hxy, ← mul_assoc]
    have hP : 1 ≤ (2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
        (2 * (B / (x + y).natAbs) + 1) := by
      have hP0 : 0 < (2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) := by positivity
      omega
    rw [Nat.cast_sub hP, Nat.cast_one]
  · rw [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro t _
    rw [ite_eq_right]
    rintro ⟨-, -, hrun⟩
    obtain ⟨⟨hxa, -⟩, ⟨hyb, -⟩, hxc, -⟩ :=
      (isDivRunUpTo_small x y t.1 t.2.1 t.2.2).2.2.mp hrun
    exact hc ⟨hxa, hyb, hxc⟩

private theorem card_filter_ne (B : ℕ) :
    ((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).card = 2 * B := by
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(B : ℤ)) B := by
    simp only [Finset.mem_Icc]
    omega
  have heq : (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0) =
      (Finset.Icc (-(B : ℤ)) B).erase 0 := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [heq, Finset.card_erase_of_mem h0, card_Icc_neg_self]
  omega

private theorem neg_mem_Icc (B : ℕ) (x : ℤ)
    (hx : x ∈ Finset.Icc (-(B : ℤ)) B) : -x ∈ Finset.Icc (-(B : ℤ)) B := by
  simp only [Finset.mem_Icc] at hx ⊢
  omega

private theorem card_diag (B : ℕ) :
    (((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0) ×ˢ
      (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).filter
      fun p => p.1 + p.2 = 0).card = 2 * B := by
  have hbij : (((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0) ×ˢ
      (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).filter
      fun p => p.1 + p.2 = 0).card =
      ((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).card := by
    refine Finset.card_bij' (fun p _ => p.1) (fun x _ => (x, -x)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpC, -⟩ := hp
      rw [Finset.mem_product] at hpC
      exact hpC.1
    · intro x hx
      have hx0 : x ∈ (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0) := hx
      rw [Finset.mem_filter] at hx0
      obtain ⟨hxC, hxne⟩ := hx0
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · constructor
        · exact ⟨hxC, hxne⟩
        · exact ⟨neg_mem_Icc B x hxC, fun h => hxne (by omega)⟩
      · omega
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpC, hsum⟩ := hp
      obtain ⟨x, y⟩ := p
      simp only at hsum ⊢
      have hy : y = -x := by omega
      rw [hy]
    · intro x _
      rfl
  rw [hbij, card_filter_ne]

private theorem card_valid (B : ℕ) :
    ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B).filter
      fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0).card = 4 * B ^ 2 - 2 * B := by
  have hS0 : ((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).card = 2 * B :=
    card_filter_ne B
  have hP0 : ((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0) ×ˢ
      (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).card = 4 * B ^ 2 := by
    rw [Finset.card_product, hS0]
    ring
  have hVeq : (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B).filter
      (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0) =
      ((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0) ×ˢ
        (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).filter
        fun p => p.1 + p.2 ≠ 0 := by
    ext p
    obtain ⟨x, y⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  have hsplit := ((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0) ×ˢ
      (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).card_filter_add_card_filter_not
    (fun p : ℤ × ℤ => p.1 + p.2 ≠ 0)
  have hD : (((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0) ×ˢ
      (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).filter
      fun p => ¬ p.1 + p.2 ≠ 0).card = 2 * B := by
    have heq : ((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0) ×ˢ
        (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).filter
        (fun p : ℤ × ℤ => ¬ p.1 + p.2 ≠ 0) =
        ((Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0) ×ˢ
          (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)).filter
        fun p => p.1 + p.2 = 0 := by
      apply Finset.filter_congr
      intro p _
      simp only [not_ne_iff]
    rw [heq, card_diag]
  rw [hVeq]
  omega

private theorem sum_Icc_split (B : ℕ) (f : ℤ → ℤ) (hf0 : f 0 = 0) :
    ∑ x ∈ Finset.Icc (-(B : ℤ)) B, f x =
      ∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), f x + ∑ x ∈ Finset.Icc (1 : ℤ) B, f x := by
  have hsub : Finset.Icc (-(B : ℤ)) (-1) ∪ Finset.Icc (1 : ℤ) B ⊆
      Finset.Icc (-(B : ℤ)) B := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_Icc] at hx ⊢
    omega
  have hvan : ∀ x ∈ Finset.Icc (-(B : ℤ)) B,
      x ∉ Finset.Icc (-(B : ℤ)) (-1) ∪ Finset.Icc (1 : ℤ) B → f x = 0 := by
    intro x hx hxout
    simp only [Finset.mem_union, Finset.mem_Icc] at hx hxout
    have hx0 : x = 0 := by omega
    rw [hx0, hf0]
  have hdisj : Disjoint (Finset.Icc (-(B : ℤ)) (-1)) (Finset.Icc (1 : ℤ) B) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1 hx2
    omega
  have h := Finset.sum_subset hsub hvan
  rw [Finset.sum_union hdisj] at h
  exact h.symm

private theorem Pos_eq_image (B : ℕ) :
    Finset.Icc (1 : ℤ) B = (Finset.Icc 1 B).image (fun m : ℕ => (m : ℤ)) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_image]
  constructor
  · intro hx
    have hx0 : 0 ≤ x := by omega
    have heq : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hx0
    refine ⟨x.natAbs, ⟨?_, ?_⟩, heq⟩
    · have h1 : (1 : ℤ) ≤ (x.natAbs : ℤ) := by rw [heq]; exact hx.1
      exact_mod_cast h1
    · have h2 : (x.natAbs : ℤ) ≤ (B : ℤ) := by rw [heq]; exact hx.2
      exact_mod_cast h2
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
    constructor
    · exact_mod_cast hm1
    · exact_mod_cast hm2

private theorem Neg_eq_image (B : ℕ) :
    Finset.Icc (-(B : ℤ)) (-1) =
      (Finset.Icc 1 B).image (fun m : ℕ => (-(m : ℤ))) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_image]
  constructor
  · intro hx
    have hx0 : x ≤ 0 := by omega
    have heq : (x.natAbs : ℤ) = -x := Int.ofNat_natAbs_of_nonpos hx0
    have hxeq : x = -((x.natAbs : ℕ) : ℤ) := Int.eq_neg_natAbs_of_nonpos hx0
    refine ⟨x.natAbs, ⟨?_, ?_⟩, hxeq.symm⟩
    · have h1 : (1 : ℤ) ≤ (x.natAbs : ℤ) := by rw [heq]; omega
      exact_mod_cast h1
    · have h2 : (x.natAbs : ℤ) ≤ (B : ℤ) := by rw [heq]; omega
      exact_mod_cast h2
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
    have hm1' : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm1
    have hm2' : (m : ℤ) ≤ (B : ℤ) := by exact_mod_cast hm2
    constructor
    · omega
    · omega

private theorem sum_Pos (B : ℕ) (h : ℤ → ℤ) :
    ∑ x ∈ Finset.Icc (1 : ℤ) B, h x = ∑ m ∈ Finset.Icc 1 B, h (m : ℤ) := by
  rw [Pos_eq_image]
  apply Finset.sum_image
  intro m _ n _ hmn
  simp only at hmn
  exact Nat.cast_inj.mp hmn

private theorem sum_Neg (B : ℕ) (h : ℤ → ℤ) :
    ∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), h x = ∑ m ∈ Finset.Icc 1 B, h (-(m : ℤ)) := by
  rw [Neg_eq_image]
  apply Finset.sum_image
  intro m _ n _ hmn
  simp only at hmn
  have h2 : (m : ℤ) = (n : ℤ) := neg_inj.mp hmn
  exact Nat.cast_inj.mp h2

private theorem natAbs_add_pos (m n : ℕ) : ((m : ℤ) + (n : ℤ)).natAbs = m + n := by
  rw [← Nat.cast_add, Int.natAbs_natCast]

private theorem natAbs_add_neg (m n : ℕ) :
    ((-(m : ℤ)) + (-(n : ℤ))).natAbs = m + n := by
  have h : (-(m : ℤ)) + (-(n : ℤ)) = -(((m + n : ℕ)) : ℤ) := by
    push_cast
    ring
  rw [h, Int.natAbs_neg, Int.natAbs_natCast]

private theorem natAbs_sub_eq (m n : ℕ) (h : n ≤ m) :
    ((m : ℤ) - (n : ℤ)).natAbs = m - n := by
  have hcast : (((m - n : ℕ)) : ℤ) = (m : ℤ) - (n : ℤ) := Nat.cast_sub h
  rw [← hcast, Int.natAbs_natCast]

private theorem natAbs_sub_eq' (m n : ℕ) (h : m ≤ n) :
    ((m : ℤ) - (n : ℤ)).natAbs = n - m := by
  have hcast : (((n - m : ℕ)) : ℤ) = (n : ℤ) - (m : ℤ) := Nat.cast_sub h
  have hneg : (m : ℤ) - (n : ℤ) = -(((n - m : ℕ)) : ℤ) := by
    rw [hcast]
    ring
  rw [hneg, Int.natAbs_neg, Int.natAbs_natCast]

private theorem sum_PP (B : ℕ) :
    ∑ x ∈ Finset.Icc (1 : ℤ) B, ∑ y ∈ Finset.Icc (1 : ℤ) B,
      (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
        ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
       else 0)
    = (((∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
        ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m + n)) + 1) : ℕ)) : ℕ) : ℤ) := by
  have hLHS : (∑ x ∈ Finset.Icc (1 : ℤ) B, ∑ y ∈ Finset.Icc (1 : ℤ) B,
      (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
        ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
       else 0))
      = ∑ x ∈ Finset.Icc (1 : ℤ) B, ∑ y ∈ Finset.Icc (1 : ℤ) B,
        ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.mem_Icc] at hx hy
    have hx0 : x ≠ 0 := by omega
    have hy0 : y ≠ 0 := by omega
    have hxy : x + y ≠ 0 := by omega
    rw [ite_eq_left ⟨hx0, hy0, hxy⟩]
  rw [hLHS, sum_Pos B _, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sum_Pos B _, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [Int.natAbs_natCast, natAbs_add_pos]

private theorem sum_NN (B : ℕ) :
    ∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), ∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
      (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
        ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
       else 0)
    = (((∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
        ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m + n)) + 1) : ℕ)) : ℕ) : ℤ) := by
  have hLHS : (∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), ∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
      (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
        ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
       else 0))
      = ∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), ∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
        ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.mem_Icc] at hx hy
    have hx0 : x ≠ 0 := by omega
    have hy0 : y ≠ 0 := by omega
    have hxy : x + y ≠ 0 := by omega
    rw [ite_eq_left ⟨hx0, hy0, hxy⟩]
  rw [hLHS, sum_Neg B _, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sum_Neg B _, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [Int.natAbs_neg, Int.natAbs_natCast, natAbs_add_neg]

private theorem sum_PN (B : ℕ) :
    ∑ x ∈ Finset.Icc (1 : ℤ) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
      (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
        ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
       else 0)
    = ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
        (if m ≠ n then
          ((((2 * (B / m) + 1) * (2 * (B / n) + 1) *
            (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)) : ℤ)
         else 0) := by
  have hLHS : (∑ x ∈ Finset.Icc (1 : ℤ) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
      (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
        ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
       else 0))
      = ∑ x ∈ Finset.Icc (1 : ℤ) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
        (if x + y ≠ 0 then
          ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
            (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
         else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.mem_Icc] at hx hy
    have hx0 : x ≠ 0 := by omega
    have hy0 : y ≠ 0 := by omega
    by_cases hxy : x + y ≠ 0
    · rw [ite_eq_left ⟨hx0, hy0, hxy⟩, ite_eq_left hxy]
    · rw [ite_eq_right (fun h => hxy h.2.2), ite_eq_right hxy]
  rw [hLHS, sum_Pos B _]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sum_Neg B _]
  apply Finset.sum_congr rfl
  intro n hn
  have hcond : ((m : ℤ) + (-(n : ℤ)) ≠ 0) ↔ m ≠ n := by
    have hsub : (m : ℤ) + (-(n : ℤ)) = (m : ℤ) - (n : ℤ) := by ring
    rw [hsub, sub_ne_zero]
    exact not_congr Nat.cast_inj
  have hnat : (((m : ℤ) + (-(n : ℤ))).natAbs) = ((m : ℤ) - (n : ℤ)).natAbs := rfl
  by_cases hmn : m ≠ n
  · have hxy : (m : ℤ) + (-(n : ℤ)) ≠ 0 := hcond.mpr hmn
    rw [ite_eq_left hxy, ite_eq_left hmn, hnat]
    simp [Int.natAbs_natCast, Int.natAbs_neg]
  · have hxy : ¬ (m : ℤ) + (-(n : ℤ)) ≠ 0 := fun h => hmn (hcond.mp h)
    rw [ite_eq_right hxy, ite_eq_right hmn]

private theorem sum_NP (B : ℕ) :
    ∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), ∑ y ∈ Finset.Icc (1 : ℤ) B,
      (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
        ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
       else 0)
    = ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
        (if m ≠ n then
          ((((2 * (B / m) + 1) * (2 * (B / n) + 1) *
            (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)) : ℤ)
         else 0) := by
  have hLHS : (∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), ∑ y ∈ Finset.Icc (1 : ℤ) B,
      (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
        ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
       else 0))
      = ∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), ∑ y ∈ Finset.Icc (1 : ℤ) B,
        (if x + y ≠ 0 then
          ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
            (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
         else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.mem_Icc] at hx hy
    have hx0 : x ≠ 0 := by omega
    have hy0 : y ≠ 0 := by omega
    by_cases hxy : x + y ≠ 0
    · rw [ite_eq_left ⟨hx0, hy0, hxy⟩, ite_eq_left hxy]
    · rw [ite_eq_right (fun h => hxy h.2.2), ite_eq_right hxy]
  rw [hLHS, sum_Neg B _]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sum_Pos B _]
  apply Finset.sum_congr rfl
  intro n hn
  have hcond : ((-(m : ℤ)) + (n : ℤ) ≠ 0) ↔ m ≠ n := by
    have hsub : (-(m : ℤ)) + (n : ℤ) = (n : ℤ) - (m : ℤ) := by ring
    rw [hsub, sub_ne_zero]
    exact (not_congr Nat.cast_inj).trans ne_comm
  have hnat : (((-(m : ℤ)) + (n : ℤ)).natAbs) = ((m : ℤ) - (n : ℤ)).natAbs := by
    have hneg : (-(m : ℤ)) + (n : ℤ) = -((m : ℤ) - (n : ℤ)) := by ring
    rw [hneg, Int.natAbs_neg]
  by_cases hmn : m ≠ n
  · have hxy : (-(m : ℤ)) + (n : ℤ) ≠ 0 := hcond.mpr hmn
    rw [ite_eq_left hxy, ite_eq_left hmn, hnat]
    simp [Int.natAbs_natCast, Int.natAbs_neg, mul_comm]
  · have hxy : ¬ (-(m : ℤ)) + (n : ℤ) ≠ 0 := fun h => hmn (hcond.mp h)
    rw [ite_eq_right hxy, ite_eq_right hmn]

private theorem mixed_symm (B m n : ℕ) :
    ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
      (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
    = (2 * (B / n) + 1) * (2 * (B / m) + 1) *
      (2 * (B / ((n : ℤ) - (m : ℤ)).natAbs) + 1) := by
  have habs : ((m : ℤ) - (n : ℤ)).natAbs = ((n : ℤ) - (m : ℤ)).natAbs := by
    have hneg : (m : ℤ) - (n : ℤ) = -((n : ℤ) - (m : ℤ)) := by ring
    rw [hneg, Int.natAbs_neg]
  rw [habs]
  ring

private theorem Ico_eq_filter (B m : ℕ) (hm : m ∈ Finset.Icc 1 B) :
    Finset.Ico 1 m = (Finset.Icc 1 B).filter (fun n => n < m) := by
  simp only [Finset.mem_Icc] at hm
  ext n
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro hn
    exact ⟨⟨hn.1, by omega⟩, hn.2⟩
  · intro hn
    exact ⟨hn.1.1, hn.2⟩

private theorem mixed_double (B : ℕ) :
    (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
      (if m ≠ n then
        ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
          (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
       else 0))
    = 2 * ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Ico 1 m,
        ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m - n)) + 1) : ℕ) := by
  have hL_eq : (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
      (if n < m then
        ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
          (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
       else 0))
      = ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Ico 1 m,
        ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m - n)) + 1) : ℕ) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hfilter : (Finset.Icc 1 B).filter (fun n => n < m) = Finset.Ico 1 m := by
      rw [Ico_eq_filter B m hm]
    have h1 : (∑ n ∈ Finset.Icc 1 B,
        (if n < m then
          ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
            (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
         else 0))
        = ∑ n ∈ (Finset.Icc 1 B).filter (fun n => n < m),
          ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
            (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ) := by
      rw [Finset.sum_filter]
    rw [h1, hfilter]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Ico] at hn
    have hle : n ≤ m := Nat.le_of_lt hn.2
    rw [natAbs_sub_eq m n hle]
  have hU_eq_L : (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
      (if m < n then
        ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
          (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
       else 0))
      = ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
        (if n < m then
          ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
            (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
         else 0) := by
    have hcomm : (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
        (if m < n then
          ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
            (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
         else 0))
        = ∑ n ∈ Finset.Icc 1 B, ∑ m ∈ Finset.Icc 1 B,
          (if m < n then
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
              (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
           else 0) := Finset.sum_comm
    rw [hcomm]
    have hpoint : ∀ m n : ℕ,
        (if n < m then
          ((2 * (B / n) + 1) * (2 * (B / m) + 1) *
            (2 * (B / ((n : ℤ) - (m : ℤ)).natAbs) + 1) : ℕ)
         else 0)
        = (if n < m then
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
              (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
           else 0) := by
      intro m n
      by_cases h : n < m
      · rw [ite_eq_left h, ite_eq_left h, mixed_symm B n m]
      · rw [ite_eq_right h, ite_eq_right h]
    have hrename : (∑ n ∈ Finset.Icc 1 B, ∑ m ∈ Finset.Icc 1 B,
        (if m < n then
          ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
            (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
         else 0))
        = ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          (if n < m then
            ((2 * (B / n) + 1) * (2 * (B / m) + 1) *
              (2 * (B / ((n : ℤ) - (m : ℤ)).natAbs) + 1) : ℕ)
           else 0) := rfl
    rw [hrename]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint m n
  have hsplit : ∀ m n : ℕ,
      (if m ≠ n then
        ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
          (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
       else 0)
      = (if n < m then
          ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
            (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
         else 0)
        + (if m < n then
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
              (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
           else 0) := by
    intro m n
    by_cases hlt : n < m
    · have hne : m ≠ n := by omega
      have hnge : ¬ m < n := by omega
      rw [ite_eq_left hne, ite_eq_left hlt, ite_eq_right hnge, add_zero]
    · by_cases hgt : m < n
      · have hne : m ≠ n := by omega
        rw [ite_eq_left hne, ite_eq_right hlt, ite_eq_left hgt, zero_add]
      · have heq : m = n := by omega
        subst heq
        simp
  have hT : (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
      (if m ≠ n then
        ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
          (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
       else 0))
      = (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          (if n < m then
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
              (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
           else 0))
        + (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          (if m < n then
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
              (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
           else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    exact hsplit m n
  rw [hT, hU_eq_L, hL_eq]
  ring

end divRunCount_three

/-- **Exact formula for the length-three run count.** For a natural number $B$, let $A_B(3)$ be
the number of integer tuples $(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and
$(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at least $3$, and for integers
$m \ge 1$ let $d_B(m) = 2\lfloor B/m \rfloor + 1$. Then
$$A_B(3) = \sum_{x, y} \left(d_B(|x|)\, d_B(|y|)\, d_B(|x+y|) - 1\right),$$
where the sum runs over the integers $x, y \in [-B, B]$ with $x \ne 0$, $y \ne 0$ and
$x + y \ne 0$, and also
$$
A_B(3) = 2 \sum_{m=1}^{B} \sum_{n=1}^{B} d_B(m)\, d_B(n)\, d_B(m+n) +
4 \sum_{1 \le n < m \le B} d_B(m)\, d_B(n)\, d_B(m-n) - (4B^2 - 2B).
$$

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 6
(`integers-2026-A122-prop-6`). -/
public theorem divRunCount_three (B : ℕ) :
    ((divRunCount B 3 : ℤ)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1)
                * (2 * (B / (x + y).natAbs) + 1) - 1 : ℕ)
            else 0) ∧
    (divRunCount B 3 : ℤ)
        = 2 * ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m + n)) + 1) : ℕ)
          + 4 * ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Ico 1 m,
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m - n)) + 1) : ℕ)
          - (4 * B ^ 2 - 2 * B)
    := by
  have hfirst : (divRunCount B 3 : ℤ) =
      ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
        if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
          ((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1)
            * (2 * (B / (x + y).natAbs) + 1) - 1 : ℕ)
        else 0 := by
    have hdecomp : (divRunCount B 3 : ℤ) =
        ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          ∑ t ∈ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
              Finset.Icc (-(B : ℤ)) B,
            if (x, y) ≠ (0, 0) ∧ (t.1, t.2.1, t.2.2) ≠ (0, 0, 0) ∧
                IsDivRunUpTo x y t.1 t.2.1 t.2.2 3 then (1 : ℤ) else 0 := by
      unfold divRunCount
      rw [Finset.natCast_card_filter]
      simp only [Finset.sum_product]
    rw [hdecomp]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    exact Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => divRunCount_three.sum_triple B x y
  refine ⟨hfirst, ?_⟩
  have hfirst_z : (divRunCount B 3 : ℤ) = ∑ x ∈ Finset.Icc (-(B : ℤ)) B,
      ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
        (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
          (((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
            (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ) - 1)
         else 0) := by
    rw [hfirst]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    have hP : 1 ≤ (2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
        (2 * (B / (x + y).natAbs) + 1) := by
      have hP0 : 0 < (2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
          (2 * (B / (x + y).natAbs) + 1) := by positivity
      omega
    by_cases hc : x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0
    · rw [ite_eq_left hc, ite_eq_left hc, Nat.cast_sub hP, Nat.cast_one]
    · rw [ite_eq_right hc, ite_eq_right hc]
  have hsplit : (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
        (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
          (((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
            (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ) - 1)
         else 0))
      = (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
            ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
              (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
           else 0))
        - (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then (1 : ℤ) else 0)) := by
    have hpoint : ∀ x y : ℤ,
        (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
          (((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
            (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ) - 1)
         else 0)
        = (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
            ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
              (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
           else 0)
          - (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then (1 : ℤ) else 0) := by
      intro x y
      by_cases h : x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0
      · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, sub_zero]
    simp only [hpoint, Finset.sum_sub_distrib]
  have hN : (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
        (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then (1 : ℤ) else 0))
      = (((4 * B ^ 2 - 2 * B : ℕ)) : ℤ) := by
    have h1 : (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
        (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then (1 : ℤ) else 0))
        = ∑ p ∈ (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B),
          (if p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0 then (1 : ℤ) else 0) := by
      rw [← Finset.sum_product']
    rw [h1, Finset.sum_boole, divRunCount_three.card_valid]
  have hG : (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
        (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
          ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
            (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
         else 0))
      = 2 * (((∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m + n)) + 1) : ℕ)) : ℕ) : ℤ)
        + 4 * (((∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Ico 1 m,
          ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m - n)) + 1) : ℕ)) : ℕ) : ℤ) := by
    have hinner : ∀ x : ℤ,
        (∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
            ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
              (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
           else 0))
        = (∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
            (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
             else 0))
          + (∑ y ∈ Finset.Icc (1 : ℤ) B,
            (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
             else 0)) := by
      intro x
      apply divRunCount_three.sum_Icc_split
      have h0 : ¬(x ≠ 0 ∧ (0 : ℤ) ≠ 0 ∧ x + 0 ≠ 0) := by simp
      rw [ite_eq_right h0]
    have houter : (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
            ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
              (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
           else 0))
        = (∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
             else 0))
          + (∑ x ∈ Finset.Icc (1 : ℤ) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
             else 0)) := by
      apply divRunCount_three.sum_Icc_split
      apply Finset.sum_eq_zero
      intro y _
      have h0 : ¬((0 : ℤ) ≠ 0 ∧ y ≠ 0 ∧ (0 : ℤ) + y ≠ 0) := by simp
      rw [ite_eq_right h0]
    rw [houter]
    have hNeg : (∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
            ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
              (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
           else 0))
        = (∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), ∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
            (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
             else 0))
          + (∑ x ∈ Finset.Icc (-(B : ℤ)) (-1), ∑ y ∈ Finset.Icc (1 : ℤ) B,
            (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
             else 0)) := by
      have h1 : ∀ x ∈ Finset.Icc (-(B : ℤ)) (-1),
          (∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
             else 0))
          = (∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
              (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
                ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                  (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
               else 0))
            + (∑ y ∈ Finset.Icc (1 : ℤ) B,
              (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
                ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                  (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
               else 0)) := fun x _ => hinner x
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    have hPos : (∑ x ∈ Finset.Icc (1 : ℤ) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
            ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
              (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
           else 0))
        = (∑ x ∈ Finset.Icc (1 : ℤ) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
            (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
             else 0))
          + (∑ x ∈ Finset.Icc (1 : ℤ) B, ∑ y ∈ Finset.Icc (1 : ℤ) B,
            (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
             else 0)) := by
      have h1 : ∀ x ∈ Finset.Icc (1 : ℤ) B,
          (∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
             else 0))
          = (∑ y ∈ Finset.Icc (-(B : ℤ)) (-1),
              (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
                ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                  (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
               else 0))
            + (∑ y ∈ Finset.Icc (1 : ℤ) B,
              (if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
                ((((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1) *
                  (2 * (B / (x + y).natAbs) + 1) : ℕ)) : ℤ)
               else 0)) := fun x _ => hinner x
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    rw [hNeg, hPos, divRunCount_three.sum_NN, divRunCount_three.sum_NP,
      divRunCount_three.sum_PN, divRunCount_three.sum_PP]
    have hT : (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          (if m ≠ n then
            ((((2 * (B / m) + 1) * (2 * (B / n) + 1) *
              (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)) : ℤ)
           else 0))
        = (((∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
            (if m ≠ n then
              ((2 * (B / m) + 1) * (2 * (B / n) + 1) *
                (2 * (B / ((m : ℤ) - (n : ℤ)).natAbs) + 1) : ℕ)
             else 0)) : ℕ) : ℤ) := by
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    rw [hT, divRunCount_three.mixed_double]
    push_cast
    ring
  have hNcast : (((4 * B ^ 2 - 2 * B : ℕ)) : ℤ) = 4 * (B : ℤ) ^ 2 - 2 * (B : ℤ) := by
    have hle : 2 * B ≤ 4 * B ^ 2 := by
      rcases Nat.eq_zero_or_pos B with rfl | hpos
      · simp
      · have h1 : 1 ≤ B := hpos
        nlinarith
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [hfirst_z, hsplit, hN, hG, hNcast]

end MetaMathlibExt
