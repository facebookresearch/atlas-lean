/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

/-! # Fano's inequality

For finitely many hypotheses with pairwise KL divergences at most
`β`, any estimator has average error probability at least
`1 - (β + log 2) / log M`. This is roadmap package ML-30 of the
Atlas TCS canon roadmap, built on the Le Cam two-point bound.

Source: Tsybakov, Introduction to Nonparametric Estimation
(2009), Section 2.3.
-/

open Finset

/-- Kullback-Leibler divergence between two PMFs on a finite type
(in nats, with `0 log 0 = 0`). Only meaningful when `q` dominates
`p`; the theorem assumes this. -/
noncomputable def klSum {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
  ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)

private lemma pmf_ne_top {α : Type*} [Fintype α] (p : PMF α) (a : α) :
    p a ≠ ⊤ := by
  have h1 : (∑ b, p b) = 1 := by
    have h := p.tsum_coe
    rwa [tsum_fintype] at h
  have hle : p a ≤ ∑ b, p b :=
    Finset.single_le_sum (fun _ _ => zero_le) (mem_univ a)
  rw [h1] at hle
  exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hle ENNReal.one_lt_top)

private lemma pmf_toReal_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  have h1 : (∑ b, p b) = 1 := by
    have h := p.tsum_coe
    rwa [tsum_fintype] at h
  have h2 : (∑ b, p b).toReal = ∑ b, (p b).toReal :=
    ENNReal.toReal_sum (fun a _ => pmf_ne_top p a)
  rw [h1] at h2
  simpa using h2.symm

private lemma jensen_concave {ι : Type*} (t : Finset ι) (w p : ι → ℝ)
    {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    (hw0 : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1)
    (hmem : ∀ i ∈ t, p i ∈ s) :
    ∑ i ∈ t, w i * f (p i) ≤ f (∑ i ∈ t, w i * p i) := by
  have h := hf.le_map_sum hw0 hw1 hmem
  simpa [smul_eq_mul] using h

private lemma entropy_le_log_card {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ t i) (h1 : ∑ i ∈ s, t i = 1)
    (hn : 1 ≤ (s.card : ℝ)) :
    ∑ i ∈ s, Real.negMulLog (t i) ≤ Real.log s.card := by
  have hn0 : (s.card : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hn_pos : 0 < (s.card : ℝ) := lt_of_lt_of_le zero_lt_one hn
  set n : ℝ := (s.card : ℝ) with hn_def
  have hw1 : ∑ i ∈ s, (1 / n) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← hn_def, mul_one_div_cancel hn0]
  have hJ := jensen_concave s (fun _ => 1 / n) t Real.concaveOn_negMulLog
    (fun i _ => by positivity) hw1 (fun i hi => Set.mem_Ici.mpr (h0 i hi))
  rw [← Finset.mul_sum, ← Finset.mul_sum, h1, mul_one] at hJ
  have hval : n * Real.negMulLog (1 / n) = Real.log n := by
    have hrw : Real.negMulLog (1 / n) = -(1 / n) * Real.log (1 / n) := rfl
    rw [hrw, one_div, Real.log_inv]
    field_simp
  have h3 : n * ((1 / n) * ∑ i ∈ s, Real.negMulLog (t i)) =
      ∑ i ∈ s, Real.negMulLog (t i) := by
    field_simp
  have h2 := mul_le_mul_of_nonneg_left hJ (le_of_lt hn_pos)
  rw [h3] at h2
  rw [hval] at h2
  exact h2

private lemma log_sum_jensen {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < r i) (hn : 0 < (s.card : ℝ)) :
    ∑ i ∈ s, Real.log (r i) ≤ s.card * Real.log ((∑ i ∈ s, r i) / s.card) := by
  have hn0 : (s.card : ℝ) ≠ 0 := ne_of_gt hn
  set n : ℝ := (s.card : ℝ) with hn_def
  have hw1 : ∑ i ∈ s, (1 / n) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← hn_def, mul_one_div_cancel hn0]
  have hlog := strictConcaveOn_log_Ioi.concaveOn
  have hJ := jensen_concave s (fun _ => 1 / n) r hlog
    (fun i _ => by positivity) hw1 (fun i hi => Set.mem_Ioi.mpr (hpos i hi))
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hJ
  have h3 : n * ((1 / n) * ∑ i ∈ s, Real.log (r i)) =
      ∑ i ∈ s, Real.log (r i) := by
    field_simp
  have h4 : (1 / n) * ∑ i ∈ s, r i = (∑ i ∈ s, r i) / n := by ring
  have h2 := mul_le_mul_of_nonneg_left hJ (le_of_lt hn)
  rw [h3, h4] at h2
  exact h2

private lemma per_symbol_entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → ℝ) (k : ι) (e : ℝ)
    (he : e = ∑ i ∈ Finset.univ.erase k, t i)
    (h0 : ∀ i, 0 ≤ t i) (h1 : ∑ i, t i = 1)
    (hM : 2 ≤ Fintype.card ι) :
    ∑ i, Real.negMulLog (t i) ≤
      Real.binEntropy e + e * Real.log ((Fintype.card ι : ℝ) - 1) := by
  have htk : t k = 1 - e := by
    have h := Finset.add_sum_erase Finset.univ t (Finset.mem_univ k)
    rw [h1, ← he] at h
    linarith
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun i => Real.negMulLog (t i)) (Finset.mem_univ k)
  have he_nonneg : 0 ≤ e := by
    rw [he]
    exact Finset.sum_nonneg (fun i _ => h0 i)
  by_cases he0 : e = 0
  · have hsum0 : ∑ i ∈ Finset.univ.erase k, t i = 0 := by rw [← he, he0]
    have hall : ∀ i ∈ Finset.univ.erase k, t i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h0 i)).mp hsum0
    have hsumN : ∑ i ∈ Finset.univ.erase k, Real.negMulLog (t i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hall i hi, Real.negMulLog_zero]
    have htk1 : t k = 1 := by rw [htk, he0, sub_zero]
    rw [← hsplit, hsumN, htk1, Real.negMulLog_one, he0, Real.binEntropy_zero]
    simp
  · have hepos : 0 < e := lt_of_le_of_ne he_nonneg (Ne.symm he0)
    have hcard : ((Finset.univ.erase k).card : ℝ) =
        (Fintype.card ι : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
        Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one]
    have hcard1 : 1 ≤ ((Finset.univ.erase k).card : ℝ) := by
      rw [hcard]
      have hM' : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hM
      linarith
    have hS1 : ∑ i ∈ Finset.univ.erase k, (t i / e) = 1 := by
      rw [← Finset.sum_div, ← he, div_self (ne_of_gt hepos)]
    have hB := entropy_le_log_card (Finset.univ.erase k) (fun i => t i / e)
      (fun i _ => div_nonneg (h0 i) (le_of_lt hepos)) hS1 hcard1
    rw [hcard] at hB
    have hterm : ∀ i ∈ Finset.univ.erase k, Real.negMulLog (t i) =
        e * Real.negMulLog (t i / e) + t i * (-Real.log e) := by
      intro i _
      by_cases hti : t i = 0
      · rw [hti]
        simp [Real.negMulLog_zero]
      · have hlog : Real.log (t i / e) = Real.log (t i) - Real.log e :=
          Real.log_div hti (ne_of_gt hepos)
        have h1r : Real.negMulLog (t i) = -(t i) * Real.log (t i) := rfl
        have h2r : Real.negMulLog (t i / e) =
            -(t i / e) * Real.log (t i / e) := rfl
        rw [h1r, h2r, hlog]
        field_simp
        ring
    have hsum_eq : ∑ i ∈ Finset.univ.erase k, Real.negMulLog (t i) =
        e * (∑ i ∈ Finset.univ.erase k, Real.negMulLog (t i / e)) +
          Real.negMulLog e := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hmul : ∑ i ∈ Finset.univ.erase k, (t i * (-Real.log e)) =
          (∑ i ∈ Finset.univ.erase k, t i) * (-Real.log e) := by
        rw [Finset.sum_mul]
      rw [hmul, ← he]
      congr 1
      have hrfl : Real.negMulLog e = -e * Real.log e := rfl
      rw [hrfl]
      ring
    have hle : ∑ i ∈ Finset.univ.erase k, Real.negMulLog (t i) ≤
        e * Real.log ((Fintype.card ι : ℝ) - 1) + Real.negMulLog e := by
      rw [hsum_eq]
      have hB' := mul_le_mul_of_nonneg_left hB (le_of_lt hepos)
      linarith
    rw [← hsplit, htk, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    linarith [hle]

private noncomputable def fanJ {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → PMF α) (i : ι) (a : α) : ℝ :=
  (P i a).toReal / (Fintype.card ι : ℝ)

private noncomputable def fanQ {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → PMF α) (a : α) : ℝ :=
  (∑ i, (P i a).toReal) / (Fintype.card ι : ℝ)

private noncomputable def fanE {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → PMF α) (est : α → ι) (a : α) : ℝ :=
  (∑ i ∈ Finset.univ.erase (est a), fanJ P i a) / fanQ P a

private lemma fanQ_eq_sum {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → PMF α) (a : α) :
    fanQ P a = ∑ i, fanJ P i a := by
  simp only [fanQ, fanJ]
  exact Finset.sum_div Finset.univ (fun i => (P i a).toReal)
    ((Fintype.card ι : ℝ))

private lemma fanQ_sum {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → PMF α) (hM : 1 ≤ Fintype.card ι) :
    ∑ a, fanQ P a = 1 := by
  have hM0 : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  simp only [fanQ]
  rw [← Finset.sum_div, Finset.sum_comm]
  have h1 : ∀ i, ∑ a, (P i a).toReal = 1 := fun i => pmf_toReal_sum (P i)
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, div_self hM0]

private lemma fanJ_nonneg {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → PMF α) (i : ι) (a : α) : 0 ≤ fanJ P i a := by
  simp only [fanJ]
  exact div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

private lemma fanQ_nonneg {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → PMF α) (a : α) : 0 ≤ fanQ P a := by
  simp only [fanQ]
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    (Nat.cast_nonneg _)

private lemma fanE_mul {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → PMF α) (est : α → ι) (a : α) :
    fanQ P a * fanE P est a = ∑ i ∈ Finset.univ.erase (est a), fanJ P i a := by
  simp only [fanE]
  by_cases hQ : fanQ P a = 0
  · have hsum : ∑ i, fanJ P i a = 0 := by rw [← fanQ_eq_sum P a, hQ]
    have hall : ∀ i, fanJ P i a = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => fanJ_nonneg P i a)).mp hsum
        i (Finset.mem_univ i)
    rw [hQ, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact hall i
  · field_simp

private lemma fanE_mem {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → PMF α) (est : α → ι) (a : α) :
    fanE P est a ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [fanE]
  rw [Set.mem_Icc]
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => fanJ_nonneg P i a))
      (fanQ_nonneg P a)
  · by_cases hQ : fanQ P a = 0
    · rw [hQ, div_zero]
      exact zero_le_one
    · have hQpos : 0 < fanQ P a :=
        lt_of_le_of_ne (fanQ_nonneg P a) (Ne.symm hQ)
      rw [div_le_one hQpos, fanQ_eq_sum P a]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun i _ _ => fanJ_nonneg P i a)

private lemma cond_identity {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → PMF α) (a : α) :
    ∑ i, Real.negMulLog (fanJ P i a) - Real.negMulLog (fanQ P a) =
      fanQ P a * ∑ i, Real.negMulLog (fanJ P i a / fanQ P a) := by
  rw [Finset.mul_sum]
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      fanQ P a * Real.negMulLog (fanJ P i a / fanQ P a) =
      Real.negMulLog (fanJ P i a) + fanJ P i a * Real.log (fanQ P a) := by
    intro i _
    by_cases hJ : fanJ P i a = 0
    · simp [hJ, Real.negMulLog_zero]
    · have hle : fanJ P i a ≤ ∑ j, fanJ P j a :=
        Finset.single_le_sum (fun j _ => fanJ_nonneg P j a) (Finset.mem_univ i)
      have hJpos : 0 < fanJ P i a :=
        lt_of_le_of_ne (fanJ_nonneg P i a) (Ne.symm hJ)
      have hsumpos : 0 < ∑ j, fanJ P j a := lt_of_lt_of_le hJpos hle
      rw [← fanQ_eq_sum P a] at hsumpos
      have hQ : fanQ P a ≠ 0 := ne_of_gt hsumpos
      have hlog : Real.log (fanJ P i a / fanQ P a) =
          Real.log (fanJ P i a) - Real.log (fanQ P a) := Real.log_div hJ hQ
      have h1r : Real.negMulLog (fanJ P i a / fanQ P a) =
          -(fanJ P i a / fanQ P a) * Real.log (fanJ P i a / fanQ P a) := rfl
      have h2r : Real.negMulLog (fanJ P i a) =
          -(fanJ P i a) * Real.log (fanJ P i a) := rfl
      rw [h1r, h2r, hlog]
      field_simp
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hmul : ∑ i, (fanJ P i a * Real.log (fanQ P a)) =
      (∑ i, fanJ P i a) * Real.log (fanQ P a) := by
    rw [← Finset.sum_mul]
  rw [hmul, ← fanQ_eq_sum P a]
  have hrfl : Real.negMulLog (fanQ P a) = -(fanQ P a) * Real.log (fanQ P a) := rfl
  rw [hrfl]
  ring

private lemma cond_bound {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → PMF α) (est : α → ι) (a : α)
    (hM : 2 ≤ Fintype.card ι) :
    ∑ i, Real.negMulLog (fanJ P i a) - Real.negMulLog (fanQ P a) ≤
      fanQ P a * (Real.binEntropy (fanE P est a) +
        fanE P est a * Real.log ((Fintype.card ι : ℝ) - 1)) := by
  by_cases hQ : fanQ P a = 0
  · have hsum : ∑ i, fanJ P i a = 0 := by rw [← fanQ_eq_sum P a, hQ]
    have hall : ∀ i, fanJ P i a = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => fanJ_nonneg P i a)).mp hsum
        i (Finset.mem_univ i)
    have hJN : ∑ i, Real.negMulLog (fanJ P i a) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hall i, Real.negMulLog_zero]
    rw [hJN, hQ, Real.negMulLog_zero, sub_zero, zero_mul]
  · have h1 : ∑ i, (fanJ P i a / fanQ P a) = 1 := by
      rw [← Finset.sum_div, ← fanQ_eq_sum P a, div_self hQ]
    have he : fanE P est a =
        ∑ i ∈ Finset.univ.erase (est a), (fanJ P i a / fanQ P a) := by
      simp only [fanE]
      rw [← Finset.sum_div]
    have hPS := per_symbol_entropy (fun i => fanJ P i a / fanQ P a) (est a)
      (fanE P est a) he
      (fun i => div_nonneg (fanJ_nonneg P i a) (fanQ_nonneg P a)) h1 hM
    rw [cond_identity P a]
    exact mul_le_mul_of_nonneg_left hPS (fanQ_nonneg P a)

private lemma err_sum {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → PMF α) (est : α → ι) :
    ∑ a, ∑ i ∈ Finset.univ.erase (est a), fanJ P i a =
      (∑ i, ∑ a ∈ Finset.univ.filter (fun a => est a ≠ i), (P i a).toReal) /
        (Fintype.card ι : ℝ) := by
  have h1 : ∀ a, ∑ i ∈ Finset.univ.erase (est a), fanJ P i a =
      ∑ i, (if i ≠ est a then fanJ P i a else 0) := by
    intro a
    rw [← Finset.filter_ne' Finset.univ (est a), Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_comm]
  have h2 : ∀ i, (∑ a, (if i ≠ est a then fanJ P i a else 0)) =
      ∑ a ∈ Finset.univ.filter (fun a => est a ≠ i), fanJ P i a := by
    intro i
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : est a ≠ i
    · simp [h, Ne.symm h]
    · have h2 : ¬ (i ≠ est a) := fun hh => h (Ne.symm hh)
      simp [h, h2]
  rw [Finset.sum_congr rfl (fun i _ => h2 i)]
  simp only [fanJ]
  simp_rw [← Finset.sum_div]

private lemma pe_eq {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → PMF α) (est : α → ι) :
    ∑ a, fanQ P a * fanE P est a =
      (∑ i, ∑ a ∈ Finset.univ.filter (fun a => est a ≠ i), (P i a).toReal) /
        (Fintype.card ι : ℝ) := by
  rw [Finset.sum_congr rfl (fun a _ => fanE_mul P est a)]
  exact err_sum P est

private lemma binEnt_le {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → PMF α) (est : α → ι) (hM : 1 ≤ Fintype.card ι) :
    ∑ a, fanQ P a * Real.binEntropy (fanE P est a) ≤ Real.log 2 := by
  have hJ := jensen_concave Finset.univ (fun a => fanQ P a) (fun a => fanE P est a)
    Real.strictConcave_binEntropy.concaveOn
    (fun a _ => fanQ_nonneg P a) (fanQ_sum P hM) (fun a _ => fanE_mem P est a)
  exact le_trans hJ Real.binEntropy_le_log_two

private lemma Hcond_le {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → PMF α) (est : α → ι)
    (hM : 2 ≤ Fintype.card ι) :
    ∑ a, (∑ i, Real.negMulLog (fanJ P i a) - Real.negMulLog (fanQ P a)) ≤
      Real.log 2 + ((∑ i, ∑ a ∈ Finset.univ.filter (fun a => est a ≠ i),
        (P i a).toReal) / (Fintype.card ι : ℝ)) *
        Real.log ((Fintype.card ι : ℝ) - 1) := by
  have hM1 : 1 ≤ Fintype.card ι := by omega
  have hle : (∑ a, (∑ i, Real.negMulLog (fanJ P i a) - Real.negMulLog (fanQ P a))) ≤
      ∑ a, fanQ P a * (Real.binEntropy (fanE P est a) +
        fanE P est a * Real.log ((Fintype.card ι : ℝ) - 1)) :=
    Finset.sum_le_sum (fun a _ => cond_bound P est a hM)
  have hexpand : ∀ a, fanQ P a * (Real.binEntropy (fanE P est a) +
      fanE P est a * Real.log ((Fintype.card ι : ℝ) - 1)) =
      fanQ P a * Real.binEntropy (fanE P est a) +
        (fanQ P a * fanE P est a) * Real.log ((Fintype.card ι : ℝ) - 1) := by
    intro a; ring
  rw [Finset.sum_congr rfl (fun a _ => hexpand a), Finset.sum_add_distrib,
    ← Finset.sum_mul, pe_eq P est] at hle
  exact le_trans hle (add_le_add_left (binEnt_le P est hM1) _)

private lemma MI_eq {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → PMF α) (hM : 2 ≤ Fintype.card ι) :
    Real.log (Fintype.card ι : ℝ) =
      (∑ i, ∑ a, fanJ P i a * Real.log (fanJ P i a / (fanQ P a / (Fintype.card ι : ℝ)))) +
      (∑ a, (∑ i, Real.negMulLog (fanJ P i a) - Real.negMulLog (fanQ P a))) := by
  have hM0 : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  have hterm : ∀ i a, fanJ P i a * Real.log (fanJ P i a / (fanQ P a / (Fintype.card ι : ℝ))) =
      fanJ P i a * Real.log (fanJ P i a) -
        fanJ P i a * Real.log (fanQ P a / (Fintype.card ι : ℝ)) := by
    intro i a
    by_cases hJ : fanJ P i a = 0
    · simp [hJ]
    · have hle : fanJ P i a ≤ ∑ j, fanJ P j a :=
        Finset.single_le_sum (fun j _ => fanJ_nonneg P j a) (Finset.mem_univ i)
      have hJpos : 0 < fanJ P i a :=
        lt_of_le_of_ne (fanJ_nonneg P i a) (Ne.symm hJ)
      have hsumpos : 0 < ∑ j, fanJ P j a := lt_of_lt_of_le hJpos hle
      rw [← fanQ_eq_sum P a] at hsumpos
      have hQ : fanQ P a / (Fintype.card ι : ℝ) ≠ 0 :=
        div_ne_zero (ne_of_gt hsumpos) hM0
      rw [Real.log_div hJ hQ, mul_sub]
  have hMI : (∑ i, ∑ a, fanJ P i a * Real.log (fanJ P i a / (fanQ P a / (Fintype.card ι : ℝ)))) =
      (∑ i, ∑ a, fanJ P i a * Real.log (fanJ P i a)) -
        ∑ a, fanQ P a * Real.log (fanQ P a / (Fintype.card ι : ℝ)) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => hterm i a))]
    simp_rw [Finset.sum_sub_distrib]
    have hY : (∑ i, ∑ a, fanJ P i a * Real.log (fanQ P a / (Fintype.card ι : ℝ))) =
        ∑ a, fanQ P a * Real.log (fanQ P a / (Fintype.card ι : ℝ)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_mul, ← fanQ_eq_sum P a]
    rw [hY]
  have hQx : ∀ a, fanQ P a * Real.log (fanQ P a / (Fintype.card ι : ℝ)) =
      fanQ P a * Real.log (fanQ P a) - fanQ P a * Real.log (Fintype.card ι : ℝ) := by
    intro a
    by_cases h0 : fanQ P a = 0
    · simp [h0]
    · rw [Real.log_div h0 hM0, mul_sub]
  have hneg : ∀ x : ℝ, x * Real.log x = -Real.negMulLog x := by
    intro x
    have hrfl : Real.negMulLog x = -x * Real.log x := rfl
    rw [hrfl]; ring
  have hM1 : 1 ≤ Fintype.card ι := by omega
  have hB2 : ∑ a, fanQ P a * Real.log (Fintype.card ι : ℝ) =
      Real.log (Fintype.card ι : ℝ) := by
    rw [← Finset.sum_mul, fanQ_sum P hM1, one_mul]
  have hAC : (∑ i, ∑ a, fanJ P i a * Real.log (fanJ P i a)) +
      (∑ a, ∑ i, Real.negMulLog (fanJ P i a)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_add_distrib]
    have hzero : ∀ a i, fanJ P i a * Real.log (fanJ P i a) +
        Real.negMulLog (fanJ P i a) = 0 := by
      intro a i
      rw [hneg]
      ring
    simp_rw [hzero]
    simp
  have hBD : (∑ a, fanQ P a * Real.log (fanQ P a)) +
      (∑ a, Real.negMulLog (fanQ P a)) = 0 := by
    simp_rw [← Finset.sum_add_distrib]
    have hzero : ∀ a, fanQ P a * Real.log (fanQ P a) +
        Real.negMulLog (fanQ P a) = 0 := by
      intro a
      rw [hneg]
      ring
    simp_rw [hzero]
    simp
  rw [hMI, Finset.sum_congr rfl (fun a _ => hQx a)]
  simp_rw [Finset.sum_sub_distrib]
  rw [hB2]
  linarith [hAC, hBD]

private lemma kl_mix {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → PMF α) (hsupp : ∀ i j a, (P j a) = 0 → (P i a) = 0)
    (β : ℝ) (hkl : ∀ i j, klSum (P i) (P j) ≤ β)
    (hM : 2 ≤ Fintype.card ι) (i : ι) :
    ∑ a, ((P i a).toReal * Real.log ((P i a).toReal / fanQ P a)) ≤ β := by
  have hM0 : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  have hMpos : 0 < (Fintype.card ι : ℝ) := by
    have h2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hM
    linarith
  have hterm : ∀ a, (P i a).toReal * Real.log ((P i a).toReal / fanQ P a) ≤
      (1 / (Fintype.card ι : ℝ)) *
        ∑ j, ((P i a).toReal * Real.log ((P i a).toReal / (P j a).toReal)) := by
    intro a
    by_cases hp : (P i a).toReal = 0
    · simp [hp]
    · have hsupp_pos : ∀ j, 0 < (P j a).toReal := by
        intro j
        refine ENNReal.toReal_pos ?_ (pmf_ne_top (P j) a)
        intro hj0
        have hi0 := hsupp i j a hj0
        rw [hi0, ENNReal.toReal_zero] at hp
        exact absurd rfl hp
      have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨i0⟩ := hne
      have hSpos : 0 < ∑ j, (P j a).toReal :=
        Finset.sum_pos (fun j _ => hsupp_pos j) ⟨i0, Finset.mem_univ i0⟩
      have hQxpos : 0 < fanQ P a := by
        simp only [fanQ]
        exact div_pos hSpos hMpos
      have hJ := log_sum_jensen Finset.univ (fun j => (P j a).toReal)
        (fun j _ => hsupp_pos j) hMpos
      rw [Finset.card_univ] at hJ
      have hQxeq : (∑ j, (P j a).toReal) / (Fintype.card ι : ℝ) = fanQ P a := rfl
      rw [hQxeq] at hJ
      have havg : (1 / (Fintype.card ι : ℝ)) * ∑ j, Real.log (P j a).toReal ≤
          Real.log (fanQ P a) := by
        have h2 := mul_le_mul_of_nonneg_left hJ
          (le_of_lt (one_div_pos.mpr hMpos))
        have h3 : (1 / (Fintype.card ι : ℝ)) *
            ((Fintype.card ι : ℝ) * Real.log (fanQ P a)) =
            Real.log (fanQ P a) := by
          field_simp
        rw [h3] at h2
        exact h2
      have hsplit : Real.log ((P i a).toReal / fanQ P a) =
          Real.log (P i a).toReal - Real.log (fanQ P a) :=
        Real.log_div (hp) (ne_of_gt hQxpos)
      have hperj : ∀ j, Real.log ((P i a).toReal / (P j a).toReal) =
          Real.log (P i a).toReal - Real.log (P j a).toReal := by
        intro j
        exact Real.log_div (hp) (ne_of_gt (hsupp_pos j))
      have hRHS : (1 / (Fintype.card ι : ℝ)) *
            ∑ j, Real.log ((P i a).toReal / (P j a).toReal) =
          Real.log (P i a).toReal -
            (1 / (Fintype.card ι : ℝ)) * ∑ j, Real.log (P j a).toReal := by
        rw [Finset.sum_congr rfl (fun j _ => hperj j), Finset.sum_sub_distrib,
          mul_sub, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcancel : (1 / (Fintype.card ι : ℝ)) *
            ((Fintype.card ι : ℝ) * Real.log (P i a).toReal) =
            Real.log (P i a).toReal := by
          field_simp
        rw [hcancel]
      have hmain : Real.log ((P i a).toReal / fanQ P a) ≤
          (1 / (Fintype.card ι : ℝ)) *
            ∑ j, Real.log ((P i a).toReal / (P j a).toReal) := by
        rw [hsplit, hRHS]
        linarith [havg]
      have hfin : (P i a).toReal * Real.log ((P i a).toReal / fanQ P a) ≤
          (P i a).toReal * ((1 / (Fintype.card ι : ℝ)) *
            ∑ j, Real.log ((P i a).toReal / (P j a).toReal)) :=
        mul_le_mul_of_nonneg_left hmain ENNReal.toReal_nonneg
      have hmul : (1 / (Fintype.card ι : ℝ)) *
            ∑ j, ((P i a).toReal * Real.log ((P i a).toReal / (P j a).toReal)) =
          (P i a).toReal * ((1 / (Fintype.card ι : ℝ)) *
            ∑ j, Real.log ((P i a).toReal / (P j a).toReal)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hmul]
      exact hfin
  have hsum : (∑ a, ((P i a).toReal * Real.log ((P i a).toReal / fanQ P a))) ≤
      ∑ a, ((1 / (Fintype.card ι : ℝ)) *
        ∑ j, ((P i a).toReal * Real.log ((P i a).toReal / (P j a).toReal))) :=
    Finset.sum_le_sum (fun a _ => hterm a)
  have hRHS : (∑ a, ((1 / (Fintype.card ι : ℝ)) *
        ∑ j, ((P i a).toReal * Real.log ((P i a).toReal / (P j a).toReal)))) =
      (1 / (Fintype.card ι : ℝ)) * ∑ j, klSum (P i) (P j) := by
    simp only [klSum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hβ : (1 / (Fintype.card ι : ℝ)) * ∑ j, klSum (P i) (P j) ≤ β := by
    have hle : (∑ j, klSum (P i) (P j)) ≤ ∑ _ : ι, β :=
      Finset.sum_le_sum (fun j _ => hkl i j)
    have hcard : (∑ _ : ι, β) = (Fintype.card ι : ℝ) * β := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard] at hle
    have hcancel : (1 / (Fintype.card ι : ℝ)) *
        ((Fintype.card ι : ℝ) * β) = β := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hle (le_of_lt (one_div_pos.mpr hMpos))
    rw [hcancel] at h2
    exact h2
  rw [hRHS] at hsum
  exact le_trans hsum hβ

private lemma MI_le {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → PMF α) (hsupp : ∀ i j a, (P j a) = 0 → (P i a) = 0)
    (β : ℝ) (hkl : ∀ i j, klSum (P i) (P j) ≤ β)
    (hM : 2 ≤ Fintype.card ι) :
    (∑ i, ∑ a, fanJ P i a * Real.log (fanJ P i a / (fanQ P a / (Fintype.card ι : ℝ)))) ≤ β := by
  have hM0 : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  have hMpos : 0 < (Fintype.card ι : ℝ) := by
    have h2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hM
    linarith
  have hdiv : ∀ i a, fanJ P i a / (fanQ P a / (Fintype.card ι : ℝ)) =
      (P i a).toReal / fanQ P a := by
    intro i a
    simp only [fanJ]
    field_simp
  have hJeq : ∀ i a, fanJ P i a = (1 / (Fintype.card ι : ℝ)) * (P i a).toReal := by
    intro i a
    simp only [fanJ]
    ring
  have hterm : ∀ i a, fanJ P i a * Real.log (fanJ P i a / (fanQ P a / (Fintype.card ι : ℝ))) =
      (1 / (Fintype.card ι : ℝ)) *
        ((P i a).toReal * Real.log ((P i a).toReal / fanQ P a)) := by
    intro i a
    rw [hdiv, hJeq]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => hterm i a))]
  have hfac : (∑ i, ∑ a, ((1 / (Fintype.card ι : ℝ)) *
        ((P i a).toReal * Real.log ((P i a).toReal / fanQ P a)))) =
      (1 / (Fintype.card ι : ℝ)) *
        ∑ i, ∑ a, ((P i a).toReal * Real.log ((P i a).toReal / fanQ P a)) := by
    simp_rw [← Finset.mul_sum]
  rw [hfac]
  have hle : (∑ i, ∑ a, ((P i a).toReal * Real.log ((P i a).toReal / fanQ P a))) ≤
      ∑ _ : ι, β :=
    Finset.sum_le_sum (fun i _ => kl_mix P hsupp β hkl hM i)
  have hcard : (∑ _ : ι, β) = (Fintype.card ι : ℝ) * β := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcard] at hle
  have hcancel : (1 / (Fintype.card ι : ℝ)) * ((Fintype.card ι : ℝ) * β) = β := by
    field_simp
  have h2 := mul_le_mul_of_nonneg_left hle (le_of_lt (one_div_pos.mpr hMpos))
  rw [hcancel] at h2
  exact h2

/-- Fano's inequality (finite form): for distributions `P i` on a
finite type, an estimator `est`, at least two hypotheses, and
pairwise KL divergences at most `β`, the average error probability
of `est` is at least `1 - (β + log 2) / log M`. -/
theorem fano_finite {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → PMF α) (est : α → ι)
    (hM : 2 ≤ Fintype.card ι)
    (hsupp : ∀ i j a, (P j a) = 0 → (P i a) = 0)
    (β : ℝ) (hkl : ∀ i j, klSum (P i) (P j) ≤ β) :
    1 - (β + Real.log 2) / Real.log (Fintype.card ι) ≤
      (∑ i, (∑ a ∈ Finset.univ.filter (fun a => est a ≠ i), (P i a).toReal)) / Fintype.card ι := by
  have h2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hM
  have h1lt : (1 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  have hlogM : 0 < Real.log (Fintype.card ι : ℝ) := Real.log_pos h1lt
  have hMI := MI_eq P hM
  have hMIle := MI_le P hsupp β hkl hM
  have hHle := Hcond_le P est hM
  have hlogle : Real.log ((Fintype.card ι : ℝ) - 1) ≤
      Real.log (Fintype.card ι : ℝ) := by
    apply Real.log_le_log
    · linarith
    · linarith
  have hpe_nonneg : 0 ≤ (∑ i, ∑ a ∈ Finset.univ.filter (fun a => est a ≠ i),
      (P i a).toReal) / (Fintype.card ι : ℝ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro a _
    exact ENNReal.toReal_nonneg
  have hpe_le : ((∑ i, ∑ a ∈ Finset.univ.filter (fun a => est a ≠ i),
        (P i a).toReal) / (Fintype.card ι : ℝ)) *
        Real.log ((Fintype.card ι : ℝ) - 1) ≤
      ((∑ i, ∑ a ∈ Finset.univ.filter (fun a => est a ≠ i),
        (P i a).toReal) / (Fintype.card ι : ℝ)) *
        Real.log (Fintype.card ι : ℝ) :=
    mul_le_mul_of_nonneg_left hlogle hpe_nonneg
  have hcomb : (1 - (∑ i, ∑ a ∈ Finset.univ.filter (fun a => est a ≠ i),
      (P i a).toReal) / (Fintype.card ι : ℝ)) * Real.log (Fintype.card ι : ℝ) ≤
      β + Real.log 2 := by
    linarith [hMI, hMIle, hHle, hpe_le]
  have hdiv : 1 - (∑ i, ∑ a ∈ Finset.univ.filter (fun a => est a ≠ i),
      (P i a).toReal) / (Fintype.card ι : ℝ) ≤
      (β + Real.log 2) / Real.log (Fintype.card ι : ℝ) := by
    rw [le_div_iff₀ hlogM]
    linarith [hcomb]
  linarith [hdiv]
