/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-! # Total variation and couplings on finite spaces

`tvDist` is half the `L1` distance between two probability mass
functions on a finite discrete space. The coupling inequality
bounds it by the probability that coupled samples differ, and a
maximal coupling attains equality. This is the finite-space core of
roadmap package ML-23 of the Atlas TCS canon roadmap; the bridges
to the measure-theoretic total variation distance in
`MathlibExt/Probability/TotalVariationDistance.lean` are follow-ups.

Source: Levin and Peres, Markov Chains and Mixing Times (2017),
Section 4.1.
-/

open Finset

/-- Total variation distance between two probability mass functions
on a finite type: half the `L1` distance. -/
noncomputable def tvDist {α : Type*} [Fintype α] [MeasurableSpace α] (p q : PMF α) : ℝ :=
  (1 / 2) * ∑ a, |(p a).toReal - (q a).toReal|

/-- A coupling of `p` and `q`: a joint law on `α × α` with the two
coordinate marginals `p` and `q`. -/
def IsCoupling {α : Type*} [Fintype α] [MeasurableSpace α] (p q : PMF α) (r : PMF (α × α)) : Prop :=
  (∀ a, ∑ b, r (a, b) = p a) ∧ (∀ b, ∑ a, r (a, b) = q b)

-- Helpers (private).

private theorem pmf_ne_top {α : Type*} (p : PMF α) (a : α) : p a ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one p a)

private theorem pmf_sum_eq_one {α : Type*} [Fintype α] (p : PMF α) : ∑ a, p a = 1 :=
  (tsum_fintype _).symm.trans (PMF.tsum_coe p)

private theorem abs_sub_le_add_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x - y| ≤ x + y := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

private theorem erase_sum_eq {α : Type*} [Fintype α] [DecidableEq α] (a : α) (g : α → ℝ) :
    ∑ b ∈ univ.erase a, g b = ∑ b, (if a ≠ b then g b else 0) := by
  symm
  have h := Finset.sum_subset (erase_subset a univ)
    (f := fun b => if a ≠ b then g b else 0)
    (fun b _ hb => by
      simp only [mem_erase, mem_univ, and_true] at hb
      have hba : b = a := not_ne_iff.mp hb
      simp [hba])
  rw [← h]
  apply sum_congr rfl
  intro b hb
  simp only [mem_erase, mem_univ, and_true] at hb
  simp [Ne.symm hb]

private theorem sum_offdiag_eq {α : Type*} [Fintype α] [DecidableEq α] (u : α × α → ℝ) :
    ∑ x ∈ univ.filter (fun x => x.1 ≠ x.2), u x
      = ∑ a, ∑ b ∈ univ.erase a, u (a, b) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  rw [erase_sum_eq a (fun b => u (a, b))]

private theorem abs_sub_eq_add_sub_two_min {x y : ℝ} :
    |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring

private theorem ennreal_eq_sub_of_add_eq {x s : ENNReal} (hx : x ≠ ⊤) (hs : s ≠ ⊤)
    (hle : s ≤ 1) (h : x + s = 1) : x = 1 - s := by
  have hts : (1 : ENNReal) - s ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have h1 : x.toReal + s.toReal = 1 := by
    have hcon := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_add hx hs, ENNReal.toReal_one] at hcon
  have h2 : ((1 : ENNReal) - s).toReal = x.toReal := by
    rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one]
    linarith
  apply le_antisymm
  · exact (ENNReal.toReal_le_toReal hx hts).mp h2.ge
  · exact (ENNReal.toReal_le_toReal hts hx).mp h2.le

/-- The coupling inequality: total variation is at most the
probability that the coupled samples differ. -/
theorem tvDist_le_prob_ne {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {p q : PMF α} {r : PMF (α × α)}
    (hr : IsCoupling p q r) :
    tvDist p q ≤ (r.toMeasure {x : α × α | x.1 ≠ x.2}).toReal := by
  obtain ⟨hleft, hright⟩ := hr
  classical
  -- Real-valued masses.
  set u : α × α → ℝ := fun x => (r x).toReal with hu
  -- Marginal identities in reals.
  have hrow : ∀ a : α, (p a).toReal = ∑ b, u (a, b) := by
    intro a
    rw [← hleft a]
    rw [ENNReal.toReal_sum (fun b _ => pmf_ne_top r (a, b))]
  have hcol : ∀ b : α, (q b).toReal = ∑ a, u (a, b) := by
    intro b
    rw [← hright b]
    rw [ENNReal.toReal_sum (fun a _ => pmf_ne_top r (a, b))]
  -- Off-diagonal finset.
  set D : Finset (α × α) := univ.filter (fun x => x.1 ≠ x.2) with hD
  -- Measure of the off-diagonal set as a finset sum.
  have hmeas : (r.toMeasure {x : α × α | x.1 ≠ x.2}).toReal = ∑ x ∈ D, u x := by
    have h1 : r.toMeasure {x : α × α | x.1 ≠ x.2}
        = ∑ x, {x : α × α | x.1 ≠ x.2}.indicator (⇑r) x := by
      rw [PMF.toMeasure_apply r MeasurableSet.of_discrete, tsum_fintype]
    rw [h1, ENNReal.toReal_sum (fun x _ => by
      by_cases hx : x ∈ {x : α × α | x.1 ≠ x.2}
      · rw [Set.indicator_of_mem hx]; exact pmf_ne_top r x
      · rw [Set.indicator_of_notMem hx]; exact ENNReal.zero_ne_top)]
    rw [hD, Finset.sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases hx : x.1 ≠ x.2
    · have hx' : x ∈ {x : α × α | x.1 ≠ x.2} := hx
      rw [Set.indicator_of_mem hx']
      simp [hx, hu]
    · have hx' : x ∉ {x : α × α | x.1 ≠ x.2} := hx
      rw [Set.indicator_of_notMem hx']
      simp [hx]
  -- Per-point bound.
  have hper : ∀ a : α, |(p a).toReal - (q a).toReal|
      ≤ ∑ b ∈ univ.erase a, (u (a, b) + u (b, a)) := by
    intro a
    have hdiff : (p a).toReal - (q a).toReal
        = ∑ b ∈ univ.erase a, (u (a, b) - u (b, a)) := by
      rw [hrow a, hcol a, ← Finset.sum_sub_distrib]
      have h0 : u (a, a) - u (a, a) = 0 := sub_self _
      have h := Finset.add_sum_erase univ (fun b => u (a, b) - u (b, a)) (mem_univ a)
      rw [h0, zero_add] at h
      exact h.symm
    calc |(p a).toReal - (q a).toReal|
        = |∑ b ∈ univ.erase a, (u (a, b) - u (b, a))| := by rw [hdiff]
      _ ≤ ∑ b ∈ univ.erase a, |u (a, b) - u (b, a)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ univ.erase a, (u (a, b) + u (b, a)) :=
          sum_le_sum fun b _ => abs_sub_le_add_of_nonneg
            ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hsum : ∑ a, |(p a).toReal - (q a).toReal|
      ≤ ∑ a, ∑ b ∈ univ.erase a, (u (a, b) + u (b, a)) :=
    sum_le_sum fun a _ => hper a
  -- Collapse the double sum to twice the off-diagonal mass.
  have hA : ∑ a, ∑ b ∈ univ.erase a, u (a, b) = ∑ x ∈ D, u x :=
    (sum_offdiag_eq u).symm
  have hB : ∑ a, ∑ b ∈ univ.erase a, u (b, a) = ∑ x ∈ D, u x := by
    have h1 : ∀ a : α, ∑ b ∈ univ.erase a, u (b, a)
        = ∑ b, (if a ≠ b then u (b, a) else 0) := fun a => erase_sum_eq a _
    have hswap : (∑ a, ∑ b, (if a ≠ b then u (b, a) else 0))
        = ∑ a, ∑ b, (if a ≠ b then u (a, b) else 0) := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      by_cases h : a ≠ b
      · simp [h, Ne.symm h]
      · have h' : ¬ b ≠ a := fun hh => h (Ne.symm hh)
        simp [h, h']
    calc ∑ a, ∑ b ∈ univ.erase a, u (b, a)
        = ∑ a, ∑ b, (if a ≠ b then u (b, a) else 0) := by simp_rw [h1]
      _ = ∑ a, ∑ b, (if a ≠ b then u (a, b) else 0) := hswap
      _ = ∑ a, ∑ b ∈ univ.erase a, u (a, b) := by simp_rw [erase_sum_eq]
      _ = ∑ x ∈ D, u x := (sum_offdiag_eq u).symm
  have hRHS : ∑ a, ∑ b ∈ univ.erase a, (u (a, b) + u (b, a))
      = 2 * ∑ x ∈ D, u x := by
    have h1 : ∀ a : α, ∑ b ∈ univ.erase a, (u (a, b) + u (b, a))
        = ∑ b ∈ univ.erase a, u (a, b) + ∑ b ∈ univ.erase a, u (b, a) :=
      fun a => Finset.sum_add_distrib
    simp_rw [h1, Finset.sum_add_distrib, hA, hB]
    ring
  -- Assemble.
  have hfin : ∑ a, |(p a).toReal - (q a).toReal| ≤ 2 * ∑ x ∈ D, u x :=
    hsum.trans_eq hRHS
  rw [hmeas]
  unfold tvDist
  calc (1 / 2) * ∑ a, |(p a).toReal - (q a).toReal|
      ≤ (1 / 2) * (2 * ∑ x ∈ D, u x) :=
        mul_le_mul_of_nonneg_left hfin (by norm_num)
    _ = ∑ x ∈ D, u x := by ring

/-- A maximal coupling exists: some coupling attains equality in the
coupling inequality. -/
theorem exists_maximal_coupling {α : Type*} [Fintype α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (p q : PMF α) :
    ∃ r : PMF (α × α), IsCoupling p q r ∧
      (r.toMeasure {x : α × α | x.1 ≠ x.2}).toReal = tvDist p q := by
  classical
  -- Common part and overlap.
  set m : α → ENNReal := fun a => min (p a) (q a) with hm_def
  have hm_eq : ∀ a, m a = min (p a) (q a) := fun a => rfl
  set s : ENNReal := ∑ a, m a with hs_def
  have hs_eq : s = ∑ a, m a := rfl
  have hm_le_p : ∀ a, m a ≤ p a := fun a => by rw [hm_eq a]; exact min_le_left _ _
  have hm_le_q : ∀ a, m a ≤ q a := fun a => by rw [hm_eq a]; exact min_le_right _ _
  have hm_ne : ∀ a, m a ≠ ⊤ :=
    fun a => ne_top_of_le_ne_top (pmf_ne_top p a) (hm_le_p a)
  have hs_le : s ≤ 1 := by
    rw [hs_eq]
    calc ∑ a, m a ≤ ∑ a, p a := sum_le_sum fun a _ => hm_le_p a
      _ = 1 := pmf_sum_eq_one p
  have hs_ne : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hs_le
  have hm_toReal : ∀ a, (m a).toReal = min (p a).toReal (q a).toReal := by
    intro a
    by_cases hle : p a ≤ q a
    · have hle' : (p a).toReal ≤ (q a).toReal :=
        (ENNReal.toReal_le_toReal (pmf_ne_top p a) (pmf_ne_top q a)).mpr hle
      rw [hm_eq a, min_eq_left hle, min_eq_left hle']
    · have hlt : q a < p a := lt_of_not_ge hle
      have hle' : (q a).toReal ≤ (p a).toReal :=
        (ENNReal.toReal_le_toReal (pmf_ne_top q a) (pmf_ne_top p a)).mpr hlt.le
      rw [hm_eq a, min_eq_right hlt.le, min_eq_right hle']
  -- Real mass sums.
  have hsum_p : ∑ a, (p a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => pmf_ne_top p a), pmf_sum_eq_one p,
      ENNReal.toReal_one]
  have hsum_q : ∑ a, (q a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => pmf_ne_top q a), pmf_sum_eq_one q,
      ENNReal.toReal_one]
  have hsum_m : ∑ a, (m a).toReal = s.toReal := by
    rw [hs_eq, ← ENNReal.toReal_sum (fun a _ => hm_ne a)]
  -- tvDist in terms of s.
  have htv : tvDist p q = 1 - s.toReal := by
    have hsum_abs : ∑ a, |(p a).toReal - (q a).toReal| = 2 - 2 * s.toReal := by
      have e : ∀ a, |(p a).toReal - (q a).toReal|
          = ((p a).toReal + (q a).toReal) - 2 * (m a).toReal := by
        intro a
        rw [hm_toReal a]
        exact abs_sub_eq_add_sub_two_min
      simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum_p, hsum_q,
        ← Finset.mul_sum, hsum_m]
      ring
    unfold tvDist
    rw [hsum_abs]
    ring
  by_cases hs1 : s = 1
  · -- Case A: p = q, diagonal coupling.
    have hpq_toReal : ∀ a, (p a).toReal = (q a).toReal := by
      have hmp : ∀ a, (m a).toReal = (p a).toReal := by
        have hle : ∀ a ∈ univ, (m a).toReal ≤ (p a).toReal := fun a _ =>
          (ENNReal.toReal_le_toReal (hm_ne a) (pmf_ne_top p a)).mpr (hm_le_p a)
        have heq : ∑ a, (m a).toReal = ∑ a, (p a).toReal := by
          rw [hsum_m, hsum_p, hs1, ENNReal.toReal_one]
        exact fun a => (Finset.sum_eq_sum_iff_of_le hle).mp heq a (mem_univ a)
      have hmq : ∀ a, (m a).toReal = (q a).toReal := by
        have hle : ∀ a ∈ univ, (m a).toReal ≤ (q a).toReal := fun a _ =>
          (ENNReal.toReal_le_toReal (hm_ne a) (pmf_ne_top q a)).mpr (hm_le_q a)
        have heq : ∑ a, (m a).toReal = ∑ a, (q a).toReal := by
          rw [hsum_m, hsum_q, hs1, ENNReal.toReal_one]
        exact fun a => (Finset.sum_eq_sum_iff_of_le hle).mp heq a (mem_univ a)
      intro a
      rw [← hmp a, hmq a]
    have hpq : ∀ a, p a = q a := by
      intro a
      apply le_antisymm
      · exact (ENNReal.toReal_le_toReal (pmf_ne_top p a) (pmf_ne_top q a)).mp
          (le_of_eq (hpq_toReal a))
      · exact (ENNReal.toReal_le_toReal (pmf_ne_top q a) (pmf_ne_top p a)).mp
          (le_of_eq (hpq_toReal a).symm)
    set f : α × α → ENNReal := fun x => if x.1 = x.2 then p x.1 else 0 with hf_def
    have hdiag : ∀ a : α, ∑ b, f (a, b) = p a := by
      intro a
      have e : ∀ b, f (a, b) = (if a = b then p a else 0) := fun b => rfl
      simp_rw [e]
      rw [Finset.sum_ite_eq univ a (fun _ => p a)]
      simp
    have hdiag' : ∀ b : α, ∑ a, f (a, b) = q b := by
      intro b
      have e : ∀ a, f (a, b) = (if a = b then p a else 0) := fun a => rfl
      simp_rw [e]
      rw [Finset.sum_ite_eq' univ b p]
      simp [hpq b]
    have htot : ∑ x, f x = 1 := by
      rw [Fintype.sum_prod_type]
      simp_rw [hdiag]
      exact pmf_sum_eq_one p
    refine ⟨PMF.ofFintype f htot, ⟨?_, ?_⟩, ?_⟩
    · intro a
      simp only [PMF.ofFintype_apply]
      exact hdiag a
    · intro b
      simp only [PMF.ofFintype_apply]
      exact hdiag' b
    · have hD0 : ∀ x ∈ univ.filter (fun x : α × α => x.1 ≠ x.2), f x = 0 := by
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        have e : f x = (if x.1 = x.2 then p x.1 else 0) := rfl
        rw [e]
        simp [hx]
      have hmeas : ((PMF.ofFintype f htot).toMeasure {x : α × α | x.1 ≠ x.2}).toReal
          = 0 := by
        have h1 : (PMF.ofFintype f htot).toMeasure {x : α × α | x.1 ≠ x.2}
            = ∑ x, {x : α × α | x.1 ≠ x.2}.indicator (⇑(PMF.ofFintype f htot)) x := by
          rw [PMF.toMeasure_apply _ MeasurableSet.of_discrete, tsum_fintype]
        rw [h1, ENNReal.toReal_sum (fun x _ => by
          by_cases hxm : x ∈ {x : α × α | x.1 ≠ x.2}
          · rw [Set.indicator_of_mem hxm]; exact pmf_ne_top _ x
          · rw [Set.indicator_of_notMem hxm]; exact ENNReal.zero_ne_top)]
        apply Finset.sum_eq_zero
        intro x _
        by_cases hxm : x ∈ {x : α × α | x.1 ≠ x.2}
        · rw [Set.indicator_of_mem hxm, PMF.ofFintype_apply]
          have hx : x.1 ≠ x.2 := hxm
          have hfx : f x = 0 := hD0 x (by simp [hx])
          rw [hfx, ENNReal.toReal_zero]
        · rw [Set.indicator_of_notMem hxm, ENNReal.toReal_zero]
      have htv0 : tvDist p q = 0 := by
        rw [htv, hs1, ENNReal.toReal_one, sub_self]
      rw [hmeas, htv0]
  · -- Case B: s ≠ 1, mixture construction.
    set t : ENNReal := 1 - s with ht_def
    have ht_eq : t = 1 - s := rfl
    have ht_ne0 : t ≠ 0 := by
      rw [ht_eq]
      intro hcon
      rw [tsub_eq_zero_iff_le] at hcon
      exact hs1 (le_antisymm hs_le hcon)
    have ht_ne : t ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [ht_eq]; exact tsub_le_self)
    set g : α → ENNReal := fun a => p a - m a with hg_def
    have hg_eq : ∀ a, g a = p a - m a := fun a => rfl
    set h : α → ENNReal := fun b => q b - m b with hh_def
    have hh_eq : ∀ b, h b = q b - m b := fun b => rfl
    have hg_ne : ∀ a, g a ≠ ⊤ := fun a => ne_top_of_le_ne_top (pmf_ne_top p a)
      (by rw [hg_eq a]; exact tsub_le_self)
    have hh_ne : ∀ b, h b ≠ ⊤ := fun b => ne_top_of_le_ne_top (pmf_ne_top q b)
      (by rw [hh_eq b]; exact tsub_le_self)
    have hsum_g : ∑ a, g a = t := by
      have hadd : (∑ a, g a) + s = 1 := by
        have e : ∀ a, g a + m a = p a := fun a => by
          rw [hg_eq a]; exact tsub_add_cancel_of_le (hm_le_p a)
        calc (∑ a, g a) + s = ∑ a, (g a + m a) := by
                rw [hs_eq, Finset.sum_add_distrib]
          _ = ∑ a, p a := sum_congr rfl fun a _ => e a
          _ = 1 := pmf_sum_eq_one p
      have hne : (∑ a, g a) ≠ ⊤ := by
        intro hcon
        rw [hcon, top_add] at hadd
        exact ENNReal.one_ne_top hadd.symm
      rw [ht_eq]
      exact ennreal_eq_sub_of_add_eq hne hs_ne hs_le hadd
    have hsum_h : ∑ b, h b = t := by
      have hadd : (∑ b, h b) + s = 1 := by
        have e : ∀ b, h b + m b = q b := fun b => by
          rw [hh_eq b]; exact tsub_add_cancel_of_le (hm_le_q b)
        calc (∑ b, h b) + s = ∑ b, (h b + m b) := by
                rw [hs_eq, Finset.sum_add_distrib]
          _ = ∑ b, q b := sum_congr rfl fun b _ => e b
          _ = 1 := pmf_sum_eq_one q
      have hne : (∑ b, h b) ≠ ⊤ := by
        intro hcon
        rw [hcon, top_add] at hadd
        exact ENNReal.one_ne_top hadd.symm
      rw [ht_eq]
      exact ennreal_eq_sub_of_add_eq hne hs_ne hs_le hadd
    set f : α × α → ENNReal := fun x =>
      (if x.1 = x.2 then m x.1 else 0) + g x.1 * h x.2 / t with hf_def
    have hf_eq : ∀ a b, f (a, b)
        = (if a = b then m a else 0) + g a * h b / t := fun a b => rfl
    have hrow : ∀ a : α, ∑ b, f (a, b) = p a := by
      intro a
      simp_rw [hf_eq a]
      rw [Finset.sum_add_distrib]
      have h1 : ∑ b, (if a = b then m a else 0) = m a := by
        rw [Finset.sum_ite_eq univ a (fun _ => m a)]
        simp
      have h2 : ∑ b, (g a * h b / t) = g a := by
        have e : ∀ b, g a * h b / t = g a * (h b / t) := fun b => mul_div_assoc _ _ _
        have hdiv : ∑ b, (h b / t) = (∑ b, h b) / t := by
          simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
        simp_rw [e, ← Finset.mul_sum, hdiv, hsum_h, ← mul_div_assoc,
          ENNReal.mul_div_cancel_right ht_ne0 ht_ne]
      rw [h1, h2, hg_eq a]
      exact add_tsub_cancel_of_le (hm_le_p a)
    have hcol : ∀ b : α, ∑ a, f (a, b) = q b := by
      intro b
      simp_rw [hf_eq]
      rw [Finset.sum_add_distrib]
      have h1 : ∑ a, (if a = b then m a else 0) = m b := by
        rw [Finset.sum_ite_eq' univ b m]
        simp
      have h2 : ∑ a, (g a * h b / t) = h b := by
        have e : ∀ a, g a * h b / t = g a * (h b / t) := fun a => mul_div_assoc _ _ _
        simp_rw [e, ← Finset.sum_mul, hsum_g]
        exact ENNReal.mul_div_cancel ht_ne0 ht_ne
      rw [h1, h2, hh_eq b]
      exact add_tsub_cancel_of_le (hm_le_q b)
    have htot : ∑ x, f x = 1 := by
      rw [Fintype.sum_prod_type]
      simp_rw [hrow]
      exact pmf_sum_eq_one p
    refine ⟨PMF.ofFintype f htot, ⟨?_, ?_⟩, ?_⟩
    · intro a
      simp only [PMF.ofFintype_apply]
      exact hrow a
    · intro b
      simp only [PMF.ofFintype_apply]
      exact hcol b
    · -- Real residuals and their sums.
      set G : α → ℝ := fun a => (g a).toReal with hG_def
      set H : α → ℝ := fun b => (h b).toReal with hH_def
      set T : ℝ := t.toReal with hT_def
      have hG_eq : ∀ a, G a = (g a).toReal := fun a => rfl
      have hH_eq : ∀ b, H b = (h b).toReal := fun b => rfl
      have hT_eq : T = t.toReal := rfl
      have hT_pos : 0 < T := by
        rw [hT_eq]; exact ENNReal.toReal_pos ht_ne0 ht_ne
      have hT0 : T ≠ 0 := ne_of_gt hT_pos
      have hsum_G : ∑ a, G a = T := by
        simp_rw [hG_eq, hT_eq, ← ENNReal.toReal_sum (fun a _ => hg_ne a), hsum_g]
      have hsum_H : ∑ b, H b = T := by
        simp_rw [hH_eq, hT_eq, ← ENNReal.toReal_sum (fun b _ => hh_ne b), hsum_h]
      have hGH0 : ∀ a, G a * H a = 0 := by
        intro a
        have hGa : G a = (p a).toReal - (m a).toReal := by
          rw [hG_eq a, hg_eq a, ENNReal.toReal_sub_of_le (hm_le_p a) (pmf_ne_top p a)]
        have hHa : H a = (q a).toReal - (m a).toReal := by
          rw [hH_eq a, hh_eq a, ENNReal.toReal_sub_of_le (hm_le_q a) (pmf_ne_top q a)]
        rw [hm_toReal a] at hGa hHa
        by_cases hle : (p a).toReal ≤ (q a).toReal
        · rw [min_eq_left hle] at hGa
          rw [hGa]
          simp
        · have hle' : (q a).toReal ≤ (p a).toReal := le_of_not_ge hle
          rw [min_eq_right hle'] at hHa
          rw [hHa]
          simp
      have hsum_GH0 : ∑ a, G a * H a = 0 := Finset.sum_eq_zero (fun a _ => hGH0 a)
      have h2 : ∑ x ∈ univ.filter (fun x : α × α => x.1 ≠ x.2), G x.1 * H x.2
          = T * T := by
        rw [sum_offdiag_eq]
        have hsplit : (∑ a, G a) * (∑ b, H b)
            = ∑ a, G a * H a + ∑ a, ∑ b ∈ univ.erase a, G a * H b := by
          rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
          apply sum_congr rfl
          intro a _
          exact (Finset.add_sum_erase _ _ (mem_univ a)).symm
        rw [hsum_G, hsum_H, hsum_GH0, zero_add] at hsplit
        exact hsplit.symm
      have hDsum : ∑ x ∈ univ.filter (fun x : α × α => x.1 ≠ x.2), (G x.1 * H x.2 / T)
          = T := by
        have h1 : ∑ x ∈ univ.filter (fun x : α × α => x.1 ≠ x.2), (G x.1 * H x.2 / T)
            = (∑ x ∈ univ.filter (fun x : α × α => x.1 ≠ x.2), G x.1 * H x.2) / T := by
          simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
        rw [h1, h2]
        field_simp
      have hmeas : ((PMF.ofFintype f htot).toMeasure {x : α × α | x.1 ≠ x.2}).toReal
          = ∑ x ∈ univ.filter (fun x : α × α => x.1 ≠ x.2), (G x.1 * H x.2 / T) := by
        have h1 : (PMF.ofFintype f htot).toMeasure {x : α × α | x.1 ≠ x.2}
            = ∑ x, {x : α × α | x.1 ≠ x.2}.indicator (⇑(PMF.ofFintype f htot)) x := by
          rw [PMF.toMeasure_apply _ MeasurableSet.of_discrete, tsum_fintype]
        rw [h1, ENNReal.toReal_sum (fun x _ => by
          by_cases hxm : x ∈ {x : α × α | x.1 ≠ x.2}
          · rw [Set.indicator_of_mem hxm]; exact pmf_ne_top _ x
          · rw [Set.indicator_of_notMem hxm]; exact ENNReal.zero_ne_top)]
        rw [Finset.sum_filter]
        apply sum_congr rfl
        intro x _
        by_cases hx : x.1 ≠ x.2
        · have hxm : x ∈ {x : α × α | x.1 ≠ x.2} := hx
          rw [Set.indicator_of_mem hxm, PMF.ofFintype_apply]
          have hfx : f x = g x.1 * h x.2 / t := by
            have e : f x = (if x.1 = x.2 then m x.1 else 0) + g x.1 * h x.2 / t := rfl
            rw [e]
            simp [hx]
          rw [hfx, ENNReal.toReal_div, ENNReal.toReal_mul]
          simp [hx, hG_eq, hH_eq, hT_eq]
        · have hxm : x ∉ {x : α × α | x.1 ≠ x.2} := hx
          rw [Set.indicator_of_notMem hxm]
          simp [hx]
      have hTtv : T = tvDist p q := by
        rw [hT_eq, ht_eq, ENNReal.toReal_sub_of_le hs_le ENNReal.one_ne_top,
          ENNReal.toReal_one, htv]
      rw [hmeas, hDsum, hTtv]
