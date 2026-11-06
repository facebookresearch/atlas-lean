/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.Tauto

namespace MetaMathlibExt

@[expose] public section

private lemma measSet_inf_true {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hmeas : ∀ i, Measurable (X i))
    (s : Finset ℕ) :
    MeasurableSet (s.inf fun i => {ω | X i ω = true}) := by
  rw [Finset.inf_eq_iInf]
  apply MeasurableSet.biInter (Finset.finite_toSet s).countable
  intro b _
  exact hmeas b (measurableSet_singleton true)

private lemma measSet_inf_false {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hmeas : ∀ i, Measurable (X i))
    (s : Finset ℕ) :
    MeasurableSet (s.inf fun i => {ω | X i ω = false}) := by
  rw [Finset.inf_eq_iInf]
  apply MeasurableSet.biInter (Finset.finite_toSet s).countable
  intro b _
  exact hmeas b (measurableSet_singleton false)

private lemma meas_inf_true {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (p : ENNReal)
    (hmarg : ∀ i, μ {ω | X i ω = true} = p)
    (hindep : ∀ s : Finset ℕ, s.Nonempty →
      μ (s.inf fun i => {ω | X i ω = true}) =
        s.prod fun i => μ {ω | X i ω = true})
    (s : Finset ℕ) :
    μ (s.inf fun i => {ω | X i ω = true}) = p ^ s.card := by
  by_cases hs : s.Nonempty
  · have hprod : s.prod (fun i => μ {ω | X i ω = true}) = p ^ s.card := by
      have h1 : s.prod (fun i => μ {ω | X i ω = true}) = s.prod (fun _ => p) := by
        apply Finset.prod_congr rfl
        intro i _
        exact hmarg i
      rw [h1, Finset.prod_const]
    rw [hindep s hs, hprod]
  · have hcard : s.card = 0 := by
      have hpos : ¬ 0 < s.card := by
        rw [Finset.card_pos]
        exact hs
      omega
    have hs0 : s = ∅ := Finset.card_eq_zero.mp hcard
    subst hs0
    simp

private lemma choose_succ_succ_two (n k : ℕ) :
    (n + 2).choose (k + 2) = n.choose k + 2 * n.choose (k + 1) + n.choose (k + 2) := by
  have h1 : n + 2 = (n + 1) + 1 := by ring
  have h2 : k + 2 = (k + 1) + 1 := by ring
  rw [h1, h2, Nat.choose_succ_succ, Nat.choose_succ_succ, Nat.choose_succ_succ]
  ring

private lemma condorcet_step (r : ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 2),
      (((2 * m + 3).choose (m + 2 + j) : ℕ) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j))
    = (∑ j ∈ Finset.range (m + 1),
      (((2 * m + 1).choose (m + 1 + j) : ℕ) : ℝ) * r ^ (m + 1 + j) * (1 - r) ^ (m - j))
    + (((2 * m + 1).choose m : ℕ) : ℝ) * (r * (1 - r)) ^ (m + 1) * (2 * r - 1) := by
  have hP : ∀ j ∈ Finset.range (m + 2),
      ((((2 * m + 3).choose (m + 2 + j) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j)
      = ((((2 * m + 1).choose (m + j) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j)
      + 2 * (((((2 * m + 1).choose (m + j + 1) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j))
      + (((2 * m + 1).choose (m + j + 2) : ℕ) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j) := by
    intro j _
    have e1 : 2 * m + 3 = (2 * m + 1) + 2 := by ring
    have e2 : m + 2 + j = (m + j) + 2 := by ring
    rw [e1, e2, choose_succ_succ_two]
    push_cast
    ring
  have hpow1 : ∀ j, r ^ (m + 2 + j) = r ^ 2 * r ^ (m + j) := by
    intro j
    have e : m + 2 + j = 2 + (m + j) := by omega
    rw [e, pow_add]
  have step1 :
      (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 3).choose (m + 2 + j) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j))
      = (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 1).choose (m + j) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j))
      + (∑ j ∈ Finset.range (m + 2),
        2 * (((((2 * m + 1).choose (m + j + 1) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j)))
      + (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 1).choose (m + j + 2) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j hj => hP j hj)
  have hP1 :
      (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 1).choose (m + j) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j))
      = r ^ 2 * (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 1).choose (m + j) : ℕ)) : ℝ) * r ^ (m + j) * (1 - r) ^ (m + 1 - j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hpow1 j]
    ring
  have hP2 :
      (∑ j ∈ Finset.range (m + 2),
        2 * (((((2 * m + 1).choose (m + j + 1) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j)))
      = (2 * (r * (1 - r))) * (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 1).choose (m + j + 1) : ℕ)) : ℝ) * r ^ (m + 1 + j) * (1 - r) ^ (m - j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjm : j = m + 1
    · subst hjm
      have hc : (2 * m + 1).choose (m + (m + 1) + 1) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      rw [hc]
      simp
    · have hlt : j < m + 1 := by
        have h := Finset.mem_range.mp hj
        omega
      have e : m + 2 + j = (m + 1 + j) + 1 := by omega
      have hq : (1 - r) ^ (m + 1 - j) = (1 - r) * (1 - r) ^ (m - j) := by
        have eq : m + 1 - j = (m - j) + 1 := by omega
        rw [eq, pow_succ]
        ring
      rw [hq, e, pow_succ]
      ring
  have hP3 :
      (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 1).choose (m + j + 2) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j))
      = (1 - r) ^ 2 * (∑ j ∈ Finset.range m,
        ((((2 * m + 1).choose (m + 2 + j) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m - 1 - j)) := by
    have e1 : m + 2 = (m + 1) + 1 := by omega
    rw [e1, Finset.sum_range_succ]
    have hZ1 : ((((2 * m + 1).choose (m + (m + 1) + 2) : ℕ)) : ℝ)
        * r ^ (m + 2 + (m + 1)) * (1 - r) ^ (m + 1 - (m + 1)) = 0 := by
      have hc : (2 * m + 1).choose (m + (m + 1) + 2) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      rw [hc]
      simp
    rw [hZ1, add_zero, Finset.sum_range_succ]
    have hZ0 : ((((2 * m + 1).choose (m + m + 2) : ℕ)) : ℝ)
        * r ^ (m + 2 + m) * (1 - r) ^ (m + 1 - m) = 0 := by
      have hc : (2 * m + 1).choose (m + m + 2) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      rw [hc]
      simp
    rw [hZ0, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hlt : j < m := Finset.mem_range.mp hj
    have i1 : m + j + 2 = m + 2 + j := by omega
    have i2 : m + 1 - j = 2 + (m - 1 - j) := by omega
    rw [i1, i2, pow_add (1 - r) 2 (m - 1 - j)]
    ring
  have hS1 :
      (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 1).choose (m + j) : ℕ)) : ℝ) * r ^ (m + j) * (1 - r) ^ (m + 1 - j))
      = ((((2 * m + 1).choose m : ℕ)) : ℝ) * r ^ m * (1 - r) ^ (m + 1)
      + (∑ j ∈ Finset.range (m + 1),
        ((((2 * m + 1).choose (m + 1 + j) : ℕ)) : ℝ) * r ^ (m + 1 + j) * (1 - r) ^ (m - j)) := by
    have e : m + 2 = (m + 1) + 1 := by omega
    rw [e, Finset.sum_range_succ']
    have hzero : ((((2 * m + 1).choose (m + 0) : ℕ)) : ℝ)
        * r ^ (m + 0) * (1 - r) ^ (m + 1 - 0)
        = ((((2 * m + 1).choose m : ℕ)) : ℝ) * r ^ m * (1 - r) ^ (m + 1) := by
      simp
    have htail : (∑ k ∈ Finset.range (m + 1),
        ((((2 * m + 1).choose (m + (k + 1)) : ℕ)) : ℝ) * r ^ (m + (k + 1)) * (1 - r) ^ (m + 1 - (k + 1)))
        = (∑ j ∈ Finset.range (m + 1),
        ((((2 * m + 1).choose (m + 1 + j) : ℕ)) : ℝ) * r ^ (m + 1 + j) * (1 - r) ^ (m - j)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hlt : k < m + 1 := Finset.mem_range.mp hk
      have i1 : m + (k + 1) = m + 1 + k := by omega
      have i2 : m + 1 - (k + 1) = m - k := by omega
      rw [i1, i2]
    rw [hzero, htail]
    exact add_comm _ _
  have hS2 :
      (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 1).choose (m + j + 1) : ℕ)) : ℝ) * r ^ (m + 1 + j) * (1 - r) ^ (m - j))
      = (∑ j ∈ Finset.range (m + 1),
        ((((2 * m + 1).choose (m + 1 + j) : ℕ)) : ℝ) * r ^ (m + 1 + j) * (1 - r) ^ (m - j)) := by
    have e : m + 2 = (m + 1) + 1 := by omega
    rw [e, Finset.sum_range_succ]
    have htop : ((((2 * m + 1).choose (m + (m + 1) + 1) : ℕ)) : ℝ)
        * r ^ (m + 1 + (m + 1)) * (1 - r) ^ (m - (m + 1)) = 0 := by
      have hc : (2 * m + 1).choose (m + (m + 1) + 1) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      rw [hc]
      simp
    rw [htop, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    have i1 : m + j + 1 = m + 1 + j := by omega
    rw [i1]
  have hC : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    have hle : m + 1 ≤ 2 * m + 1 := by omega
    have hsub : 2 * m + 1 - (m + 1) = m := by omega
    have hsym := Nat.choose_symm hle
    rw [hsub] at hsym
    exact hsym.symm
  have hTm :
      (∑ j ∈ Finset.range (m + 1),
        ((((2 * m + 1).choose (m + 1 + j) : ℕ)) : ℝ) * r ^ (m + 1 + j) * (1 - r) ^ (m - j))
      = ((((2 * m + 1).choose m : ℕ)) : ℝ) * r ^ (m + 1) * (1 - r) ^ m
      + (∑ j ∈ Finset.range m,
        ((((2 * m + 1).choose (m + 2 + j) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m - 1 - j)) := by
    rw [Finset.sum_range_succ']
    have hzero : ((((2 * m + 1).choose (m + 1 + 0) : ℕ)) : ℝ)
        * r ^ (m + 1 + 0) * (1 - r) ^ (m - 0)
        = ((((2 * m + 1).choose m : ℕ)) : ℝ) * r ^ (m + 1) * (1 - r) ^ m := by
      have e1 : m + 1 + 0 = m + 1 := by omega
      have e2 : m - 0 = m := by omega
      rw [e1, e2, hC]
    have htail : (∑ k ∈ Finset.range m,
        ((((2 * m + 1).choose (m + 1 + (k + 1)) : ℕ)) : ℝ) * r ^ (m + 1 + (k + 1)) * (1 - r) ^ (m - (k + 1)))
        = (∑ j ∈ Finset.range m,
        ((((2 * m + 1).choose (m + 2 + j) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m - 1 - j)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hlt : k < m := Finset.mem_range.mp hk
      have i1 : m + 1 + (k + 1) = m + 2 + k := by omega
      have i2 : m - (k + 1) = m - 1 - k := by omega
      rw [i1, i2]
    rw [hzero, htail]
    exact add_comm _ _
  have hT :
      (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 3).choose (m + 2 + j) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m + 1 - j))
      = r ^ 2 * (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 1).choose (m + j) : ℕ)) : ℝ) * r ^ (m + j) * (1 - r) ^ (m + 1 - j))
      + (2 * (r * (1 - r))) * (∑ j ∈ Finset.range (m + 2),
        ((((2 * m + 1).choose (m + j + 1) : ℕ)) : ℝ) * r ^ (m + 1 + j) * (1 - r) ^ (m - j))
      + (1 - r) ^ 2 * (∑ j ∈ Finset.range m,
        ((((2 * m + 1).choose (m + 2 + j) : ℕ)) : ℝ) * r ^ (m + 2 + j) * (1 - r) ^ (m - 1 - j)) := by
    rw [step1, hP1, hP2, hP3]
  have e1 : r ^ 2 * r ^ m = r * r ^ (m + 1) := by
    have h : 2 + m = (m + 1) + 1 := by omega
    calc r ^ 2 * r ^ m = r ^ (2 + m) := by rw [pow_add]
      _ = r * r ^ (m + 1) := by rw [h, pow_succ']
  have e2 : (1 - r) ^ 2 * (1 - r) ^ m = (1 - r) * (1 - r) ^ (m + 1) := by
    have h : 2 + m = (m + 1) + 1 := by omega
    calc (1 - r) ^ 2 * (1 - r) ^ m = (1 - r) ^ (2 + m) := by rw [pow_add]
      _ = (1 - r) * (1 - r) ^ (m + 1) := by rw [h, pow_succ']
  have hfin : r ^ 2 * (((((2 * m + 1).choose m : ℕ)) : ℝ) * r ^ m * (1 - r) ^ (m + 1))
      - (1 - r) ^ 2 * (((((2 * m + 1).choose m : ℕ)) : ℝ) * r ^ (m + 1) * (1 - r) ^ m)
      = ((((2 * m + 1).choose m : ℕ)) : ℝ) * (r * (1 - r)) ^ (m + 1) * (2 * r - 1) := by
    rw [mul_pow]
    linear_combination
      ((((2 * m + 1).choose m : ℕ)) : ℝ) * (1 - r) ^ (m + 1) * e1
      - ((((2 * m + 1).choose m : ℕ)) : ℝ) * r ^ (m + 1) * e2
  linear_combination hT + r ^ 2 * hS1 + (2 * (r * (1 - r))) * hS2 - (1 - r) ^ 2 * hTm + hfin

private lemma true_union_false {Ω : Type*} (X : ℕ → Ω → Bool) (j : ℕ) :
    {ω | X j ω = true} ∪ {ω | X j ω = false} = Set.univ := by
  ext ω
  simp

private lemma true_inter_false {Ω : Type*} (X : ℕ → Ω → Bool) (j : ℕ) :
    Disjoint {ω | X j ω = true} {ω | X j ω = false} := by
  apply Set.disjoint_left.mpr
  intro ω h1 h2
  simp at h1 h2
  rw [h1] at h2
  simp at h2

private lemma sdiff_erase_eq {s t : Finset ℕ} {j : ℕ} :
    (s.erase j) \ t = (s \ t).erase j := by
  ext x
  simp [Finset.mem_erase, Finset.mem_sdiff]
  tauto

private lemma insert_sdiff_eq {s t : Finset ℕ} {j : ℕ} :
    s \ insert j t = (s \ t).erase j := by
  ext x
  simp [Finset.mem_erase, Finset.mem_sdiff]
  tauto

private lemma pat_split {Ω : Type*} (X : ℕ → Ω → Bool) (s t : Finset ℕ) (j : ℕ)
    (hjmem : j ∈ s \ t) :
    let E_mid := (t.inf fun i => {ω : Ω | X i ω = true}) ∩
      (((s.erase j) \ t).inf fun i => {ω : Ω | X i ω = false})
    let E1 := (t.inf fun i => {ω : Ω | X i ω = true}) ∩
      ((s \ t).inf fun i => {ω : Ω | X i ω = false})
    let E2 := ((insert j t).inf fun i => {ω : Ω | X i ω = true}) ∩
      ((s \ insert j t).inf fun i => {ω : Ω | X i ω = false})
    E_mid = E1 ∪ E2 ∧ Disjoint E1 E2 := by
  have hjs : j ∈ s := (Finset.mem_sdiff.mp hjmem).1
  have hjt : j ∉ t := (Finset.mem_sdiff.mp hjmem).2
  have hsdiff : s \ t = insert j ((s \ t).erase j) := (Finset.insert_erase hjmem).symm
  have hmid_eq : (s.erase j) \ t = (s \ t).erase j := sdiff_erase_eq
  have hE2sdiff : s \ insert j t = (s.erase j) \ t := by
    rw [insert_sdiff_eq, hmid_eq]
  have hinf_false : ((s \ t).inf fun i => {ω : Ω | X i ω = false})
      = {ω : Ω | X j ω = false} ∩ (((s.erase j) \ t).inf fun i => {ω : Ω | X i ω = false}) := by
    conv_lhs => rw [hsdiff, ← hmid_eq]
    rw [Finset.inf_insert]
    rfl
  have hinf_true : ((insert j t).inf fun i => {ω : Ω | X i ω = true})
      = {ω : Ω | X j ω = true} ∩ (t.inf fun i => {ω : Ω | X i ω = true}) := by
    rw [Finset.inf_insert]
    rfl
  have hU := true_union_false (Ω := Ω) X j
  have hD := true_inter_false (Ω := Ω) X j
  constructor
  · show (t.inf fun i => {ω : Ω | X i ω = true}) ∩
      (((s.erase j) \ t).inf fun i => {ω : Ω | X i ω = false}) = _
    rw [hinf_false, hE2sdiff, hinf_true]
    ext ω
    have hmem : ω ∈ ({ω : Ω | X j ω = true} ∪ {ω : Ω | X j ω = false}) := by
      rw [hU]
      trivial
    simp only [Set.mem_inter_iff, Set.mem_union] at hmem ⊢
    tauto
  · show Disjoint _ _
    rw [hinf_false, hE2sdiff, hinf_true]
    apply Set.disjoint_left.mpr
    intro ω h1 h2
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at h1 h2
    obtain ⟨_, hf, _⟩ := h1
    obtain ⟨⟨ht, _⟩, _⟩ := h2
    rw [hf] at ht
    simp at ht

private lemma condorcet_tail_gt (r : ℝ) (hr1 : 1 / 2 < r) (hr2 : r < 1) (m : ℕ) (hm : 1 ≤ m) :
    r < ∑ j ∈ Finset.range (m + 1),
      ((((2 * m + 1).choose (m + 1 + j) : ℕ)) : ℝ) * r ^ (m + 1 + j) * (1 - r) ^ (m - j) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have h2r : (0 : ℝ) < 2 * r - 1 := by linarith
  induction m, hm using Nat.le_induction with
  | base =>
    have hpos : 0 < r * (2 * r - 1) * (1 - r) := mul_pos (mul_pos hr0 h2r) h1r
    show r < ∑ j ∈ Finset.range (1 + 1),
      ((((3).choose (2 + j) : ℕ)) : ℝ) * r ^ (2 + j) * (1 - r) ^ (1 - j)
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have c0 : (3).choose (2 + 0) = 3 := by decide
    have c1 : (3).choose (2 + 1) = 1 := by decide
    have p0 : (2 + 0 : ℕ) = 2 := by omega
    have p1 : (1 - 0 : ℕ) = 1 := by omega
    have p2 : (2 + 1 : ℕ) = 3 := by omega
    have p3 : (1 - 1 : ℕ) = 0 := by omega
    rw [c0, c1, p0, p1, p2, p3]
    push_cast
    rw [pow_zero]
    have heq : (3 : ℝ) * r ^ 2 * (1 - r) ^ 1 + 1 * r ^ 3 * 1
        = r + r * (2 * r - 1) * (1 - r) := by ring
    linarith
  | succ n hn ih =>
    have e1 : n + 1 + 1 = n + 2 := by omega
    have e2 : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
    rw [e1, e2, condorcet_step r n]
    have hCpos : (0 : ℝ) < ((((2 * n + 1).choose n : ℕ)) : ℝ) := by
      apply Nat.cast_pos.mpr
      exact Nat.choose_pos (by omega)
    have hpow : (0 : ℝ) < (r * (1 - r)) ^ (n + 1) := pow_pos (mul_pos hr0 h1r) _
    have hextra : 0 < ((((2 * n + 1).choose n : ℕ)) : ℝ) * (r * (1 - r)) ^ (n + 1) * (2 * r - 1) :=
      mul_pos (mul_pos hCpos hpow) h2r
    linarith

private lemma pattern_aux {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (p : ENNReal)
    (hmeas : ∀ i, Measurable (X i))
    (hmarg : ∀ i, μ {ω | X i ω = true} = p)
    (hindep : ∀ s : Finset ℕ, s.Nonempty →
      μ (s.inf fun i => {ω | X i ω = true}) =
        s.prod fun i => μ {ω | X i ω = true})
    (hp_le : p ≤ 1) (hp_top : p ≠ ⊤) (h1p_top : 1 - p ≠ ⊤)
    (k : ℕ) (s t : Finset ℕ) (hsub : t ⊆ s) (hcard : (s \ t).card = k) :
    μ ((t.inf fun i => {ω | X i ω = true}) ∩
      ((s \ t).inf fun i => {ω | X i ω = false})) =
      p ^ t.card * (1 - p) ^ k := by
  induction k generalizing s t with
  | zero =>
    have hst : s \ t = ∅ := Finset.card_eq_zero.mp hcard
    have hseq : s ⊆ t := Finset.sdiff_eq_empty_iff_subset.mp hst
    have hsteq : s = t := Finset.Subset.antisymm hseq hsub
    subst hsteq
    have hsd : s \ s = ∅ := by simp
    have htop : ((s.inf fun i => {ω | X i ω = true}) ∩ ⊤)
        = s.inf fun i => {ω | X i ω = true} := by simp
    rw [hsd, Finset.inf_empty, htop,
      meas_inf_true X p hmarg hindep s, pow_zero, mul_one]
  | succ k ih =>
    have hpos : 0 < (s \ t).card := by omega
    have hne : (s \ t).Nonempty := Finset.card_pos.mp hpos
    obtain ⟨j, hjmem⟩ := hne
    have hjs : j ∈ s := (Finset.mem_sdiff.mp hjmem).1
    have hjt : j ∉ t := (Finset.mem_sdiff.mp hjmem).2
    have hsub_erase : t ⊆ s.erase j := by
      intro x hx
      simp [Finset.mem_erase]
      constructor
      · intro hxj
        subst hxj
        exact absurd hx hjt
      · exact hsub hx
    have hcard_mid : ((s.erase j) \ t).card = k := by
      have h1 : (s.erase j) \ t = (s \ t).erase j := sdiff_erase_eq
      rw [h1]
      have h2 := Finset.card_erase_add_one hjmem
      omega
    have hsub_ins : insert j t ⊆ s := by
      apply Finset.insert_subset hjs hsub
    have hcard_ins : (s \ insert j t).card = k := by
      have h1 : s \ insert j t = (s \ t).erase j := insert_sdiff_eq
      rw [h1]
      have h2 := Finset.card_erase_add_one hjmem
      omega
    have hcard_ins_t : (insert j t).card = t.card + 1 :=
      Finset.card_insert_of_notMem hjt
    have ih_mid := ih (s.erase j) t hsub_erase hcard_mid
    have ih_ins := ih s (insert j t) hsub_ins hcard_ins
    have hsplit := pat_split (Ω := Ω) X s t j hjmem
    simp only at hsplit
    obtain ⟨heq, hdisj⟩ := hsplit
    have hmeas2 : MeasurableSet (((insert j t).inf fun i => {ω : Ω | X i ω = true}) ∩
        ((s \ insert j t).inf fun i => {ω : Ω | X i ω = false})) :=
      (measSet_inf_true X hmeas (insert j t)).inter
        (measSet_inf_false X hmeas (s \ insert j t))
    have hmu : μ ((t.inf fun i => {ω : Ω | X i ω = true}) ∩
        (((s.erase j) \ t).inf fun i => {ω : Ω | X i ω = false}))
        = μ ((t.inf fun i => {ω : Ω | X i ω = true}) ∩
        ((s \ t).inf fun i => {ω : Ω | X i ω = false}))
        + μ (((insert j t).inf fun i => {ω : Ω | X i ω = true}) ∩
        ((s \ insert j t).inf fun i => {ω : Ω | X i ω = false})) := by
      conv_lhs => rw [heq]
      exact MeasureTheory.measure_union hdisj hmeas2
    rw [ih_mid] at hmu
    rw [ih_ins] at hmu
    rw [hcard_ins_t] at hmu
    have hexp : p ^ t.card * (1 - p) ^ k
        = p ^ t.card * (1 - p) ^ (k + 1) + p ^ (t.card + 1) * (1 - p) ^ k := by
      have hpow : (1 - p) ^ (k + 1) = (1 - p) ^ k * (1 - p) := pow_succ (1 - p) k
      rw [hpow]
      have hpow2 : p ^ (t.card + 1) = p ^ t.card * p := pow_succ p t.card
      rw [hpow2]
      have hcancel : (1 - p) + p = 1 := tsub_add_cancel_of_le hp_le
      have hfactor : p ^ t.card * ((1 - p) ^ k * (1 - p))
          + p ^ t.card * p * (1 - p) ^ k
          = p ^ t.card * (1 - p) ^ k * ((1 - p) + p) := by ring
      have h1 : p ^ t.card * ((1 - p) ^ k * (1 - p))
          + p ^ t.card * p * (1 - p) ^ k
          = p ^ t.card * (1 - p) ^ k := by
        rw [hfactor, hcancel, mul_one]
      exact h1.symm
    have hfin : p ^ (t.card + 1) * (1 - p) ^ k ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top hp_top) (ENNReal.pow_ne_top h1p_top)
    have hcombined : μ ((t.inf fun i => {ω : Ω | X i ω = true}) ∩
        ((s \ t).inf fun i => {ω : Ω | X i ω = false}))
        + (p ^ (t.card + 1) * (1 - p) ^ k)
        = p ^ t.card * (1 - p) ^ (k + 1) + (p ^ (t.card + 1) * (1 - p) ^ k) := by
      rw [← hmu, hexp]
    exact (ENNReal.add_left_inj hfin).mp hcombined

private lemma mem_inf_iff {Ω : Type*} (s : Finset ℕ) (f : ℕ → Set Ω) (ω : Ω) :
    ω ∈ s.inf f ↔ ∀ i ∈ s, ω ∈ f i := by
  simp [Finset.inf_eq_iInf]

private lemma pat_eq_filter {Ω : Type*} (X : ℕ → Ω → Bool)
    (s t : Finset ℕ) (hsub : t ⊆ s) :
    (t.inf fun i => {ω : Ω | X i ω = true}) ∩
      ((s \ t).inf fun i => {ω : Ω | X i ω = false})
    = {ω | Finset.filter (fun i => X i ω = true) s = t} := by
  ext ω
  simp only [Set.mem_inter_iff, mem_inf_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    obtain ⟨ht, hf⟩ := h
    have h1 : Finset.filter (fun i => X i ω = true) s ⊆ t := by
      intro x hx
      simp [Finset.mem_filter] at hx
      obtain ⟨hxs, hxtrue⟩ := hx
      by_contra hxn
      have hmem : x ∈ s \ t := Finset.mem_sdiff.mpr ⟨hxs, hxn⟩
      have hfalse := hf x hmem
      rw [hxtrue] at hfalse
      simp at hfalse
    have h2 : t ⊆ Finset.filter (fun i => X i ω = true) s := by
      intro x hx
      simp [Finset.mem_filter]
      constructor
      · exact hsub hx
      · exact ht x hx
    exact Finset.Subset.antisymm h1 h2
  · intro h
    constructor
    · intro i hi
      have hmem : i ∈ Finset.filter (fun i => X i ω = true) s := by
        rw [h]
        exact hi
      simp [Finset.mem_filter] at hmem
      exact hmem.2
    · intro i hi
      have hmem_s : i ∈ s := (Finset.mem_sdiff.mp hi).1
      have hmem_nt : i ∉ t := (Finset.mem_sdiff.mp hi).2
      have hnf : i ∉ Finset.filter (fun i => X i ω = true) s := by
        rw [h]
        exact hmem_nt
      simp [Finset.mem_filter] at hnf
      have hxs : i ∈ s := hmem_s
      simp [hxs] at hnf
      cases hx : X i ω with
      | true => simp [hx] at hnf
      | false => rfl

private lemma binom_sum (r q : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * r ^ k * q ^ (n - k)
      = (r + q) ^ n := by
  have h := add_pow r q n
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma choose_succ_mul_succ (n k : ℕ) :
    (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by
  have h := Nat.choose_mul (n := n + 1) (k := k + 1) (s := 1) (by omega)
  rw [Nat.choose_one_right, Nat.choose_one_right] at h
  have e1 : n + 1 - 1 = n := by omega
  have e2 : k + 1 - 1 = k := by omega
  rw [e1, e2] at h
  linarith [h]

private lemma binom_mean (r q : ℝ) (h : r + q = 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * r ^ k * q ^ (n - k) * (k : ℝ)
      = (n : ℝ) * r := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, add_zero]
    have hmul : ∀ k ∈ Finset.range (n + 1),
        ((n + 1).choose (k + 1) : ℝ) * r ^ (k + 1) * q ^ (n + 1 - (k + 1)) * ((k + 1 : ℕ) : ℝ)
        = ((n + 1 : ℕ) : ℝ) * r * ((n.choose k : ℝ) * r ^ k * q ^ (n - k)) := by
      intro k _
      have hnat := choose_succ_mul_succ n k
      have hexp : n + 1 - (k + 1) = n - k := by omega
      rw [hexp, pow_succ']
      have hcast : ((k + 1 : ℕ) : ℝ) * (((n + 1).choose (k + 1) : ℕ) : ℝ)
          = ((n + 1 : ℕ) : ℝ) * ((n.choose k : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at hcast ⊢
      linear_combination hcast * (r ^ k * q ^ (n - k) * r)
    rw [Finset.sum_congr rfl hmul, ← Finset.mul_sum, binom_sum, h, one_pow, mul_one]

private lemma choose_succ_mul_succ2 (n k : ℕ) :
    (k + 2) * ((k + 1) * (n + 2).choose (k + 2)) = (n + 2) * ((n + 1) * n.choose k) := by
  have h1 := Nat.choose_mul (n := n + 2) (k := k + 2) (s := 1) (by omega)
  have h2 := Nat.choose_mul (n := n + 1) (k := k + 1) (s := 1) (by omega)
  rw [Nat.choose_one_right, Nat.choose_one_right] at h1 h2
  have e1 : n + 2 - 1 = n + 1 := by omega
  have e2 : k + 2 - 1 = k + 1 := by omega
  have e3 : n + 1 - 1 = n := by omega
  have e4 : k + 1 - 1 = k := by omega
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  linear_combination (k + 1) * h1 + (n + 2) * h2

private lemma binom_fac_one (r q : ℝ) :
    ∑ k ∈ Finset.range (1 + 1), (Nat.choose 1 k : ℝ) * r ^ k * q ^ (1 - k)
      * ((k : ℝ) * ((k : ℝ) - 1)) = (1 : ℝ) * ((1 : ℝ) - 1) * r ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp

private lemma binom_fac (r q : ℝ) (h : r + q = 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * r ^ k * q ^ (n - k)
        * ((k : ℝ) * ((k : ℝ) - 1))
      = (n : ℝ) * ((n : ℝ) - 1) * r ^ 2 := by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero =>
      simpa using binom_fac_one r q
    | succ n =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [Nat.cast_zero, Nat.cast_one, zero_add, zero_mul, mul_zero, sub_self, add_zero]
      have hmul : ∀ k ∈ Finset.range (n + 1),
          ((n + 2).choose (k + 1 + 1) : ℝ) * r ^ (k + 1 + 1) * q ^ (n + 2 - (k + 1 + 1))
            * ((((k + 1 + 1 : ℕ)) : ℝ) * ((((k + 1 + 1 : ℕ)) : ℝ) - 1))
          = ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * r ^ 2
            * ((n.choose k : ℝ) * r ^ k * q ^ (n - k)) := by
        intro k _
        have hnat := choose_succ_mul_succ2 n k
        have hexp : n + 2 - (k + 1 + 1) = n - k := by omega
        have hexp2 : k + 1 + 1 = k + 2 := by omega
        rw [hexp, hexp2, pow_succ', pow_succ']
        have hcast : ((k + 2 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (((n + 2).choose (k + 2) : ℕ) : ℝ))
            = ((n + 2 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * ((n.choose k : ℕ) : ℝ)) := by
          exact_mod_cast hnat
        push_cast at hcast ⊢
        linear_combination hcast * (r ^ 2 * r ^ k * q ^ (n - k))
      rw [Finset.sum_congr rfl hmul, ← Finset.mul_sum, binom_sum, h, one_pow]
      push_cast
      ring

private lemma binom_var (r q : ℝ) (h : r + q = 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * r ^ k * q ^ (n - k)
        * (((k : ℝ) - (n : ℝ) * r) ^ 2)
      = (n : ℝ) * r * q := by
  have hq : q = 1 - r := by linarith
  have e1 : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * r ^ k * q ^ (n - k) * (((k : ℝ) - (n : ℝ) * r) ^ 2)
      = ((n.choose k : ℝ) * r ^ k * q ^ (n - k) * ((k : ℝ) * ((k : ℝ) - 1))
        + (n.choose k : ℝ) * r ^ k * q ^ (n - k) * (k : ℝ))
        - ((n.choose k : ℝ) * r ^ k * q ^ (n - k) * (k : ℝ)) * ((n : ℝ) * r * 2)
        + (n.choose k : ℝ) * r ^ k * q ^ (n - k) * (((n : ℝ) * r) ^ 2) := by
    intro k _
    ring
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hM2 : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * r ^ k * q ^ (n - k) * (k : ℝ))
        * ((n : ℝ) * r * 2)
      = ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℝ) * r ^ k * q ^ (n - k) * (k : ℝ)) * ((n : ℝ) * r * 2) :=
    Finset.sum_mul _ _ _
  have hB2 : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * r ^ k * q ^ (n - k))
        * (((n : ℝ) * r) ^ 2)
      = ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * r ^ k * q ^ (n - k) * (((n : ℝ) * r) ^ 2) :=
    Finset.sum_mul _ _ _
  rw [← hM2, ← hB2, binom_fac r q h n, binom_mean r q h n]
  have hS : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * r ^ k * q ^ (n - k)) = 1 := by
    rw [binom_sum, h, one_pow]
  rw [hS, hq]
  ring

private lemma odd_tail_eq (r q : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1 + 1),
      (if (2 * m + 1) / 2 < k then ((2*m+1).choose k : ℝ) * r ^ k * q ^ (2*m+1-k) else 0)
    = ∑ j ∈ Finset.range (m + 1),
      (((2*m+1).choose (m+1+j) : ℕ) : ℝ) * r ^ (m+1+j) * q ^ (m-j) := by
  have hset : (Finset.range (2*m+1+1)).filter (fun k => (2*m+1)/2 < k)
      = Finset.Ico (m+1) (2*m+1+1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter, hset, Finset.sum_Ico_eq_sum_range]
  have hsub : 2*m+1+1-(m+1) = m+1 := by omega
  rw [hsub]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hlt : j < m + 1 := Finset.mem_range.mp hj
  have hexp : 2*m+1-(m+1+j) = m-j := by omega
  rw [hexp]

private lemma measSet_filter_eq {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hmeas : ∀ i, Measurable (X i))
    (s t : Finset ℕ) :
    MeasurableSet {ω | Finset.filter (fun i => X i ω = true) s = t} := by
  by_cases hsub : t ⊆ s
  · rw [← pat_eq_filter X s t hsub]
    exact (measSet_inf_true X hmeas t).inter (measSet_inf_false X hmeas (s \ t))
  · have hempty : {ω | Finset.filter (fun i => X i ω = true) s = t} = ∅ := by
      ext ω
      simp only [Set.mem_empty_iff_false, iff_false, Set.mem_ofPred_eq]
      intro hcon
      apply hsub
      rw [← hcon]
      exact Finset.filter_subset _ _
    rw [hempty]
    exact MeasurableSet.empty

private lemma binomial_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (p : ENNReal)
    (hmeas : ∀ i, Measurable (X i))
    (hmarg : ∀ i, μ {ω | X i ω = true} = p)
    (hindep : ∀ s : Finset ℕ, s.Nonempty →
      μ (s.inf fun i => {ω | X i ω = true}) =
        s.prod fun i => μ {ω | X i ω = true})
    (hp_le : p ≤ 1) (hp_top : p ≠ ⊤) (h1p_top : 1 - p ≠ ⊤)
    (Q : ℕ → Prop) [DecidablePred Q] (n : ℕ) :
    μ {ω | Q ((Finset.filter (fun i => X i ω = true) (Finset.range n)).card)}
    = ∑ k ∈ Finset.range (n + 1),
      (n.choose k) • (if Q k then p ^ k * (1 - p) ^ (n - k) else 0) := by
  set F : Finset (Finset ℕ) :=
    (Finset.powerset (Finset.range n)).filter (fun t => Q t.card) with hFdef
  have hunion : {ω | Q ((Finset.filter (fun i => X i ω = true) (Finset.range n)).card)}
      = ⋃ t ∈ F, {ω | Finset.filter (fun i => X i ω = true) (Finset.range n) = t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hQ
      have hmem : Finset.filter (fun i => X i ω = true) (Finset.range n)
          ∈ Finset.powerset (Finset.range n) :=
        Finset.mem_powerset.mpr (Finset.filter_subset _ _)
      exact ⟨_, hFdef ▸ Finset.mem_filter.mpr ⟨hmem, hQ⟩, rfl⟩
    · rintro ⟨t, ht, heq⟩
      have ht' : t ∈ (Finset.powerset (Finset.range n)).filter (fun t => Q t.card) := hFdef ▸ ht
      rw [heq]
      exact (Finset.mem_filter.mp ht').2
  have hdisj : (↑F : Set (Finset ℕ)).PairwiseDisjoint
      (fun t => {ω | Finset.filter (fun i => X i ω = true) (Finset.range n) = t}) := by
    intro t1 _ t2 _ hne
    show Disjoint _ _
    apply Set.disjoint_left.mpr
    intro ω h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    exact hne (h1.symm.trans h2)
  have hmeas_each : ∀ t ∈ F,
      MeasurableSet {ω | Finset.filter (fun i => X i ω = true) (Finset.range n) = t} :=
    fun t _ => measSet_filter_eq X hmeas _ t
  rw [hunion, MeasureTheory.measure_biUnion_finset hdisj hmeas_each]
  have hterm : ∀ t ∈ F, μ {ω | Finset.filter (fun i => X i ω = true) (Finset.range n) = t}
      = p ^ t.card * (1 - p) ^ (n - t.card) := by
    intro t ht
    have ht' : t ∈ (Finset.powerset (Finset.range n)).filter (fun t => Q t.card) := hFdef ▸ ht
    have hsub : t ⊆ Finset.range n :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp ht').1
    rw [← pat_eq_filter X _ t hsub]
    have hcard : ((Finset.range n) \ t).card = n - t.card := by
      have h := Finset.card_sdiff_add_card_eq_card hsub
      rw [Finset.card_range] at h
      omega
    have hpa := pattern_aux X p hmeas hmarg hindep hp_le hp_top h1p_top
      ((Finset.range n) \ t).card (Finset.range n) t hsub rfl
    rw [hcard] at hpa
    exact hpa
  rw [Finset.sum_congr rfl hterm]
  have hgroup : (∑ t ∈ F, (p ^ t.card * (1 - p) ^ (n - t.card)))
      = ∑ k ∈ Finset.range (n + 1),
        (n.choose k) • (if Q k then p ^ k * (1 - p) ^ (n - k) else 0) := by
    have h1 : (∑ t ∈ F, (p ^ t.card * (1 - p) ^ (n - t.card)))
        = ∑ t ∈ Finset.powerset (Finset.range n),
          (if Q t.card then p ^ t.card * (1 - p) ^ (n - t.card) else 0) := by
      rw [hFdef, Finset.sum_filter]
    rw [h1]
    have h2 := Finset.sum_powerset_apply_card (x := Finset.range n)
      (fun j => if Q j then p ^ j * (1 - p) ^ (n - j) else 0)
    rw [Finset.card_range] at h2
    exact h2
  exact hgroup

private lemma maj_toReal {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (p : ENNReal) (r q : ℝ)
    (hr : p.toReal = r) (hq : (1 - p).toReal = q)
    (hmeas : ∀ i, Measurable (X i))
    (hmarg : ∀ i, μ {ω | X i ω = true} = p)
    (hindep : ∀ s : Finset ℕ, s.Nonempty →
      μ (s.inf fun i => {ω | X i ω = true}) =
        s.prod fun i => μ {ω | X i ω = true})
    (hp_le : p ≤ 1) (hp_top : p ≠ ⊤) (h1p_top : 1 - p ≠ ⊤)
    (Q : ℕ → Prop) [DecidablePred Q] (n : ℕ) :
    (μ {ω | Q ((Finset.filter (fun i => X i ω = true) (Finset.range n)).card)}).toReal
    = ∑ k ∈ Finset.range (n + 1),
      (if Q k then (n.choose k : ℝ) * r ^ k * q ^ (n - k) else 0) := by
  rw [binomial_law X p hmeas hmarg hindep hp_le hp_top h1p_top Q n]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro k _
    by_cases hk : Q k
    · simp only [hk, ite_true]
      rw [nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_mul,
        ENNReal.toReal_pow, ENNReal.toReal_pow, hr, hq]
      ring
    · simp only [hk, ite_false]
      rw [nsmul_eq_mul]
      simp
  · intro k _
    by_cases hk : Q k
    · simp only [hk, ite_true]
      rw [nsmul_eq_mul]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top hp_top) (ENNReal.pow_ne_top h1p_top))
    · simp only [hk, ite_false]
      simp

private lemma measSet_maj {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hmeas : ∀ i, Measurable (X i))
    (Q : ℕ → Prop) [DecidablePred Q] (n : ℕ) :
    MeasurableSet {ω | Q ((Finset.filter (fun i => X i ω = true) (Finset.range n)).card)} := by
  have hun : {ω | Q ((Finset.filter (fun i => X i ω = true) (Finset.range n)).card)}
      = ⋃ t ∈ (Finset.powerset (Finset.range n)).filter (fun t => Q t.card),
        {ω | Finset.filter (fun i => X i ω = true) (Finset.range n) = t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hQ
      have hmem : Finset.filter (fun i => X i ω = true) (Finset.range n)
          ∈ Finset.powerset (Finset.range n) :=
        Finset.mem_powerset.mpr (Finset.filter_subset _ _)
      exact ⟨_, Finset.mem_filter.mpr ⟨hmem, hQ⟩, rfl⟩
    · rintro ⟨t, ht, heq⟩
      rw [heq]
      exact (Finset.mem_filter.mp ht).2
  have hcongr : (⋃ t ∈ (Finset.powerset (Finset.range n)).filter (fun t => Q t.card),
        {ω | Finset.filter (fun i => X i ω = true) (Finset.range n) = t})
      = ⋃ t ∈ (↑((Finset.powerset (Finset.range n)).filter (fun t => Q t.card)) : Set (Finset ℕ)),
        {ω | Finset.filter (fun i => X i ω = true) (Finset.range n) = t} := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_coe]
  rw [hun, hcongr]
  exact (Finset.finite_toSet _).measurableSet_biUnion
    (fun t _ => measSet_filter_eq X hmeas _ t)

/-- **Condorcet's jury theorem.** Let $\mu$ be a probability measure on a measurable space
$\Omega$, let $X_0, X_1, \dots$ be measurable maps from $\Omega$ to $\{\text{true}, \text{false}\}$
(the votes, true meaning a correct vote), and let $p$ be a number with $1/2 < p < 1$. Suppose that
each vote is correct with probability $p$, that is $\mu(X_i = \text{true}) = p$ for every $i$, and
that the events $\{X_i = \text{true}\}$ are independent: for every nonempty finite set $s$ of
indices, $\mu\bigl(\bigcap_{i \in s} \{X_i = \text{true}\}\bigr) = \prod_{i \in s}
\mu(X_i = \text{true})$. For $n \in \mathbb{N}$ let $M_n$ be the event that more than
$\lfloor n/2 \rfloor$ of the first $n$ votes $X_0, \dots, X_{n-1}$ are correct. Then
$\mu(M_n) \to 1$ as $n \to \infty$, and $\mu(M_n) > p$ for every odd $n > 1$.

Source: https://en.wikipedia.org/wiki/Condorcet%27s_jury_theorem.
Proves `Wanted` entry `condorcet_jury_theorem`.
-/
theorem condorcet_jury_theorem {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (p : ENNReal) (hp : 1 / 2 < p) (hp2 : p < 1)
    (hmeas : ∀ i, Measurable (X i))
    (hmarg : ∀ i, μ {ω | X i ω = true} = p)
    (hindep : ∀ s : Finset ℕ, s.Nonempty →
      μ (s.inf fun i => {ω | X i ω = true}) =
        s.prod fun i => μ {ω | X i ω = true}) :
    Filter.Tendsto
      (fun n => μ {ω | n / 2 < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card})
      Filter.atTop (nhds 1) ∧
    ∀ n : ℕ, Odd n → 1 < n →
      p < μ {ω | n / 2 < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card} := by
  have hp_le : p ≤ 1 := le_of_lt hp2
  have hp_top : p ≠ ⊤ := ne_top_of_lt hp2
  have h1p_top : 1 - p ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have h12ne : (1 / 2 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)
  have h12 : ((1 / 2 : ENNReal)).toReal = (1 / 2 : ℝ) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one]
    norm_num
  have hr1 : (1 / 2 : ℝ) < p.toReal := by
    have h := (ENNReal.toReal_lt_toReal h12ne hp_top).mpr hp
    rwa [h12] at h
  have hr2 : p.toReal < 1 := by
    have h := (ENNReal.toReal_lt_toReal hp_top ENNReal.one_ne_top).mpr hp2
    rwa [ENNReal.toReal_one] at h
  have hq_eq : (1 - p).toReal = 1 - p.toReal := by
    rw [ENNReal.toReal_sub_of_le hp_le ENNReal.one_ne_top, ENNReal.toReal_one]
  have hrq : p.toReal + (1 - p).toReal = 1 := by
    rw [hq_eq]; ring
  have hr0 : (0 : ℝ) < p.toReal := by linarith
  have hq0 : (0 : ℝ) < (1 - p).toReal := by rw [hq_eq]; linarith
  set ε := p.toReal - 1 / 2 with hεdef
  set C := p.toReal * (1 - p).toReal / ε ^ 2 with hCdef
  have hε : (0 : ℝ) < ε := by rw [hεdef]; linarith
  constructor
  · -- Part 1: the majority probability tends to 1.
    have hceq : ∀ n : ℕ, {ω | n / 2
        < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}ᶜ
        = {ω | (Finset.filter (fun i => X i ω = true) (Finset.range n)).card ≤ n / 2} := by
      intro n
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    have hpt : ∀ n : ℕ, 1 ≤ n → ∀ k ∈ Finset.range (n + 1),
        (if k ≤ n / 2 then (n.choose k : ℝ) * p.toReal ^ k * (1 - p).toReal ^ (n - k) else 0)
        ≤ ((n.choose k : ℝ) * p.toReal ^ k * (1 - p).toReal ^ (n - k)
          * (((k : ℝ) - (n : ℝ) * p.toReal) ^ 2)) / (((n : ℝ) * ε) ^ 2) := by
      intro n hn k _
      have hterm_nn : (0 : ℝ)
          ≤ (n.choose k : ℝ) * p.toReal ^ k * (1 - p).toReal ^ (n - k) := by
        apply mul_nonneg
        apply mul_nonneg
        · exact Nat.cast_nonneg _
        · exact pow_nonneg (le_of_lt hr0) _
        · exact pow_nonneg (le_of_lt hq0) _
      by_cases hk : k ≤ n / 2
      · simp only [hk, ite_true]
        have hkn : (k : ℝ) ≤ (n : ℝ) / 2 := by
          have h2 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
          have h3 : (k : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hk
          linarith
        have hnr : (n : ℝ) * ε ≤ (n : ℝ) * p.toReal - (k : ℝ) := by
          rw [hεdef]; linarith
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hpos : (0 : ℝ) < ((n : ℝ) * ε) ^ 2 := pow_pos (mul_pos hnR hε) 2
        have hsq : ((n : ℝ) * ε) ^ 2 ≤ (((k : ℝ) - (n : ℝ) * p.toReal) ^ 2) := by
          have h := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hε)) hnr 2
          linear_combination h
        have h1 : (1 : ℝ)
            ≤ (((k : ℝ) - (n : ℝ) * p.toReal) ^ 2) / (((n : ℝ) * ε) ^ 2) := by
          rw [le_div_iff₀ hpos, one_mul]
          exact hsq
        calc (n.choose k : ℝ) * p.toReal ^ k * (1 - p).toReal ^ (n - k)
            = (n.choose k : ℝ) * p.toReal ^ k * (1 - p).toReal ^ (n - k) * 1 :=
              (mul_one _).symm
          _ ≤ (n.choose k : ℝ) * p.toReal ^ k * (1 - p).toReal ^ (n - k)
              * ((((k : ℝ) - (n : ℝ) * p.toReal) ^ 2) / (((n : ℝ) * ε) ^ 2)) :=
              mul_le_mul_of_nonneg_left h1 hterm_nn
          _ = ((n.choose k : ℝ) * p.toReal ^ k * (1 - p).toReal ^ (n - k)
              * (((k : ℝ) - (n : ℝ) * p.toReal) ^ 2)) / (((n : ℝ) * ε) ^ 2) := by
              ring
      · simp only [hk, ite_false]
        apply div_nonneg
        · exact mul_nonneg hterm_nn (sq_nonneg _)
        · exact sq_nonneg _
    have hsum : ∀ n : ℕ, 1 ≤ n →
        (∑ k ∈ Finset.range (n + 1),
          (if k ≤ n / 2 then (n.choose k : ℝ) * p.toReal ^ k * (1 - p).toReal ^ (n - k)
            else 0))
        ≤ (n : ℝ) * p.toReal * (1 - p).toReal / (((n : ℝ) * ε) ^ 2) := by
      intro n hn
      have hle := Finset.sum_le_sum (hpt n hn)
      rw [← Finset.sum_div, binom_var p.toReal (1 - p).toReal hrq n] at hle
      exact hle
    have hfrac : ∀ n : ℕ, 1 ≤ n →
        (n : ℝ) * p.toReal * (1 - p).toReal / (((n : ℝ) * ε) ^ 2) = C / (n : ℝ) := by
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hε0 : ε ≠ 0 := ne_of_gt hε
      rw [hCdef]
      field_simp
    have hcompl : ∀ n : ℕ, 1 ≤ n →
        (μ {ω | n / 2 < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}ᶜ).toReal
        ≤ C / (n : ℝ) := by
      intro n hn
      have e1 : (μ {ω | n / 2
          < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}ᶜ).toReal
          = (μ {ω | (Finset.filter (fun i => X i ω = true) (Finset.range n)).card
            ≤ n / 2}).toReal := by rw [hceq n]
      have e2 : (μ {ω | (Finset.filter (fun i => X i ω = true) (Finset.range n)).card
          ≤ n / 2}).toReal
          = ∑ k ∈ Finset.range (n + 1),
            (if k ≤ n / 2 then (n.choose k : ℝ) * p.toReal ^ k * (1 - p).toReal ^ (n - k)
              else 0) :=
        maj_toReal X p p.toReal (1 - p).toReal rfl rfl hmeas hmarg hindep hp_le hp_top h1p_top
          (fun k => k ≤ n / 2) n
      rw [e1, e2]
      calc (∑ k ∈ Finset.range (n + 1),
            (if k ≤ n / 2 then (n.choose k : ℝ) * p.toReal ^ k * (1 - p).toReal ^ (n - k)
              else 0))
          ≤ (n : ℝ) * p.toReal * (1 - p).toReal / (((n : ℝ) * ε) ^ 2) := hsum n hn
        _ = C / (n : ℝ) := hfrac n hn
    have hg0 : Filter.Tendsto (fun n : ℕ => 1 - C / (n : ℝ)) Filter.atTop (nhds 1) := by
      have h := Filter.Tendsto.sub (f := fun _ : ℕ => (1 : ℝ))
        (g := fun n : ℕ => C / (n : ℝ)) tendsto_const_nhds
        (tendsto_const_div_atTop_nhds_zero_nat C)
      simpa using h
    have hle1 : ∀ n : ℕ,
        (μ {ω | n / 2 < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}).toReal
        ≤ 1 := by
      intro n
      have hfin : μ {ω | n / 2
          < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card} ≠ ⊤ :=
        ne_top_of_lt (MeasureTheory.measure_lt_top _ _)
      have h := (ENNReal.toReal_le_toReal hfin ENNReal.one_ne_top).mpr
        MeasureTheory.prob_le_one
      rwa [ENNReal.toReal_one] at h
    have hlim_real : Filter.Tendsto
        (fun n => (μ {ω | n / 2
          < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}).toReal)
        Filter.atTop (nhds 1) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hg0 tendsto_const_nhds _ _
      · apply Filter.eventually_atTop.mpr
        exact ⟨1, fun n hn => by
          have hMc : MeasurableSet {ω | n / 2
              < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card} :=
            measSet_maj X hmeas (fun k => n / 2 < k) n
          have hfinM : μ {ω | n / 2
              < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card} ≠ ⊤ :=
            ne_top_of_lt (MeasureTheory.measure_lt_top _ _)
          have hfinC : μ {ω | n / 2
              < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}ᶜ ≠ ⊤ :=
            ne_top_of_lt (MeasureTheory.measure_lt_top _ _)
          have hadd : μ {ω | n / 2
              < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}
              + μ {ω | n / 2
              < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}ᶜ = 1 := by
            rw [MeasureTheory.measure_add_measure_compl hMc, MeasureTheory.measure_univ]
          have htoReal : (μ {ω | n / 2
              < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}).toReal
              + (μ {ω | n / 2
              < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}ᶜ).toReal
              = 1 := by
            rw [← ENNReal.toReal_add hfinM hfinC, hadd, ENNReal.toReal_one]
          have hc := hcompl n hn
          linarith⟩
      · exact Filter.Eventually.of_forall hle1
    have hlim : Filter.Tendsto
        (fun n => μ {ω | n / 2
          < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card})
        Filter.atTop (nhds 1) := by
      have h := (ENNReal.continuous_ofReal.tendsto 1).comp hlim_real
      simp only [ENNReal.ofReal_one] at h
      have heq : (ENNReal.ofReal ∘ (fun n => (μ {ω | n / 2
          < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}).toReal))
          = (fun n => μ {ω | n / 2
            < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card}) := by
        funext n
        exact ENNReal.ofReal_toReal (ne_top_of_lt (MeasureTheory.measure_lt_top _ _))
      rwa [heq] at h
    exact hlim
  · -- Part 2: odd n > 1 beats a single voter.
    intro n hn h1n
    obtain ⟨m, hm⟩ := hn
    subst hm
    have hm1 : 1 ≤ m := by omega
    have htail : (μ {ω | (2 * m + 1) / 2
        < (Finset.filter (fun i => X i ω = true) (Finset.range (2 * m + 1))).card}).toReal
        = ∑ j ∈ Finset.range (m + 1),
          (((2 * m + 1).choose (m + 1 + j) : ℕ) : ℝ) * p.toReal ^ (m + 1 + j)
            * (1 - p).toReal ^ (m - j) := by
      have e2 := maj_toReal X p p.toReal (1 - p).toReal rfl rfl hmeas hmarg hindep hp_le hp_top
        h1p_top (fun k => (2 * m + 1) / 2 < k) (2 * m + 1)
      exact e2.trans (odd_tail_eq p.toReal (1 - p).toReal m)
    have hgt := condorcet_tail_gt p.toReal hr1 hr2 m hm1
    rw [← hq_eq] at hgt
    rw [← htail] at hgt
    have hfin : μ {ω | (2 * m + 1) / 2
        < (Finset.filter (fun i => X i ω = true) (Finset.range (2 * m + 1))).card} ≠ ⊤ :=
      ne_top_of_lt (MeasureTheory.measure_lt_top _ _)
    exact (ENNReal.toReal_lt_toReal hp_top hfin).mp hgt

/-- **Condorcet's jury theorem for mutually independent votes.** Let $\mu$ be a probability measure
on a measurable space $\Omega$, let $X_0, X_1, \dots$ be measurable maps from $\Omega$ to
$\{\text{true}, \text{false}\}$ (the votes, true meaning a correct vote) that are mutually
independent random variables under $\mu$, and let $p$ be a number with $1/2 < p < 1$. Suppose that
each vote is correct with probability $p$, that is $\mu(X_i = \text{true}) = p$ for every $i$. For
$n \in \mathbb{N}$ let $M_n$ be the event that more than $\lfloor n/2 \rfloor$ of the first $n$
votes $X_0, \dots, X_{n-1}$ are correct. Then $\mu(M_n) \to 1$ as $n \to \infty$, and
$\mu(M_n) > p$ for every odd $n > 1$. -/
theorem condorcet_jury_theorem_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (p : ENNReal) (hp : 1 / 2 < p) (hp2 : p < 1)
    (hmeas : ∀ i, Measurable (X i))
    (hmarg : ∀ i, μ {ω | X i ω = true} = p)
    (hindep : ProbabilityTheory.iIndepFun X μ) :
    Filter.Tendsto
      (fun n => μ {ω | n / 2 < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card})
      Filter.atTop (nhds 1) ∧
    ∀ n : ℕ, Odd n → 1 < n →
      p < μ {ω | n / 2 < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card} :=
  condorcet_jury_theorem X p hp hp2 hmeas hmarg fun s _ => by
    rw [Finset.inf_eq_iInf]
    exact hindep.measure_inter_preimage_eq_mul s (sets := fun _ => {true})
      fun _ _ => measurableSet_singleton true

end

end MetaMathlibExt
