/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Reliability.SystemSurvival
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases

/-!
# System-survival checks

Focused checks for `MathlibExt.Probability.Reliability.SystemSurvival`:
on the fair two-point law, the lifetime `if ω then 2 else 0` has
survival `1 / 2` at level 1; two independent copies (coordinates
of a product law, padded by a zero lifetime) give parallel
survival `3 / 4` by the product formula, and the union bound
applies to the same two-point lifetime.

These are elaboration and non-vacuity checks, not new results.
-/

open MeasureTheory Set Filter Finset Reliability ProbabilityTheory

open scoped ENNReal

/-- The fair two-point probability law on `Bool`. -/
noncomputable def boolFair : MeasureTheory.Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true
    + (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false

instance : MeasureTheory.IsProbabilityMeasure boolFair := by
  refine ⟨?_⟩
  simp [boolFair, MeasureTheory.Measure.add_apply,
    MeasureTheory.Measure.smul_apply, ENNReal.inv_two_add_inv_two]

/-- The stated lifetime has survival `1 / 2` at level 1. -/
example : boolFair.real {ω | (1 : ℝ) < (fun ω : Bool => if ω then 2 else 0) ω}
    = 1 / 2 := by
  have hset : {ω | (1 : ℝ) < (fun ω : Bool => if ω then 2 else 0) ω}
      = {true} := by
    ext ω
    cases ω <;> simp
  rw [hset, MeasureTheory.measureReal_def]
  simp [boolFair, MeasureTheory.Measure.add_apply,
    MeasureTheory.Measure.smul_apply]

/-- Union bound for the stated lifetime family. -/
example : boolFair.real {ω | ∃ i < 2, (1 : ℝ)
      < (fun ω : Bool => if ω then 2 else 0) ω}
    ≤ ∑ i ∈ Finset.range 2,
      boolFair.real {ω | (1 : ℝ) < (fun ω : Bool => if ω then 2 else 0) ω} :=
  parallel_survival_le_sum (T := fun _ : ℕ => fun ω : Bool =>
    if ω then 2 else 0) 2 1

/-- Product law on two coordinates. -/
noncomputable def coordLaw : MeasureTheory.Measure (Fin 2 → Bool) :=
  MeasureTheory.Measure.pi (fun _ => boolFair)

instance : MeasureTheory.IsProbabilityMeasure coordLaw := by
  unfold coordLaw
  infer_instance

/-- Coordinate lifetimes, padded by a zero lifetime. -/
noncomputable def padLifetime (i : ℕ) (ω : Fin 2 → Bool) : ℝ :=
  if i = 0 then (if ω 0 then 2 else 0)
  else if i = 1 then (if ω 1 then 2 else 0) else 0

/-- Survival of one coordinate lifetime under the product law. -/
lemma coordLaw_survival (j : Fin 2) :
    coordLaw.real {ω | (1 : ℝ) < (if ω j then (2 : ℝ) else 0)}
      = 1 / 2 := by
  have hset : {ω | (1 : ℝ) < (if ω j then (2 : ℝ) else 0)}
      = Set.pi Set.univ
        (fun i => if i = j then {true} else Set.univ) := by
    ext ω
    constructor
    · intro h i _
      by_cases hij : i = j
      · subst hij
        by_cases hi : ω i
        · simp [hi]
        · exfalso
          simp only [Set.mem_setOf_eq, ite_eq_right hi] at h
          norm_num at h
      · simp [hij]
    · intro h
      have hj := h j (Set.mem_univ j)
      by_cases hjj : ω j
      · simp [hjj]
      · simp [hjj] at hj
  rw [hset]
  simp only [coordLaw, MeasureTheory.measureReal_def,
    MeasureTheory.Measure.pi_pi, Fin.prod_univ_two]
  by_cases hj : j = 0
  · subst hj
    simp [boolFair, MeasureTheory.Measure.add_apply,
      MeasureTheory.Measure.smul_apply, ENNReal.inv_two_add_inv_two]
  · have hj1 : j = 1 := by
      fin_cases j
      · simp at hj
      · rfl
    subst hj1
    simp [boolFair, MeasureTheory.Measure.add_apply,
      MeasureTheory.Measure.smul_apply, ENNReal.inv_two_add_inv_two]

/-- The padded coordinate lifetimes are mutually independent:
indices `0` and `1` read independent coordinates, and every later
index is constant. -/
lemma padLifetime_indepFun :
    ProbabilityTheory.iIndepFun padLifetime coordLaw := by
  have hY : ProbabilityTheory.iIndepFun
      (fun j ω => (if ω j then (2 : ℝ) else 0)) coordLaw := by
    unfold coordLaw
    exact ProbabilityTheory.iIndepFun_pi
      (X := fun _ (b : Bool) => if b then (2 : ℝ) else 0)
      (fun _ => (measurable_of_finite _).aemeasurable)
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
    at hY ⊢
  intro s A hA
  by_cases hbad : ∃ i ∈ s, 2 ≤ i ∧ (0 : ℝ) ∉ A i
  · obtain ⟨i, his, hi2, hiA⟩ := hbad
    have hpre : padLifetime i ⁻¹' A i = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro ω hω
      have hi0 : i ≠ 0 := by omega
      have hi1 : i ≠ 1 := by omega
      simp [padLifetime, hi0, hi1] at hω
      exact hiA hω
    have hInter : (⋂ i ∈ s, padLifetime i ⁻¹' A i) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro ω hω
      have hωi := Set.mem_iInter₂.mp hω i his
      simp [hpre] at hωi
    rw [hInter, MeasureTheory.measure_empty]
    exact (Finset.prod_eq_zero
      (f := fun i => coordLaw (padLifetime i ⁻¹' A i)) his
      (by rw [hpre]; simp)).symm
  · push_neg at hbad
    have hpre : ∀ i ∈ s, padLifetime i ⁻¹' A i
        = (if i = 0 then (fun ω => if ω 0 then (2 : ℝ) else 0) ⁻¹' A i
          else if i = 1 then (fun ω => if ω 1 then (2 : ℝ) else 0) ⁻¹' A i
          else Set.univ) := by
      intro i hi
      by_cases h0 : i = 0
      · subst h0
        rfl
      · by_cases h1 : i = 1
        · subst h1
          rfl
        · have hi2 : 2 ≤ i := by omega
          have hmem : (0 : ℝ) ∈ A i := hbad i hi hi2
          ext ω
          simp [padLifetime, h0, h1, hi2, hmem]
    have hInter : (⋂ i ∈ s, padLifetime i ⁻¹' A i)
        = ⋂ i ∈ s.filter (fun i => i < 2),
          padLifetime i ⁻¹' A i := by
      ext ω
      simp only [Set.mem_iInter, Finset.mem_filter]
      constructor
      · intro h i hi
        exact h i hi.1
      · intro h i hi
        by_cases hi2 : i < 2
        · exact h i ⟨hi, hi2⟩
        · rw [hpre i hi]
          simp [show ¬(i = 0) by omega, show ¬(i = 1) by omega]
    have hprod : ∏ i ∈ s, coordLaw (padLifetime i ⁻¹' A i)
        = ∏ i ∈ s.filter (fun i => i < 2),
          coordLaw (padLifetime i ⁻¹' A i) := by
      rw [← Finset.prod_filter_mul_prod_filter_not s
        (fun i => i < 2)]
      have hone : ∏ i ∈ s.filter (fun i => ¬ i < 2),
          coordLaw (padLifetime i ⁻¹' A i) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [hpre i hi.1]
        simp [show ¬(i = 0) by omega, show ¬(i = 1) by omega]
      rw [hone, mul_one]
    rw [hInter, hprod]
    by_cases h0 : (0 : ℕ) ∈ s <;> by_cases h1 : (1 : ℕ) ∈ s
    · have hfilt : s.filter (fun i => i < 2) = {0, 1} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hi
          have hii : i = 0 ∨ i = 1 := by omega
          tauto
        · intro hi
          rcases hi with rfl | rfl
          · exact ⟨h0, by norm_num⟩
          · exact ⟨h1, by norm_num⟩
      rw [hfilt, Finset.prod_insert (by simp), Finset.prod_singleton]
      have hinter : (⋂ i ∈ ({0, 1} : Finset ℕ), padLifetime i ⁻¹' A i)
          = padLifetime 0 ⁻¹' A 0 ∩ padLifetime 1 ⁻¹' A 1 := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · intro h
          exact ⟨h 0 (by simp), h 1 (by simp)⟩
        · intro h i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact h.1
          · exact h.2
      rw [hinter]
      have hY' := hY {0, 1} (sets := fun j : Fin 2 => A j.val)
        (fun j _ => hA j.val (by
          fin_cases j
          · exact h0
          · exact h1))
      have hinter2 : (⋂ j ∈ ({0, 1} : Finset (Fin 2)),
            (fun ω : Fin 2 → Bool => if ω j then (2 : ℝ) else 0) ⁻¹' A j.val)
          = (fun ω : Fin 2 → Bool => if ω 0 then (2 : ℝ) else 0) ⁻¹' A 0
            ∩ (fun ω : Fin 2 → Bool => if ω 1 then (2 : ℝ) else 0) ⁻¹' A 1 := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · intro h
          exact ⟨h 0 (by simp), h 1 (by simp)⟩
        · intro h j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl
          · exact h.1
          · exact h.2
      rw [hinter2, Finset.prod_insert (by simp),
        Finset.prod_singleton] at hY'
      convert hY' using 1
      congr 1
      congr 1
      all_goals ext ω <;> simp [padLifetime]
    · have hfilt : s.filter (fun i => i < 2) = {0} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hi
          have hii : i = 0 ∨ i = 1 := by omega
          rcases hii with rfl | rfl
          · rfl
          · exact absurd hi.1 h1
        · intro hi
          subst hi
          exact ⟨h0, by norm_num⟩
      rw [hfilt]
      have hinter : (⋂ i ∈ ({0} : Finset ℕ), padLifetime i ⁻¹' A i)
          = padLifetime 0 ⁻¹' A 0 := by
        ext ω
        simp [Set.mem_iInter]
      rw [hinter, Finset.prod_singleton]
    · have hfilt : s.filter (fun i => i < 2) = {1} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hi
          have hii : i = 0 ∨ i = 1 := by omega
          rcases hii with rfl | rfl
          · exact absurd hi.1 h0
          · rfl
        · intro hi
          subst hi
          exact ⟨h1, by norm_num⟩
      rw [hfilt]
      have hinter : (⋂ i ∈ ({1} : Finset ℕ), padLifetime i ⁻¹' A i)
          = padLifetime 1 ⁻¹' A 1 := by
        ext ω
        simp [Set.mem_iInter]
      rw [hinter, Finset.prod_singleton]
    · have hfilt : s.filter (fun i => i < 2) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        intro hi
        have hii : i = 0 ∨ i = 1 := by omega
        rcases hii with rfl | rfl
        · exact h0 hi.1
        · exact h1 hi.1
      rw [hfilt]
      simp

/-- Parallel survival of the two coordinate lifetimes is `3 / 4`
by the independence product formula. -/
example : coordLaw.real {ω | ∃ i < 2, (1 : ℝ) < padLifetime i ω}
    = 3 / 4 := by
  have hmeas : ∀ i, Measurable (padLifetime i) := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      apply Measurable.piecewise (s := {ω : Fin 2 → Bool | ω 0 = true})
      · show MeasurableSet ((fun ω : Fin 2 → Bool => ω 0) ⁻¹' {true})
        exact (measurable_pi_apply (0 : Fin 2))
          (measurableSet_singleton true)
      · exact measurable_const
      · exact measurable_const
    · by_cases h1 : i = 1
      · subst h1
        apply Measurable.piecewise (s := {ω : Fin 2 → Bool | ω 1 = true})
        · show MeasurableSet ((fun ω : Fin 2 → Bool => ω 1) ⁻¹' {true})
          exact (measurable_pi_apply (1 : Fin 2))
            (measurableSet_singleton true)
        · exact measurable_const
        · exact measurable_const
      · have hfun : (fun ω => padLifetime i ω) = fun _ => (0 : ℝ) := by
          funext ω
          simp [padLifetime, h0, h1]
        have hm : Measurable (fun ω => padLifetime i ω) := by
          rw [hfun]
          exact measurable_const
        exact hm
  have h := parallel_survival_eq padLifetime_indepFun hmeas 2 1
  have hsurv : ∀ i < 2, coordLaw.real {ω | (1 : ℝ) < padLifetime i ω}
      = 1 / 2 := by
    intro i hi
    interval_cases i
    · have hset : {ω | (1 : ℝ) < padLifetime 0 ω}
          = {ω | (1 : ℝ) < (if ω 0 then (2 : ℝ) else 0)} := by
        ext ω
        simp [padLifetime]
      rw [hset]
      exact coordLaw_survival 0
    · have hset : {ω | (1 : ℝ) < padLifetime 1 ω}
          = {ω | (1 : ℝ) < (if ω 1 then (2 : ℝ) else 0)} := by
        ext ω
        simp [padLifetime]
      rw [hset]
      exact coordLaw_survival 1
  rw [h]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    hsurv 0 (by norm_num), hsurv 1 (by norm_num)]
  norm_num
