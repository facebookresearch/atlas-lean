/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.ApproximateDifferentialPrivacy

/-!
# Approximate max-divergence decomposition, part 1 (finite discrete)

Part 1 only: the finite-outcome decomposition (existence of a repaired
distribution). Part 2 (countable extension) is split out and not proved here.

Finite outcome scope: `[Fintype Outcome] [Nonempty Outcome]`. Countable
extension is a recorded gap.

The three predicates below are a standalone finite real form using
`Finset` sums of `(P w).toReal`. No bridge to the Atlas
`IsApproxDP`/`toOuterMeasure` form is proved here.
-/

@[expose] public section

namespace CSLibExt.Privacy.MaxDivergenceDecomposition

/-- Finite approximate max-divergence bound. -/
def approxMaxDivLE {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps delta : ℝ) : Prop :=
  ∀ s : Finset Outcome,
    ∑ w ∈ s, (P w).toReal ≤ Real.exp eps * ∑ w ∈ s, (Q w).toReal + delta

/-- Finite pure max-divergence bound. -/
def maxDivLE {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) : Prop :=
  ∀ w, (P w).toReal ≤ Real.exp eps * (Q w).toReal

/-- Half-L1 total variation distance on a finite type. -/
noncomputable def tvDist {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P R : PMF Outcome) : ℝ :=
  (1 / 2) * ∑ w, |(P w).toReal - (R w).toReal|

/-- Real masses of a finite PMF sum to one. -/
theorem pmf_toReal_sum_univ {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P : PMF Outcome) : ∑ w, (P w).toReal = 1 := by
  have h1 : (∑ w, P w) = 1 := by
    have htsum := P.tsum_coe
    rwa [tsum_fintype] at htsum
  have h2 : (∑ w, P w).toReal = (1 : ENNReal).toReal := by rw [h1]
  rw [ENNReal.toReal_sum (fun a _ => P.apply_ne_top a)] at h2
  simpa using h2

open Classical in
/-- Outcomes where `P` exceeds the `exp eps`-scaled `Q` mass. -/
noncomputable def excessSet {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) : Finset Outcome :=
  Finset.univ.filter (fun w => Real.exp eps * (Q w).toReal < (P w).toReal)

open Classical in
/-- Total excess mass of `P` over the scaled `Q` on `excessSet`. -/
noncomputable def excessMass {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) : ℝ :=
  ∑ w ∈ excessSet P Q eps, ((P w).toReal - Real.exp eps * (Q w).toReal)

/-- Pointwise capped envelope. -/
noncomputable def capEnvelope {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) : ℝ :=
  min ((P w).toReal) (Real.exp eps * (Q w).toReal)

open Classical in
theorem mem_excessSet {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) :
    w ∈ excessSet P Q eps ↔ Real.exp eps * (Q w).toReal < (P w).toReal := by
  simp [excessSet]

open Classical in
theorem excessMass_nonneg {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) : 0 ≤ excessMass P Q eps := by
  apply Finset.sum_nonneg
  intro w hw
  rw [mem_excessSet] at hw
  linarith

theorem capEnvelope_le_left {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) :
    capEnvelope P Q eps w ≤ (P w).toReal :=
  min_le_left _ _

theorem capEnvelope_le_right {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) :
    capEnvelope P Q eps w ≤ Real.exp eps * (Q w).toReal :=
  min_le_right _ _

theorem capEnvelope_nonneg {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) :
    0 ≤ capEnvelope P Q eps w := by
  apply le_min
  · exact ENNReal.toReal_nonneg
  · apply mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg

open Classical in
theorem capEnvelope_eq_left_of_not_mem {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (w : Outcome)
    (hw : w ∉ excessSet P Q eps) :
    capEnvelope P Q eps w = (P w).toReal := by
  have hle : (P w).toReal ≤ Real.exp eps * (Q w).toReal := by
    have h := mt (mem_excessSet P Q eps w).mpr hw
    exact le_of_not_gt h
  simp [capEnvelope, min_eq_left hle]

open Classical in
theorem capEnvelope_eq_right_of_mem {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (w : Outcome)
    (hw : w ∈ excessSet P Q eps) :
    capEnvelope P Q eps w = Real.exp eps * (Q w).toReal := by
  have hlt : Real.exp eps * (Q w).toReal < (P w).toReal :=
    (mem_excessSet P Q eps w).mp hw
  simp [capEnvelope, min_eq_right (le_of_lt hlt)]

open Classical in
theorem sum_capEnvelope {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) :
    ∑ w, capEnvelope P Q eps w = 1 - excessMass P Q eps := by
  classical
  have hS : excessSet P Q eps =
      Finset.univ.filter (fun w => Real.exp eps * (Q w).toReal < (P w).toReal) := rfl
  have hsplit_cap := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w => Real.exp eps * (Q w).toReal < (P w).toReal)
    (fun w => capEnvelope P Q eps w)
  have hsplit_p := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w => Real.exp eps * (Q w).toReal < (P w).toReal)
    (fun w => (P w).toReal)
  have hsumP := pmf_toReal_sum_univ P
  have hcapS : ∑ w ∈ excessSet P Q eps, capEnvelope P Q eps w =
      ∑ w ∈ excessSet P Q eps, Real.exp eps * (Q w).toReal := by
    apply Finset.sum_congr rfl
    intro w hw
    exact capEnvelope_eq_right_of_mem P Q eps w hw
  have hcapC : ∑ w ∈ Finset.univ.filter
      (fun w => ¬ Real.exp eps * (Q w).toReal < (P w).toReal),
      capEnvelope P Q eps w =
      ∑ w ∈ Finset.univ.filter
        (fun w => ¬ Real.exp eps * (Q w).toReal < (P w).toReal),
      (P w).toReal := by
    apply Finset.sum_congr rfl
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hnmem : w ∉ excessSet P Q eps := by
      intro hmem
      rw [mem_excessSet] at hmem
      exact hw hmem
    exact capEnvelope_eq_left_of_not_mem P Q eps w hnmem
  have hexp : excessMass P Q eps =
      (∑ w ∈ excessSet P Q eps, (P w).toReal) -
        Real.exp eps * ∑ w ∈ excessSet P Q eps, (Q w).toReal := by
    simp only [excessMass, Finset.sum_sub_distrib, Finset.mul_sum]
  have hcapS' : ∑ w ∈ excessSet P Q eps, capEnvelope P Q eps w =
      Real.exp eps * ∑ w ∈ excessSet P Q eps, (Q w).toReal := by
    rw [hcapS, Finset.mul_sum]
  rw [hS] at hcapS hcapS' hexp
  have hsplit_cap' : (∑ w ∈ Finset.univ.filter
      (fun w => Real.exp eps * (Q w).toReal < (P w).toReal),
      capEnvelope P Q eps w) +
      (∑ w ∈ Finset.univ.filter
        (fun w => ¬ Real.exp eps * (Q w).toReal < (P w).toReal),
      capEnvelope P Q eps w) = ∑ w, capEnvelope P Q eps w := hsplit_cap
  have hsplit_p' : (∑ w ∈ Finset.univ.filter
      (fun w => Real.exp eps * (Q w).toReal < (P w).toReal),
      (P w).toReal) +
      (∑ w ∈ Finset.univ.filter
        (fun w => ¬ Real.exp eps * (Q w).toReal < (P w).toReal),
      (P w).toReal) = ∑ w, (P w).toReal := hsplit_p
  rw [hsumP] at hsplit_p'
  rw [← hsplit_cap', ← hsplit_p', hcapC, hcapS', hexp]
  ring

open Classical in
theorem excessMass_le_delta {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps delta : ℝ)
    (h : approxMaxDivLE P Q eps delta) :
    excessMass P Q eps ≤ delta := by
  classical
  have hexp : excessMass P Q eps =
      (∑ w ∈ excessSet P Q eps, (P w).toReal) -
        Real.exp eps * ∑ w ∈ excessSet P Q eps, (Q w).toReal := by
    simp only [excessMass, Finset.sum_sub_distrib, Finset.mul_sum]
  have hS := h (excessSet P Q eps)
  rw [hexp]
  linarith

open Classical in
theorem sum_cq_minus_cap {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) :
    ∑ w, (Real.exp eps * (Q w).toReal - capEnvelope P Q eps w) =
      Real.exp eps - 1 + excessMass P Q eps := by
  classical
  have hsumQ := pmf_toReal_sum_univ Q
  have hsumCap := sum_capEnvelope P Q eps
  have h1 : ∑ w, (Real.exp eps * (Q w).toReal - capEnvelope P Q eps w) =
      (∑ w, Real.exp eps * (Q w).toReal) - ∑ w, capEnvelope P Q eps w := by
    rw [Finset.sum_sub_distrib]
  have h2 : (∑ w, Real.exp eps * (Q w).toReal) =
      Real.exp eps * ∑ w, (Q w).toReal := by
    rw [Finset.mul_sum]
  rw [h1, h2, hsumQ, hsumCap]
  ring

open Classical in
/-- Mixing coefficient for the repaired distribution. -/
noncomputable def repairCoeff {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) : ℝ :=
  excessMass P Q eps / (Real.exp eps - 1 + excessMass P Q eps)

open Classical in
theorem repairCoeff_denom_pos {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (hd : 0 < excessMass P Q eps) :
    0 < Real.exp eps - 1 + excessMass P Q eps := by
  have hc : (1 : ℝ) ≤ Real.exp eps := Real.one_le_exp heps
  linarith

open Classical in
theorem repairCoeff_nonneg {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (hd : 0 < excessMass P Q eps) :
    0 ≤ repairCoeff P Q eps := by
  apply div_nonneg (le_of_lt hd)
  exact le_of_lt (repairCoeff_denom_pos P Q eps heps hd)

open Classical in
theorem repairCoeff_le_one {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (hd : 0 < excessMass P Q eps) :
    repairCoeff P Q eps ≤ 1 := by
  have hc : (1 : ℝ) ≤ Real.exp eps := Real.one_le_exp heps
  have hpos := repairCoeff_denom_pos P Q eps heps hd
  simp only [repairCoeff]
  rw [div_le_one hpos]
  linarith

open Classical in
theorem repairCoeff_mul_denom {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (hd : 0 < excessMass P Q eps) :
    repairCoeff P Q eps * (Real.exp eps - 1 + excessMass P Q eps) =
      excessMass P Q eps := by
  simp only [repairCoeff]
  have hne : Real.exp eps - 1 + excessMass P Q eps ≠ 0 :=
    ne_of_gt (repairCoeff_denom_pos P Q eps heps hd)
  rw [div_mul_cancel₀ _ hne]

open Classical in
/-- Repaired pointwise masses. -/
noncomputable def repairFun {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) : ℝ :=
  capEnvelope P Q eps w + repairCoeff P Q eps *
    (Real.exp eps * (Q w).toReal - capEnvelope P Q eps w)

open Classical in
theorem repairFun_ge_cap {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (hd : 0 < excessMass P Q eps) (w : Outcome) :
    capEnvelope P Q eps w ≤ repairFun P Q eps w := by
  simp only [repairFun]
  have ht := repairCoeff_nonneg P Q eps heps hd
  have hgap : 0 ≤ Real.exp eps * (Q w).toReal - capEnvelope P Q eps w := by
    linarith [capEnvelope_le_right P Q eps w]
  linarith [mul_nonneg ht hgap]

open Classical in
theorem repairFun_le_cq {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (hd : 0 < excessMass P Q eps) (w : Outcome) :
    repairFun P Q eps w ≤ Real.exp eps * (Q w).toReal := by
  simp only [repairFun]
  have ht0 := repairCoeff_nonneg P Q eps heps hd
  have ht1 := repairCoeff_le_one P Q eps heps hd
  have hgap : 0 ≤ Real.exp eps * (Q w).toReal - capEnvelope P Q eps w := by
    linarith [capEnvelope_le_right P Q eps w]
  have hmul : repairCoeff P Q eps *
      (Real.exp eps * (Q w).toReal - capEnvelope P Q eps w) ≤
      Real.exp eps * (Q w).toReal - capEnvelope P Q eps w := by
    have := mul_le_mul_of_nonneg_right ht1 hgap
    simpa using this
  linarith

open Classical in
theorem repairFun_nonneg {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (hd : 0 < excessMass P Q eps) (w : Outcome) :
    0 ≤ repairFun P Q eps w := by
  exact le_trans (capEnvelope_nonneg P Q eps w)
    (repairFun_ge_cap P Q eps heps hd w)

open Classical in
theorem sum_repairFun {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (hd : 0 < excessMass P Q eps) :
    ∑ w, repairFun P Q eps w = 1 := by
  classical
  have hsumCap := sum_capEnvelope P Q eps
  have hgap := sum_cq_minus_cap P Q eps
  have hcoeff := repairCoeff_mul_denom P Q eps heps hd
  have h1 : ∑ w, repairFun P Q eps w =
      (∑ w, capEnvelope P Q eps w) + repairCoeff P Q eps *
        ∑ w, (Real.exp eps * (Q w).toReal - capEnvelope P Q eps w) := by
    simp only [repairFun, Finset.sum_add_distrib, Finset.mul_sum]
  rw [h1, hsumCap, hgap, hcoeff]
  ring

open Classical in
/-- Repaired distribution: `P` when excess is zero, else the envelope mixture. -/
noncomputable def repairPMF {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps) : PMF Outcome :=
  if hd : excessMass P Q eps = 0 then P
  else
    have hpos : 0 < excessMass P Q eps :=
      lt_of_le_of_ne (excessMass_nonneg P Q eps) (Ne.symm hd)
    PMF.ofFintype (fun w => ENNReal.ofReal (repairFun P Q eps w)) (by
      have hsum := sum_repairFun P Q eps heps hpos
      have hnn : ∀ i, i ∈ Finset.univ → 0 ≤ repairFun P Q eps i :=
        fun i _ => repairFun_nonneg P Q eps heps hpos i
      have hof := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun w => repairFun P Q eps w) hnn
      rw [hsum, ENNReal.ofReal_one] at hof
      exact hof.symm)

open Classical in
theorem repairPMF_apply_of_pos {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (hd : 0 < excessMass P Q eps) (w : Outcome) :
    ((repairPMF P Q eps heps w).toReal) = repairFun P Q eps w := by
  have hne : excessMass P Q eps ≠ 0 := ne_of_gt hd
  simp only [repairPMF, hne, dite_false]
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (repairFun_nonneg P Q eps heps hd w)

open Classical in
theorem repairPMF_maxDivLE_of_pos {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (hd : 0 < excessMass P Q eps) :
    maxDivLE (repairPMF P Q eps heps) Q eps := by
  intro w
  rw [repairPMF_apply_of_pos P Q eps heps hd w]
  exact repairFun_le_cq P Q eps heps hd w

theorem abs_sub_eq_add_sub_two_min (a b : ℝ) :
    |a - b| = a + b - 2 * min a b := by
  by_cases h : a ≤ b
  · simp [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
    ring
  · have hlt : b < a := lt_of_not_ge h
    simp [abs_of_pos (sub_pos.mpr hlt), min_eq_right (le_of_lt hlt)]
    ring

theorem tvDist_eq_one_minus_overlap {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P R : PMF Outcome) :
    tvDist P R = 1 - ∑ w, min ((P w).toReal) ((R w).toReal) := by
  simp only [tvDist]
  have hpt : ∀ w : Outcome,
      |(P w).toReal - (R w).toReal| =
        (P w).toReal + (R w).toReal - 2 * min ((P w).toReal) ((R w).toReal) :=
    fun w => abs_sub_eq_add_sub_two_min _ _
  have hsum : ∑ w, |(P w).toReal - (R w).toReal| =
      2 - 2 * ∑ w, min ((P w).toReal) ((R w).toReal) := by
    have h1 : ∑ w, |(P w).toReal - (R w).toReal| =
        ∑ w, ((P w).toReal + (R w).toReal -
          2 * min ((P w).toReal) ((R w).toReal)) :=
      Finset.sum_congr rfl (fun w _ => hpt w)
    rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
      pmf_toReal_sum_univ P, pmf_toReal_sum_univ R]
    ring
  rw [hsum]
  ring

theorem tvDist_self {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P : PMF Outcome) : tvDist P P = 0 := by
  simp only [tvDist]
  have : ∑ w, |(P w).toReal - (P w).toReal| = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    simp
  rw [this, mul_zero]

open Classical in
theorem repairPMF_tvDist_le_of_pos {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps delta : ℝ) (heps : 0 ≤ eps)
    (h : approxMaxDivLE P Q eps delta)
    (hd : 0 < excessMass P Q eps) :
    tvDist P (repairPMF P Q eps heps) ≤ delta := by
  classical
  have hover : ∑ w, capEnvelope P Q eps w ≤
      ∑ w, min ((P w).toReal) (((repairPMF P Q eps heps) w).toReal) := by
    apply Finset.sum_le_sum
    intro w _
    apply le_min
    · exact capEnvelope_le_left P Q eps w
    · rw [repairPMF_apply_of_pos P Q eps heps hd w]
      exact repairFun_ge_cap P Q eps heps hd w
  have htv := tvDist_eq_one_minus_overlap P (repairPMF P Q eps heps)
  have hcap := sum_capEnvelope P Q eps
  have hdle := excessMass_le_delta P Q eps delta h
  rw [htv]
  linarith

open Classical in
theorem maxDivLE_of_excess_eq_zero {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ)
    (hd : excessMass P Q eps = 0) :
    maxDivLE P Q eps := by
  classical
  have hempty : excessSet P Q eps = ∅ := by
    by_contra hne
    have hnonempty : (excessSet P Q eps).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hne
    have hpos : 0 < excessMass P Q eps := by
      simp only [excessMass]
      apply Finset.sum_pos
      · intro w hw
        rw [mem_excessSet] at hw
        linarith
      · exact hnonempty
    linarith
  intro w
  have hnmem : w ∉ excessSet P Q eps := by rw [hempty]; simp
  have h := mt (mem_excessSet P Q eps w).mpr hnmem
  exact le_of_not_gt h

open Classical in
/-- Forward direction: an approximate bound yields a repaired distribution. -/
theorem exists_repair_of_approx {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (h : approxMaxDivLE P Q eps delta) :
    ∃ Ptilde, tvDist P Ptilde ≤ delta ∧ maxDivLE Ptilde Q eps := by
  classical
  by_cases hd : excessMass P Q eps = 0
  · refine ⟨P, ?_, maxDivLE_of_excess_eq_zero P Q eps hd⟩
    rw [tvDist_self]
    exact hdelta
  · have hpos : 0 < excessMass P Q eps :=
      lt_of_le_of_ne (excessMass_nonneg P Q eps) (Ne.symm hd)
    exact ⟨repairPMF P Q eps heps,
      repairPMF_tvDist_le_of_pos P Q eps delta heps h hpos,
      repairPMF_maxDivLE_of_pos P Q eps heps hpos⟩

open Classical in
theorem event_diff_le_tvDist {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P R : PMF Outcome) (s : Finset Outcome) :
    (∑ w ∈ s, (P w).toReal) - (∑ w ∈ s, (R w).toReal) ≤ tvDist P R := by
  classical
  have hsub : s ⊆ Finset.univ := Finset.subset_univ s
  have hsplit : (∑ w ∈ Finset.univ \ s, ((P w).toReal - (R w).toReal)) +
      (∑ w ∈ s, ((P w).toReal - (R w).toReal)) =
      ∑ w, ((P w).toReal - (R w).toReal) :=
    Finset.sum_sdiff hsub
  have hsplit_abs : (∑ w ∈ Finset.univ \ s, |(P w).toReal - (R w).toReal|) +
      (∑ w ∈ s, |(P w).toReal - (R w).toReal|) =
      ∑ w, |(P w).toReal - (R w).toReal| :=
    Finset.sum_sdiff hsub
  have hsum0 : ∑ w, ((P w).toReal - (R w).toReal) = 0 := by
    rw [Finset.sum_sub_distrib, pmf_toReal_sum_univ P, pmf_toReal_sum_univ R,
      sub_self]
  have hdiff : (∑ w ∈ s, (P w).toReal) - (∑ w ∈ s, (R w).toReal) =
      ∑ w ∈ s, ((P w).toReal - (R w).toReal) := by
    rw [Finset.sum_sub_distrib]
  have habs1 : |∑ w ∈ s, ((P w).toReal - (R w).toReal)| ≤
      ∑ w ∈ s, |(P w).toReal - (R w).toReal| :=
    Finset.abs_sum_le_sum_abs _ _
  have habs2 : |∑ w ∈ Finset.univ \ s, ((P w).toReal - (R w).toReal)| ≤
      ∑ w ∈ Finset.univ \ s, |(P w).toReal - (R w).toReal| :=
    Finset.abs_sum_le_sum_abs _ _
  have hle : (∑ w ∈ s, ((P w).toReal - (R w).toReal)) -
      (∑ w ∈ Finset.univ \ s, ((P w).toReal - (R w).toReal)) ≤
      |∑ w ∈ s, ((P w).toReal - (R w).toReal)| +
        |∑ w ∈ Finset.univ \ s, ((P w).toReal - (R w).toReal)| := by
    have h1 : (∑ w ∈ s, ((P w).toReal - (R w).toReal)) ≤
        |∑ w ∈ s, ((P w).toReal - (R w).toReal)| := le_abs_self _
    have h2 : -(∑ w ∈ Finset.univ \ s, ((P w).toReal - (R w).toReal)) ≤
        |∑ w ∈ Finset.univ \ s, ((P w).toReal - (R w).toReal)| :=
      neg_le_abs _
    linarith
  simp only [tvDist]
  linarith [hsplit, hsplit_abs, hsum0, hdiff, habs1, habs2, hle]

open Classical in
/-- Backward direction: a repaired witness implies the approximate bound. -/
theorem approx_of_exists_repair {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps delta : ℝ)
    (Ptilde : PMF Outcome)
    (htv : tvDist P Ptilde ≤ delta)
    (hmax : maxDivLE Ptilde Q eps) :
    approxMaxDivLE P Q eps delta := by
  classical
  intro s
  have hdiff := event_diff_le_tvDist P Ptilde s
  have hsum : (∑ w ∈ s, (Ptilde w).toReal) ≤
      Real.exp eps * ∑ w ∈ s, (Q w).toReal := by
    have hpt : ∀ w ∈ s, (Ptilde w).toReal ≤ Real.exp eps * (Q w).toReal :=
      fun w _ => hmax w
    have hle := Finset.sum_le_sum hpt
    rw [Finset.mul_sum]
    exact hle
  linarith

/-- Zero-delta case: singleton events give a pure bound. -/
theorem maxDiv_of_approx_zero {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ)
    (h : approxMaxDivLE P Q eps 0) :
    maxDivLE P Q eps := by
  intro w
  have hsingle := h {w}
  simp only [Finset.sum_singleton] at hsingle
  linarith

open Classical in
theorem excess_eq_zero_of_approx_zero {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ)
    (h : approxMaxDivLE P Q eps 0) :
    excessMass P Q eps = 0 := by
  apply le_antisymm
  · exact excessMass_le_delta P Q eps 0 h
  · exact excessMass_nonneg P Q eps

end CSLibExt.Privacy.MaxDivergenceDecomposition
