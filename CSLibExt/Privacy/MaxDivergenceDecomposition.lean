/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.ApproximateDifferentialPrivacy
public import MathlibExt.Probability.MarkovChainContraction

/-!
# Approximate max-divergence decomposition (finite discrete)

Parts 1 and 2 of Dwork and Roth, Section 3.5.1, Lemma 3.17, over a
finite outcome type. Part 1: an approximate max-divergence bound
yields a repaired distribution `P~` within total variation `δ` of
`P` with pure max-divergence `D∞ (P~‖Q) ≤ ε`. Part 2: the two
approximate bounds together hold exactly when two witnesses `P'`,
`Q'` within `δ / (exp ε + 1)` of `P`, `Q` satisfy the pure bound in
both directions (`approxMaxDivLE_both_iff_exists_repair`).

Finite outcome scope: `[Fintype Outcome] [Nonempty Outcome]`. Total
variation is the shared `MarkovChainContraction.tvDist`. The finite
`Finset`-sum predicates below are connected to the
`IsApproxDP`/`toOuterMeasure` form by bridge theorems in both
directions.
-/

@[expose] public section

namespace CSLibExt.Privacy.MaxDivergenceDecomposition

open MathlibExt.Probability.MarkovChainContraction

/-- Finite approximate max-divergence bound. -/
def approxMaxDivLE {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps delta : ℝ) : Prop :=
  ∀ s : Finset Outcome,
    ∑ w ∈ s, (P w).toReal ≤ Real.exp eps * ∑ w ∈ s, (Q w).toReal + delta

/-- Finite pure max-divergence bound. -/
def maxDivLE {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (P Q : PMF Outcome) (eps : ℝ) : Prop :=
  ∀ w, (P w).toReal ≤ Real.exp eps * (Q w).toReal

/-- Unfolding of the shared total variation distance on `toReal` masses. -/
private theorem tvDist_unfold {Outcome : Type*} [Fintype Outcome] (P R : PMF Outcome) :
    tvDist P R = (1 / 2) * ∑ w, |(P w).toReal - (R w).toReal| :=
  rfl

/-- Real masses of a finite PMF sum to one; a local specialization of
`MathlibExt.Probability.FiniteProbability.sum_toReal_eq_one` kept private to avoid a
parallel public API. -/
private theorem pmf_toReal_sum_univ {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
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

private theorem abs_sub_eq_add_sub_two_min (a b : ℝ) :
    |a - b| = a + b - 2 * min a b := by
  by_cases h : a ≤ b
  · simp [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
    ring
  · have hlt : b < a := lt_of_not_ge h
    simp [abs_of_pos (sub_pos.mpr hlt), min_eq_right (le_of_lt hlt)]
    ring

private theorem tvDist_eq_one_minus_overlap {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P R : PMF Outcome) :
    tvDist P R = 1 - ∑ w, min ((P w).toReal) ((R w).toReal) := by
  rw [tvDist_unfold]
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
    have h0 : tvDist P P = 0 :=
      MathlibExt.Probability.MarkovMixing.tvDist_self _
    rw [h0]
    exact hdelta
  · have hpos : 0 < excessMass P Q eps :=
      lt_of_le_of_ne (excessMass_nonneg P Q eps) (Ne.symm hd)
    exact ⟨repairPMF P Q eps heps,
      repairPMF_tvDist_le_of_pos P Q eps delta heps h hpos,
      repairPMF_maxDivLE_of_pos P Q eps heps hpos⟩

open Classical in
/-- Event mass difference bounded by total variation. This specializes the canonical
`MathlibExt.Probability.MulticommodityFlow.sum_sub_le_tvDist` (mass functions swapped);
kept private to this module. -/
private theorem event_diff_le_tvDist {Outcome : Type*} [Fintype Outcome]
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
  rw [tvDist_unfold]
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

/-- Outer measure of a finite set is the real mass sum. -/
private theorem toOuterMeasure_coe_finset {Outcome : Type*} (P : PMF Outcome)
    (s : Finset Outcome) :
    P.toOuterMeasure ↑s = ENNReal.ofReal (∑ w ∈ s, (P w).toReal) := by
  rw [PMF.toOuterMeasure_apply_finset,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => ENNReal.toReal_nonneg)]
  apply Finset.sum_congr rfl
  intro a ha
  exact (ENNReal.ofReal_toReal (P.apply_ne_top a)).symm

/-- Event privacy implies the finite approximate bound. -/
theorem approxMaxDivLE_of_isApproxDP {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome]
    {D : Type*} {M : D → PMF Outcome} {adj : D → D → Prop} {eps delta : ℝ}
    (h : CSLibExt.Privacy.DifferentialPrivacy.IsApproxDP M adj eps delta)
    {d d' : D} (hadj : adj d d') :
    approxMaxDivLE (M d) (M d') eps delta := by
  intro s
  have hset := h.2.2 d d' hadj ↑s
  rw [toOuterMeasure_coe_finset, toOuterMeasure_coe_finset] at hset
  have hnn : 0 ≤ ∑ w ∈ s, ((M d') w).toReal :=
    Finset.sum_nonneg fun w _ => ENNReal.toReal_nonneg
  have hcombine : ENNReal.ofReal (Real.exp eps) *
        ENNReal.ofReal (∑ w ∈ s, ((M d') w).toReal) + ENNReal.ofReal delta =
      ENNReal.ofReal
        (Real.exp eps * (∑ w ∈ s, ((M d') w).toReal) + delta) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos eps).le,
      ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos eps).le hnn) h.2.1]
  rw [hcombine] at hset
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (mul_nonneg (Real.exp_pos eps).le hnn) h.2.1)).mp hset

/-- The finite bound for all adjacent pairs gives event privacy. -/
theorem isApproxDP_of_forall_approxMaxDivLE {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome]
    {D : Type*} (M : D → PMF Outcome) (adj : D → D → Prop)
    {eps delta : ℝ} (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (h : ∀ d d', adj d d' → approxMaxDivLE (M d) (M d') eps delta) :
    CSLibExt.Privacy.DifferentialPrivacy.IsApproxDP M adj eps delta := by
  classical
  refine ⟨heps, hdelta, fun d d' hadj s => ?_⟩
  set t : Finset Outcome := Finset.univ.filter (fun w => w ∈ s) with ht
  have hreal := h d d' hadj t
  have hcoe : ↑t = s := by
    ext w
    simp [ht]
  rw [← hcoe, toOuterMeasure_coe_finset, toOuterMeasure_coe_finset]
  have hnn : 0 ≤ ∑ w ∈ t, ((M d') w).toReal :=
    Finset.sum_nonneg fun w _ => ENNReal.toReal_nonneg
  have hcombine : ENNReal.ofReal (Real.exp eps) *
        ENNReal.ofReal (∑ w ∈ t, ((M d') w).toReal) + ENNReal.ofReal delta =
      ENNReal.ofReal (Real.exp eps * (∑ w ∈ t, ((M d') w).toReal) + delta) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos eps).le,
      ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos eps).le hnn) hdelta]
  rw [hcombine]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Repair from event privacy directly. -/
theorem exists_repair_of_isApproxDP {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] {D : Type*} {M : D → PMF Outcome}
    {adj : D → D → Prop} {eps delta : ℝ}
    (h : CSLibExt.Privacy.DifferentialPrivacy.IsApproxDP M adj eps delta)
    {d d' : D} (hadj : adj d d') :
    ∃ Ptilde, tvDist (M d) Ptilde ≤ delta ∧ maxDivLE Ptilde (M d') eps :=
  exists_repair_of_approx (M d) (M d') eps delta h.1 h.2.1
    (approxMaxDivLE_of_isApproxDP h hadj)

/-
Part 2 of Dwork-Roth Lemma 3.17 (§3.5.1): simultaneous repair.

The book prints a one-directional pure bound in the conclusion, but the
iff with a one-directional pure bound is false (e.g. `ε = log 2`,
`δ = 0`, `P = (1, 0)`, `Q = (1/2, 1/2)` satisfies the one-directional
conclusion with zero movement while the reverse approximate bound
fails). The formal statement therefore requires `maxDivLE` in BOTH
directions for the SAME witnesses; this deviation is deliberate.
-/

/-- Balanced lower envelope: per-atom mean mass over `exp ε + 1`. -/
private noncomputable def repair2L {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) : ℝ :=
  ((P w).toReal + (Q w).toReal) / (Real.exp eps + 1)

/-- Balanced upper envelope: `exp ε` times the lower envelope. -/
private noncomputable def repair2U {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) : ℝ :=
  Real.exp eps * repair2L P Q eps w

/-- `P` masses clamped into the balanced interval. -/
private noncomputable def repair2R {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) : ℝ :=
  min (max ((P w).toReal) (repair2L P Q eps w)) (repair2U P Q eps w)

private theorem exp_add_one_pos (eps : ℝ) : (0:ℝ) < Real.exp eps + 1 := by
  linarith [Real.exp_pos eps]

private theorem repair2L_nonneg {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) :
    0 ≤ repair2L P Q eps w := by
  simp only [repair2L]
  exact div_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (le_of_lt (exp_add_one_pos eps))

private theorem repair2L_le_U {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (w : Outcome) :
    repair2L P Q eps w ≤ repair2U P Q eps w := by
  have h1 : (1:ℝ) ≤ Real.exp eps := Real.one_le_exp heps
  have hL := repair2L_nonneg P Q eps w
  calc repair2L P Q eps w = 1 * repair2L P Q eps w := (one_mul _).symm
    _ ≤ Real.exp eps * repair2L P Q eps w :=
        mul_le_mul_of_nonneg_right h1 hL
    _ = repair2U P Q eps w := rfl

private theorem repair2R_ge_L {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (w : Outcome) :
    repair2L P Q eps w ≤ repair2R P Q eps w := by
  simp only [repair2R]
  exact le_min (le_max_right _ _) (repair2L_le_U P Q eps heps w)

private theorem repair2R_le_U {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (w : Outcome) :
    repair2R P Q eps w ≤ repair2U P Q eps w := by
  simp only [repair2R]
  exact min_le_right _ _

private theorem not_mem_excess_both {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (w : Outcome) (hPQ : w ∈ excessSet P Q eps)
    (hQP : w ∈ excessSet Q P eps) : False := by
  rw [mem_excessSet] at hPQ hQP
  have ha1 : (1:ℝ) ≤ Real.exp eps := Real.one_le_exp heps
  have hapos : (0:ℝ) < Real.exp eps := Real.exp_pos eps
  have hpnn : (0:ℝ) ≤ (P w).toReal := ENNReal.toReal_nonneg
  have hsq : Real.exp eps * (Real.exp eps * (P w).toReal) < (P w).toReal := by
    calc Real.exp eps * (Real.exp eps * (P w).toReal)
        < Real.exp eps * (Q w).toReal :=
          mul_lt_mul_of_pos_left hQP hapos
      _ < (P w).toReal := hPQ
  have hge : (P w).toReal ≤
      Real.exp eps * (Real.exp eps * (P w).toReal) := by
    have haa : (1:ℝ) ≤ Real.exp eps * Real.exp eps := by
      calc (1:ℝ) = 1 * 1 := (mul_one 1).symm
        _ ≤ Real.exp eps * Real.exp eps :=
            mul_le_mul ha1 ha1 zero_le_one (le_of_lt hapos)
    calc (P w).toReal = 1 * (P w).toReal := (one_mul _).symm
      _ ≤ (Real.exp eps * Real.exp eps) * (P w).toReal :=
          mul_le_mul_of_nonneg_right haa hpnn
      _ = Real.exp eps * (Real.exp eps * (P w).toReal) := by ring
  linarith

private theorem repair2L_le_of_mem {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (w : Outcome) (hw : w ∈ excessSet P Q eps) :
    repair2L P Q eps w ≤ (P w).toReal := by
  have ha1 : (1:ℝ) ≤ Real.exp eps := Real.one_le_exp heps
  have hc := exp_add_one_pos eps
  have hpnn : (0:ℝ) ≤ (P w).toReal := ENNReal.toReal_nonneg
  have hqnn : (0:ℝ) ≤ (Q w).toReal := ENNReal.toReal_nonneg
  rw [mem_excessSet] at hw
  have hqa : (Q w).toReal ≤ Real.exp eps * (P w).toReal :=
    le_trans (le_mul_of_one_le_left hqnn ha1)
      (le_trans (le_of_lt hw) (le_mul_of_one_le_left hpnn ha1))
  simp only [repair2L]
  rw [div_le_iff₀ hc]
  linarith [hqa]

private theorem repair2U_le_of_mem {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ)
    (w : Outcome) (hw : w ∈ excessSet P Q eps) :
    repair2U P Q eps w ≤ (P w).toReal := by
  have hc := exp_add_one_pos eps
  rw [mem_excessSet] at hw
  simp only [repair2U, repair2L, ← mul_div_assoc, div_le_iff₀ hc]
  linarith [le_of_lt hw]

private theorem repair2R_eq_U_of_mem {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (w : Outcome) (hw : w ∈ excessSet P Q eps) :
    repair2R P Q eps w = repair2U P Q eps w := by
  simp only [repair2R, max_eq_left (repair2L_le_of_mem P Q eps heps w hw),
    min_eq_right (repair2U_le_of_mem P Q eps w hw)]

private theorem repair2L_ge_of_mem_swap {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (w : Outcome)
    (hw : w ∈ excessSet Q P eps) :
    (P w).toReal ≤ repair2L P Q eps w := by
  have hc := exp_add_one_pos eps
  rw [mem_excessSet] at hw
  simp only [repair2L]
  rw [le_div_iff₀ hc]
  linarith [le_of_lt hw]

private theorem repair2R_eq_L_of_mem_swap {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps)
    (w : Outcome) (hw : w ∈ excessSet Q P eps) :
    repair2R P Q eps w = repair2L P Q eps w := by
  simp only [repair2R, max_eq_right (repair2L_ge_of_mem_swap P Q eps w hw),
    min_eq_left (repair2L_le_U P Q eps heps w)]

private theorem repair2R_eq_of_not_mem {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (w : Outcome)
    (hPQ : w ∉ excessSet P Q eps) (hQP : w ∉ excessSet Q P eps) :
    repair2R P Q eps w = (P w).toReal := by
  have hc := exp_add_one_pos eps
  have hle1 : (P w).toReal ≤ Real.exp eps * (Q w).toReal := by
    have h := mt (mem_excessSet P Q eps w).mpr hPQ
    exact le_of_not_gt h
  have hle2 : (Q w).toReal ≤ Real.exp eps * (P w).toReal := by
    have h := mt (mem_excessSet Q P eps w).mpr hQP
    exact le_of_not_gt h
  have hLp : repair2L P Q eps w ≤ (P w).toReal := by
    simp only [repair2L]
    rw [div_le_iff₀ hc]
    linarith [hle2]
  have hUp : (P w).toReal ≤ repair2U P Q eps w := by
    simp only [repair2U, repair2L, ← mul_div_assoc, le_div_iff₀ hc]
    linarith [hle1]
  simp only [repair2R, max_eq_left hLp, min_eq_left hUp]

private theorem sum_repair2R_sub {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps) :
    (∑ w, repair2R P Q eps w) - 1 =
      (excessMass Q P eps - excessMass P Q eps) / (Real.exp eps + 1) := by
  classical
  have hc0 : Real.exp eps + 1 ≠ 0 := ne_of_gt (exp_add_one_pos eps)
  have hdisj : Disjoint (excessSet P Q eps) (excessSet Q P eps) :=
    Finset.disjoint_left.mpr (fun w hPQ hQP =>
      not_mem_excess_both P Q eps heps w hPQ hQP)
  have hvan : ∀ w ∈ (Finset.univ : Finset Outcome),
      w ∉ excessSet P Q eps ∪ excessSet Q P eps →
      repair2R P Q eps w - (P w).toReal = 0 := by
    intro w _ hw
    rw [Finset.mem_union, not_or] at hw
    rw [repair2R_eq_of_not_mem P Q eps w hw.1 hw.2, sub_self]
  have hsplit : ∑ w, (repair2R P Q eps w - (P w).toReal) =
      (∑ w ∈ excessSet P Q eps, (repair2R P Q eps w - (P w).toReal)) +
      (∑ w ∈ excessSet Q P eps, (repair2R P Q eps w - (P w).toReal)) := by
    have hsub := Finset.sum_subset (Finset.subset_univ
      (excessSet P Q eps ∪ excessSet Q P eps)) hvan
    rw [Finset.sum_union hdisj] at hsub
    exact hsub.symm
  have hP : ∀ w ∈ excessSet P Q eps,
      repair2R P Q eps w - (P w).toReal =
        (Real.exp eps * (Q w).toReal - (P w).toReal) / (Real.exp eps + 1) := by
    intro w hw
    rw [repair2R_eq_U_of_mem P Q eps heps w hw]
    simp only [repair2U, repair2L]
    field_simp
    ring
  have hQ : ∀ w ∈ excessSet Q P eps,
      repair2R P Q eps w - (P w).toReal =
        ((Q w).toReal - Real.exp eps * (P w).toReal) / (Real.exp eps + 1) := by
    intro w hw
    rw [repair2R_eq_L_of_mem_swap P Q eps heps w hw]
    simp only [repair2L]
    field_simp
    ring
  have hexpPQ : excessMass P Q eps =
      (∑ w ∈ excessSet P Q eps, (P w).toReal) -
        Real.exp eps * ∑ w ∈ excessSet P Q eps, (Q w).toReal := by
    simp only [excessMass, Finset.sum_sub_distrib, Finset.mul_sum]
  have hexpQP : excessMass Q P eps =
      (∑ w ∈ excessSet Q P eps, (Q w).toReal) -
        Real.exp eps * ∑ w ∈ excessSet Q P eps, (P w).toReal := by
    simp only [excessMass, Finset.sum_sub_distrib, Finset.mul_sum]
  have hfactor : ∀ (s : Finset Outcome) (f : Outcome → ℝ),
      (∑ w ∈ s, f w / (Real.exp eps + 1)) =
        (Real.exp eps + 1)⁻¹ * ∑ w ∈ s, f w := by
    intro s f
    have hterm : ∀ w ∈ s, f w / (Real.exp eps + 1) =
        (Real.exp eps + 1)⁻¹ * f w := by
      intro w _
      simp only [div_eq_mul_inv]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hPsum : ∑ w ∈ excessSet P Q eps,
      (repair2R P Q eps w - (P w).toReal) =
      -(excessMass P Q eps) / (Real.exp eps + 1) := by
    rw [Finset.sum_congr rfl hP,
      hfactor _ (fun w => Real.exp eps * (Q w).toReal - (P w).toReal),
      Finset.sum_sub_distrib, ← Finset.mul_sum, hexpPQ, div_eq_mul_inv]
    ring
  have hQsum : ∑ w ∈ excessSet Q P eps,
      (repair2R P Q eps w - (P w).toReal) =
      (excessMass Q P eps) / (Real.exp eps + 1) := by
    rw [Finset.sum_congr rfl hQ,
      hfactor _ (fun w => (Q w).toReal - Real.exp eps * (P w).toReal),
      Finset.sum_sub_distrib, ← Finset.mul_sum, hexpQP, div_eq_mul_inv]
    ring
  have htot : ∑ w, (repair2R P Q eps w - (P w).toReal) =
      (excessMass Q P eps - excessMass P Q eps) / (Real.exp eps + 1) := by
    rw [hsplit, hPsum, hQsum]
    ring
  have hdecomp : ∑ w, (repair2R P Q eps w - (P w).toReal) =
      (∑ w, repair2R P Q eps w) - 1 := by
    rw [Finset.sum_sub_distrib, pmf_toReal_sum_univ P]
  rw [← hdecomp, htot]

private theorem sum_abs_sub_repair2R {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps) :
    ∑ w, |(P w).toReal - repair2R P Q eps w| =
      (excessMass P Q eps + excessMass Q P eps) / (Real.exp eps + 1) := by
  classical
  have hc0 : Real.exp eps + 1 ≠ 0 := ne_of_gt (exp_add_one_pos eps)
  have hdisj : Disjoint (excessSet P Q eps) (excessSet Q P eps) :=
    Finset.disjoint_left.mpr (fun w hPQ hQP =>
      not_mem_excess_both P Q eps heps w hPQ hQP)
  have hvan : ∀ w ∈ (Finset.univ : Finset Outcome),
      w ∉ excessSet P Q eps ∪ excessSet Q P eps →
      |(P w).toReal - repair2R P Q eps w| = 0 := by
    intro w _ hw
    rw [Finset.mem_union, not_or] at hw
    rw [repair2R_eq_of_not_mem P Q eps w hw.1 hw.2, sub_self, abs_zero]
  have hsplit : ∑ w, |(P w).toReal - repair2R P Q eps w| =
      (∑ w ∈ excessSet P Q eps, |(P w).toReal - repair2R P Q eps w|) +
      (∑ w ∈ excessSet Q P eps, |(P w).toReal - repair2R P Q eps w|) := by
    have hsub := Finset.sum_subset (Finset.subset_univ
      (excessSet P Q eps ∪ excessSet Q P eps)) hvan
    rw [Finset.sum_union hdisj] at hsub
    exact hsub.symm
  have hP : ∀ w ∈ excessSet P Q eps,
      |(P w).toReal - repair2R P Q eps w| =
        ((P w).toReal - Real.exp eps * (Q w).toReal) / (Real.exp eps + 1) := by
    intro w hw
    rw [repair2R_eq_U_of_mem P Q eps heps w hw,
      abs_of_nonneg (sub_nonneg.mpr (repair2U_le_of_mem P Q eps w hw))]
    simp only [repair2U, repair2L]
    field_simp
    ring
  have hQ : ∀ w ∈ excessSet Q P eps,
      |(P w).toReal - repair2R P Q eps w| =
        ((Q w).toReal - Real.exp eps * (P w).toReal) / (Real.exp eps + 1) := by
    intro w hw
    rw [repair2R_eq_L_of_mem_swap P Q eps heps w hw,
      abs_of_nonpos (sub_nonpos.mpr (repair2L_ge_of_mem_swap P Q eps w hw))]
    simp only [repair2L]
    field_simp
    ring
  have hexpPQ : excessMass P Q eps =
      (∑ w ∈ excessSet P Q eps, (P w).toReal) -
        Real.exp eps * ∑ w ∈ excessSet P Q eps, (Q w).toReal := by
    simp only [excessMass, Finset.sum_sub_distrib, Finset.mul_sum]
  have hexpQP : excessMass Q P eps =
      (∑ w ∈ excessSet Q P eps, (Q w).toReal) -
        Real.exp eps * ∑ w ∈ excessSet Q P eps, (P w).toReal := by
    simp only [excessMass, Finset.sum_sub_distrib, Finset.mul_sum]
  have hfactor : ∀ (s : Finset Outcome) (f : Outcome → ℝ),
      (∑ w ∈ s, f w / (Real.exp eps + 1)) =
        (Real.exp eps + 1)⁻¹ * ∑ w ∈ s, f w := by
    intro s f
    have hterm : ∀ w ∈ s, f w / (Real.exp eps + 1) =
        (Real.exp eps + 1)⁻¹ * f w := by
      intro w _
      simp only [div_eq_mul_inv]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hPsum : ∑ w ∈ excessSet P Q eps, |(P w).toReal - repair2R P Q eps w| =
      (excessMass P Q eps) / (Real.exp eps + 1) := by
    rw [Finset.sum_congr rfl hP,
      hfactor _ (fun w => (P w).toReal - Real.exp eps * (Q w).toReal),
      Finset.sum_sub_distrib, ← Finset.mul_sum, hexpPQ, div_eq_mul_inv]
    ring
  have hQsum : ∑ w ∈ excessSet Q P eps, |(P w).toReal - repair2R P Q eps w| =
      (excessMass Q P eps) / (Real.exp eps + 1) := by
    rw [Finset.sum_congr rfl hQ,
      hfactor _ (fun w => (Q w).toReal - Real.exp eps * (P w).toReal),
      Finset.sum_sub_distrib, ← Finset.mul_sum, hexpQP, div_eq_mul_inv]
    ring
  rw [hsplit, hPsum, hQsum]
  ring

private theorem sum_repair2L {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) :
    ∑ w, repair2L P Q eps w = 2 / (Real.exp eps + 1) := by
  have hsum : ∑ w, ((P w).toReal + (Q w).toReal) = 2 := by
    rw [Finset.sum_add_distrib, pmf_toReal_sum_univ P, pmf_toReal_sum_univ Q]
    norm_num
  have hterm : ∀ w ∈ (Finset.univ : Finset Outcome), repair2L P Q eps w =
      (Real.exp eps + 1)⁻¹ * ((P w).toReal + (Q w).toReal) := by
    intro w _
    simp only [repair2L, div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum, div_eq_mul_inv]
  ring

private theorem sum_repair2U {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps : ℝ) :
    ∑ w, repair2U P Q eps w = Real.exp eps * (2 / (Real.exp eps + 1)) := by
  simp only [repair2U, ← Finset.mul_sum, sum_repair2L]

private theorem add_add_abs_eq_two_max (A B : ℝ) :
    A + B + |A - B| = 2 * max A B := by
  rcases le_total A B with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_right h]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left h]
    ring

private theorem exists_interp_sum_one {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (lo hi r : Outcome → ℝ)
    (hlo : ∀ w, lo w ≤ r w) (hhi : ∀ w, r w ≤ hi w)
    (hlo_sum : ∑ w, lo w ≤ 1) (hhi_sum : 1 ≤ ∑ w, hi w) :
    ∃ r' : Outcome → ℝ, (∀ w, lo w ≤ r' w) ∧ (∀ w, r' w ≤ hi w) ∧
      (∑ w, r' w = 1) ∧ (∑ w, |r w - r' w| = |1 - ∑ w, r w|) := by
  by_cases h1 : ∑ w, r w = 1
  · refine ⟨r, hlo, hhi, h1, ?_⟩
    simp only [sub_self, abs_zero, Finset.sum_const_zero]
    rw [h1, sub_self, abs_zero]
  · by_cases hlt : ∑ w, r w < 1
    · -- Push up toward `hi`.
      have hD : (0:ℝ) < (∑ w, hi w) - ∑ w, r w := by linarith [hhi_sum, hlt]
      have hD0 : (∑ w, hi w) - ∑ w, r w ≠ 0 := ne_of_gt hD
      set lam : ℝ := (1 - ∑ w, r w) / ((∑ w, hi w) - ∑ w, r w) with hlam
      have hlam0 : (0:ℝ) ≤ lam := by
        rw [hlam]
        exact div_nonneg (by linarith [hlt]) (le_of_lt hD)
      have hlam1 : lam ≤ 1 := by
        rw [hlam, div_le_one hD]
        linarith [hhi_sum]
      have hcancel : lam * ((∑ w, hi w) - ∑ w, r w) = 1 - ∑ w, r w := by
        rw [hlam, div_mul_cancel₀ _ hD0]
      have hsum1 : (∑ w, (r w + lam * (hi w - r w))) = 1 := by
        have hsum : (∑ w, (r w + lam * (hi w - r w))) =
            (∑ w, r w) + lam * ((∑ w, hi w) - ∑ w, r w) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
        rw [hsum, hcancel]
        ring
      refine ⟨fun w => r w + lam * (hi w - r w), ?_, ?_, hsum1, ?_⟩
      · intro w
        show lo w ≤ r w + lam * (hi w - r w)
        have hnn : (0:ℝ) ≤ lam * (hi w - r w) :=
          mul_nonneg hlam0 (sub_nonneg.mpr (hhi w))
        linarith [hlo w, hnn]
      · intro w
        show r w + lam * (hi w - r w) ≤ hi w
        have hle : lam * (hi w - r w) ≤ hi w - r w := by
          have h := mul_le_mul_of_nonneg_right hlam1 (sub_nonneg.mpr (hhi w))
          simpa using h
        linarith [hle]
      · show (∑ w, |r w - (r w + lam * (hi w - r w))|) = |1 - ∑ w, r w|
        have hpt : ∀ w ∈ (Finset.univ : Finset Outcome),
            |r w - (r w + lam * (hi w - r w))| =
              ((r w + lam * (hi w - r w)) - r w) := by
          intro w _
          have hle : r w - (r w + lam * (hi w - r w)) ≤ 0 := by
            have hnn : (0:ℝ) ≤ lam * (hi w - r w) :=
              mul_nonneg hlam0 (sub_nonneg.mpr (hhi w))
            linarith [hnn]
          rw [abs_of_nonpos hle]
          ring
        rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, hsum1,
          abs_of_pos (by linarith [hlt] : (0:ℝ) < 1 - ∑ w, r w)]
    · -- Push down toward `lo`.
      have hgt : (1:ℝ) < ∑ w, r w :=
        lt_of_le_of_ne' (le_of_not_gt hlt) h1
      have hD : (0:ℝ) < (∑ w, r w) - ∑ w, lo w := by linarith [hlo_sum, hgt]
      have hD0 : (∑ w, r w) - ∑ w, lo w ≠ 0 := ne_of_gt hD
      set lam : ℝ := ((∑ w, r w) - 1) / ((∑ w, r w) - ∑ w, lo w) with hlam
      have hlam0 : (0:ℝ) ≤ lam := by
        rw [hlam]
        exact div_nonneg (by linarith [hgt]) (le_of_lt hD)
      have hlam1 : lam ≤ 1 := by
        rw [hlam, div_le_one hD]
        linarith [hlo_sum]
      have hcancel : lam * ((∑ w, lo w) - ∑ w, r w) = -((∑ w, r w) - 1) := by
        have hpos : lam * ((∑ w, r w) - ∑ w, lo w) = (∑ w, r w) - 1 := by
          rw [hlam, div_mul_cancel₀ _ hD0]
        have hneg : lam * ((∑ w, lo w) - ∑ w, r w) =
            -(lam * ((∑ w, r w) - ∑ w, lo w)) := by ring
        rw [hneg, hpos]
      have hsum1 : (∑ w, (r w + lam * (lo w - r w))) = 1 := by
        have hsum : (∑ w, (r w + lam * (lo w - r w))) =
            (∑ w, r w) + lam * ((∑ w, lo w) - ∑ w, r w) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
        rw [hsum, hcancel]
        ring
      refine ⟨fun w => r w + lam * (lo w - r w), ?_, ?_, hsum1, ?_⟩
      · intro w
        show lo w ≤ r w + lam * (lo w - r w)
        have hle : lam * (r w - lo w) ≤ 1 * (r w - lo w) :=
          mul_le_mul_of_nonneg_right hlam1 (sub_nonneg.mpr (hlo w))
        linarith [hle]
      · intro w
        show r w + lam * (lo w - r w) ≤ hi w
        have hle : lam * (lo w - r w) ≤ lam * 0 :=
          mul_le_mul_of_nonneg_left (sub_nonpos.mpr (hlo w)) hlam0
        simp only [mul_zero] at hle
        linarith [hle, hhi w]
      · show (∑ w, |r w - (r w + lam * (lo w - r w))|) = |1 - ∑ w, r w|
        have hpt : ∀ w ∈ (Finset.univ : Finset Outcome),
            |r w - (r w + lam * (lo w - r w))| =
              (r w - (r w + lam * (lo w - r w))) := by
          intro w _
          apply abs_of_nonneg
          have hle : lam * (lo w - r w) ≤ lam * 0 :=
            mul_le_mul_of_nonneg_left (sub_nonpos.mpr (hlo w)) hlam0
          simp only [mul_zero] at hle
          linarith [hle]
        rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, hsum1,
          abs_of_neg (by linarith [hgt] : (1:ℝ) - ∑ w, r w < 0)]
        ring

private theorem tvDist_symm {Outcome : Type*} [Fintype Outcome]
    (P Q : PMF Outcome) : tvDist P Q = tvDist Q P :=
  MathlibExt.Probability.MarkovMixing.tvDist_comm _ _

private theorem approx_of_repair_pair {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps delta : ℝ)
    (P' Q' : PMF Outcome)
    (htvP : tvDist P P' ≤ delta / (Real.exp eps + 1))
    (htvQ : tvDist Q Q' ≤ delta / (Real.exp eps + 1))
    (hmax : maxDivLE P' Q' eps) :
    approxMaxDivLE P Q eps delta := by
  have hapos : (0:ℝ) < Real.exp eps := Real.exp_pos eps
  have hc0 : Real.exp eps + 1 ≠ 0 := ne_of_gt (exp_add_one_pos eps)
  intro s
  have hdiff1 := event_diff_le_tvDist P P' s
  have hdiff2 := event_diff_le_tvDist Q' Q s
  rw [tvDist_symm Q' Q] at hdiff2
  have hsum : (∑ w ∈ s, (P' w).toReal) ≤
      Real.exp eps * ∑ w ∈ s, (Q' w).toReal := by
    have hpt : ∀ w ∈ s, (P' w).toReal ≤ Real.exp eps * (Q' w).toReal :=
      fun w _ => hmax w
    have hle := Finset.sum_le_sum hpt
    rw [Finset.mul_sum]
    exact hle
  have hQ'a : Real.exp eps * (∑ w ∈ s, (Q' w).toReal) ≤
      Real.exp eps * (∑ w ∈ s, (Q w).toReal) +
        Real.exp eps * tvDist Q Q' := by
    have hle : (∑ w ∈ s, (Q' w).toReal) ≤
        (∑ w ∈ s, (Q w).toReal) + tvDist Q Q' := by linarith [hdiff2]
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hapos)
    rw [mul_add] at hmul
    exact hmul
  have hdtv : Real.exp eps * tvDist Q Q' + tvDist P P' ≤ delta := by
    have hbase : Real.exp eps * (delta / (Real.exp eps + 1)) +
        delta / (Real.exp eps + 1) = delta := by
      field_simp
    calc Real.exp eps * tvDist Q Q' + tvDist P P'
        ≤ Real.exp eps * (delta / (Real.exp eps + 1)) +
            delta / (Real.exp eps + 1) := by
          apply add_le_add _ htvP
          exact mul_le_mul_of_nonneg_left htvQ (le_of_lt hapos)
      _ = delta := hbase
  have hPs : (∑ w ∈ s, (P w).toReal) ≤
      (∑ w ∈ s, (P' w).toReal) + tvDist P P' := by linarith [hdiff1]
  linarith [hPs, hsum, hQ'a, hdtv]

private theorem approx_both_of_exists_repair_both {Outcome : Type*}
    [Fintype Outcome] [Nonempty Outcome] (P Q : PMF Outcome) (eps delta : ℝ)
    (P' Q' : PMF Outcome)
    (htvP : tvDist P P' ≤ delta / (Real.exp eps + 1))
    (htvQ : tvDist Q Q' ≤ delta / (Real.exp eps + 1))
    (hmaxPQ : maxDivLE P' Q' eps) (hmaxQP : maxDivLE Q' P' eps) :
    approxMaxDivLE P Q eps delta ∧ approxMaxDivLE Q P eps delta :=
  ⟨approx_of_repair_pair P Q eps delta P' Q' htvP htvQ hmaxPQ,
    approx_of_repair_pair Q P eps delta Q' P' htvQ htvP hmaxQP⟩

private theorem exists_repair_both_of_approx_both {Outcome : Type*}
    [Fintype Outcome] [Nonempty Outcome] (P Q : PMF Outcome) (eps delta : ℝ)
    (heps : 0 ≤ eps) (_hdelta : 0 ≤ delta)
    (hPQ : approxMaxDivLE P Q eps delta)
    (hQP : approxMaxDivLE Q P eps delta) :
    ∃ P' Q' : PMF Outcome, tvDist P P' ≤ delta / (Real.exp eps + 1) ∧
      tvDist Q Q' ≤ delta / (Real.exp eps + 1) ∧
      maxDivLE P' Q' eps ∧ maxDivLE Q' P' eps := by
  classical
  have ha1 : (1:ℝ) ≤ Real.exp eps := Real.one_le_exp heps
  have hapos : (0:ℝ) < Real.exp eps := Real.exp_pos eps
  have ha0 : (0:ℝ) ≤ Real.exp eps := le_of_lt hapos
  have hc := exp_add_one_pos eps
  have hc0 : Real.exp eps + 1 ≠ 0 := ne_of_gt hc
  have hAle : excessMass P Q eps ≤ delta :=
    excessMass_le_delta P Q eps delta hPQ
  have hBle : excessMass Q P eps ≤ delta :=
    excessMass_le_delta Q P eps delta hQP
  have hL1 : ∑ w, repair2L P Q eps w ≤ 1 := by
    rw [sum_repair2L P Q eps, div_le_one hc]
    linarith [ha1]
  have hU1 : 1 ≤ ∑ w, repair2U P Q eps w := by
    rw [sum_repair2U P Q eps]
    have e : Real.exp eps * (2 / (Real.exp eps + 1)) =
        2 * Real.exp eps / (Real.exp eps + 1) := by ring
    rw [e, le_div_iff₀ hc]
    linarith [ha1]
  obtain ⟨r', hlo, hhi, hsum1, hmove⟩ := exists_interp_sum_one
    (repair2L P Q eps) (repair2U P Q eps) (repair2R P Q eps)
    (fun w => repair2R_ge_L P Q eps heps w)
    (fun w => repair2R_le_U P Q eps w)
    hL1 hU1
  have hsL : ∀ w : Outcome, ((P w).toReal + (Q w).toReal) -
      repair2L P Q eps w = repair2U P Q eps w := by
    intro w
    simp only [repair2U, repair2L]
    field_simp
    ring
  have hsU : ∀ w : Outcome, ((P w).toReal + (Q w).toReal) -
      repair2U P Q eps w = repair2L P Q eps w := by
    intro w
    simp only [repair2U, repair2L]
    field_simp
    ring
  have hqlo : ∀ w : Outcome, repair2L P Q eps w ≤
      ((P w).toReal + (Q w).toReal) - r' w := by
    intro w
    have h2 := hsL w
    linarith [hhi w, h2]
  have hqhi : ∀ w : Outcome,
      ((P w).toReal + (Q w).toReal) - r' w ≤ repair2U P Q eps w := by
    intro w
    have h2 := hsU w
    linarith [hlo w, h2]
  have hnnP : ∀ w : Outcome, 0 ≤ r' w := fun w =>
    le_trans (repair2L_nonneg P Q eps w) (hlo w)
  have hnnQ : ∀ w : Outcome,
      0 ≤ (P w).toReal + (Q w).toReal - r' w := fun w =>
    le_trans (repair2L_nonneg P Q eps w) (hqlo w)
  have hsumQ : (∑ w, ((P w).toReal + (Q w).toReal - r' w)) = 1 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      pmf_toReal_sum_univ P, pmf_toReal_sum_univ Q, hsum1]
    norm_num
  set P' : PMF Outcome := PMF.ofFintype (fun w => ENNReal.ofReal (r' w)) (by
    have hnn : ∀ i, i ∈ Finset.univ → 0 ≤ r' i := fun i _ => hnnP i
    have hof := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := r') hnn
    rw [hsum1, ENNReal.ofReal_one] at hof
    exact hof.symm) with hP'def
  set Q' : PMF Outcome := PMF.ofFintype
    (fun w => ENNReal.ofReal ((P w).toReal + (Q w).toReal - r' w)) (by
    have hnn : ∀ i, i ∈ Finset.univ →
        0 ≤ (P i).toReal + (Q i).toReal - r' i := fun i _ => hnnQ i
    have hof := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun w => (P w).toReal + (Q w).toReal - r' w) hnn
    rw [hsumQ, ENNReal.ofReal_one] at hof
    exact hof.symm) with hQ'def
  have hP'toReal : ∀ w : Outcome, (P' w).toReal = r' w := by
    intro w
    simp only [hP'def, PMF.ofFintype_apply]
    exact ENNReal.toReal_ofReal (hnnP w)
  have hQ'toReal : ∀ w : Outcome, (Q' w).toReal =
      (P w).toReal + (Q w).toReal - r' w := by
    intro w
    simp only [hQ'def, PMF.ofFintype_apply]
    exact ENNReal.toReal_ofReal (hnnQ w)
  have hmaxPQ : maxDivLE P' Q' eps := by
    intro w
    rw [hP'toReal w, hQ'toReal w]
    calc r' w ≤ repair2U P Q eps w := hhi w
      _ = Real.exp eps * repair2L P Q eps w := rfl
      _ ≤ Real.exp eps * ((P w).toReal + (Q w).toReal - r' w) :=
          mul_le_mul_of_nonneg_left (hqlo w) ha0
  have hmaxQP : maxDivLE Q' P' eps := by
    intro w
    rw [hP'toReal w, hQ'toReal w]
    calc (P w).toReal + (Q w).toReal - r' w ≤ repair2U P Q eps w := hqhi w
      _ = Real.exp eps * repair2L P Q eps w := rfl
      _ ≤ Real.exp eps * r' w := mul_le_mul_of_nonneg_left (hlo w) ha0
  have hsig : (∑ w, repair2R P Q eps w) - 1 =
      (excessMass Q P eps - excessMass P Q eps) / (Real.exp eps + 1) :=
    sum_repair2R_sub P Q eps heps
  have habs : ∑ w, |(P w).toReal - repair2R P Q eps w| =
      (excessMass P Q eps + excessMass Q P eps) / (Real.exp eps + 1) :=
    sum_abs_sub_repair2R P Q eps heps
  have h1sig : |1 - ∑ w, repair2R P Q eps w| =
      |excessMass P Q eps - excessMass Q P eps| / (Real.exp eps + 1) := by
    have h1 : (1:ℝ) - ∑ w, repair2R P Q eps w =
        (excessMass P Q eps - excessMass Q P eps) / (Real.exp eps + 1) := by
      have hneg : (excessMass P Q eps - excessMass Q P eps) /
          (Real.exp eps + 1) =
          -(((excessMass Q P eps - excessMass P Q eps)) /
            (Real.exp eps + 1)) := by
        ring
      rw [hneg]
      linarith [hsig]
    rw [h1, abs_div, abs_of_pos hc]
  have htri : ∑ w, |(P w).toReal - r' w| ≤
      (∑ w, |(P w).toReal - repair2R P Q eps w|) +
        ∑ w, |repair2R P Q eps w - r' w| := by
    have hpt : ∀ w ∈ (Finset.univ : Finset Outcome),
        |(P w).toReal - r' w| ≤ |(P w).toReal - repair2R P Q eps w| +
          |repair2R P Q eps w - r' w| :=
      fun w _ => abs_sub_le _ _ _
    have hle := Finset.sum_le_sum hpt
    rwa [Finset.sum_add_distrib] at hle
  have hM : (excessMass P Q eps + excessMass Q P eps +
      |excessMass P Q eps - excessMass Q P eps|) =
      2 * max (excessMass P Q eps) (excessMass Q P eps) :=
    add_add_abs_eq_two_max _ _
  have hMle : max (excessMass P Q eps) (excessMass Q P eps) ≤ delta :=
    max_le hAle hBle
  have hTV : (1/2) * ∑ w, |(P w).toReal - r' w| ≤
      delta / (Real.exp eps + 1) := by
    have hS : ∑ w, |(P w).toReal - r' w| ≤
        (excessMass P Q eps + excessMass Q P eps) / (Real.exp eps + 1) +
          |excessMass P Q eps - excessMass Q P eps| /
            (Real.exp eps + 1) := by
      calc ∑ w, |(P w).toReal - r' w|
          ≤ (∑ w, |(P w).toReal - repair2R P Q eps w|) +
              ∑ w, |repair2R P Q eps w - r' w| := htri
        _ = (excessMass P Q eps + excessMass Q P eps) / (Real.exp eps + 1) +
            |excessMass P Q eps - excessMass Q P eps| /
              (Real.exp eps + 1) := by
            rw [habs, hmove, h1sig]
    have hE : (excessMass P Q eps + excessMass Q P eps) / (Real.exp eps + 1) +
        |excessMass P Q eps - excessMass Q P eps| / (Real.exp eps + 1) =
        2 * max (excessMass P Q eps) (excessMass Q P eps) /
          (Real.exp eps + 1) := by
      have hXX : (excessMass P Q eps + excessMass Q P eps) +
          |excessMass P Q eps - excessMass Q P eps| =
          2 * max (excessMass P Q eps) (excessMass Q P eps) := by
        linarith [hM]
      rw [← add_div, hXX]
    calc (1/2) * ∑ w, |(P w).toReal - r' w|
        ≤ (1/2) * ((excessMass P Q eps + excessMass Q P eps) /
              (Real.exp eps + 1) +
            |excessMass P Q eps - excessMass Q P eps| /
              (Real.exp eps + 1)) :=
          mul_le_mul_of_nonneg_left hS (by norm_num)
      _ = max (excessMass P Q eps) (excessMass Q P eps) /
          (Real.exp eps + 1) := by
          rw [hE, ← mul_div_assoc]
          congr 1
          ring
      _ ≤ delta / (Real.exp eps + 1) :=
          div_le_div_of_nonneg_right hMle (le_of_lt hc)
  have htvP : tvDist P P' ≤ delta / (Real.exp eps + 1) := by
    rw [tvDist_unfold]
    simp only [hP'toReal]
    exact hTV
  have htvQ : tvDist Q Q' ≤ delta / (Real.exp eps + 1) := by
    rw [tvDist_unfold]
    have hQQ : ∑ w, |(Q w).toReal - (Q' w).toReal| =
        ∑ w, |(P w).toReal - r' w| := by
      apply Finset.sum_congr rfl
      intro w _
      rw [hQ'toReal w]
      have heq : (Q w).toReal - ((P w).toReal + (Q w).toReal - r' w) =
          -((P w).toReal - r' w) := by ring
      rw [heq, abs_neg]
    rw [hQQ]
    exact hTV
  exact ⟨P', Q', htvP, htvQ, hmaxPQ, hmaxQP⟩

/-- Simultaneous repair iff: both approximate bounds hold exactly when two
witnesses within `δ / (exp ε + 1)` satisfy the pure bound in both
directions. The two-sided pure bound (rather than the book's
one-directional conclusion) is required for the reverse direction. -/
theorem approxMaxDivLE_both_iff_exists_repair {Outcome : Type*}
    [Fintype Outcome] [Nonempty Outcome] (P Q : PMF Outcome) (eps delta : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    (approxMaxDivLE P Q eps delta ∧ approxMaxDivLE Q P eps delta) ↔
      ∃ P' Q' : PMF Outcome, tvDist P P' ≤ delta / (Real.exp eps + 1) ∧
        tvDist Q Q' ≤ delta / (Real.exp eps + 1) ∧
        maxDivLE P' Q' eps ∧ maxDivLE Q' P' eps := by
  constructor
  · rintro ⟨hPQ, hQP⟩
    exact exists_repair_both_of_approx_both P Q eps delta heps hdelta hPQ hQP
  · rintro ⟨P', Q', htvP, htvQ, hmaxPQ, hmaxQP⟩
    exact approx_both_of_exists_repair_both P Q eps delta P' Q' htvP htvQ
      hmaxPQ hmaxQP

private theorem convex_le_of_le (θ x y : ℝ) (_h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (h : y ≤ x) : θ * x + (1 - θ) * y ≤ x := by
  have hnn : 0 ≤ 1 - θ := sub_nonneg.mpr h1
  calc θ * x + (1 - θ) * y ≤ θ * x + (1 - θ) * x :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left h hnn)
    _ = x := by ring

private theorem le_convex_of_le (θ x y : ℝ) (h0 : 0 ≤ θ) (_h1 : θ ≤ 1)
    (h : y ≤ x) : y ≤ θ * x + (1 - θ) * y := by
  calc y = θ * y + (1 - θ) * y := by ring
    _ ≤ θ * x + (1 - θ) * y :=
          add_le_add (mul_le_mul_of_nonneg_left h h0) le_rfl

private theorem shrink_sum_eq (u v a θ : ℝ)
    (hθ : θ * (u - v / a) = v - v / a) :
    θ * u + (1 - θ) * (v / a) = v := by
  have hring : θ * u + (1 - θ) * (v / a) = θ * (u - v / a) + v / a := by ring
  rw [hring, hθ]
  ring

private theorem min_div_le_min_of_one_le (p q a : ℝ) (ha1 : 1 ≤ a)
    (hapos : 0 < a) (_hp : 0 ≤ p) (hq : 0 ≤ q) :
    min q (a * p) / a ≤ min p (a * q) := by
  apply le_min
  · rw [div_le_iff₀ hapos]
    calc min q (a * p) ≤ a * p := min_le_right _ _
      _ = p * a := by ring
  · calc min q (a * p) / a ≤ q / a :=
          div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hapos)
      _ ≤ a * q := by
          rw [div_le_iff₀ hapos]
          have h1 : q ≤ a * q := le_mul_of_one_le_left hq ha1
          have h2 : a * q ≤ a * q * a :=
            le_mul_of_one_le_right (mul_nonneg (le_of_lt hapos) hq) ha1
          linarith

private theorem min_le_mul_min_of_one_le (p q a : ℝ) (ha1 : 1 ≤ a)
    (hapos : 0 < a) (hp : 0 ≤ p) (_hq : 0 ≤ q) :
    min p (a * q) ≤ a * min q (a * p) := by
  classical
  by_cases h : q ≤ a * p
  · rw [min_eq_left h]
    exact min_le_right _ _
  · have hlt : a * p < q := lt_of_not_ge h
    rw [min_eq_right (le_of_lt hlt)]
    have haa : (1:ℝ) ≤ a * a :=
      calc (1:ℝ) = 1 * 1 := (mul_one 1).symm
        _ ≤ a * a := mul_le_mul ha1 ha1 zero_le_one (le_of_lt hapos)
    have hple : p ≤ a * (a * p) := by
      calc p = 1 * p := (one_mul _).symm
        _ ≤ (a * a) * p := mul_le_mul_of_nonneg_right haa hp
        _ = a * (a * p) := by ring
    exact (min_le_left _ _).trans hple

private theorem exists_dominated_of_common {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q : PMF Outcome) (eps delta : ℝ)
    (f g : Outcome → ℝ) (t : ℝ)
    (hf_nonneg : ∀ w, 0 ≤ f w) (hg_nonneg : ∀ w, 0 ≤ g w)
    (hf_sum : ∑ w, f w = t) (hg_sum : ∑ w, g w = t)
    (ht_le : 1 - delta ≤ t) (ht_pos : 0 < t)
    (hfg : ∀ w, f w ≤ Real.exp eps * g w)
    (hgf : ∀ w, g w ≤ Real.exp eps * f w)
    (hf_le : ∀ w, f w ≤ (P w).toReal)
    (hg_le : ∀ w, g w ≤ (Q w).toReal) :
    ∃ P₀ Q₀ : PMF Outcome,
      maxDivLE P₀ Q₀ eps ∧ maxDivLE Q₀ P₀ eps ∧
      (∀ w, (1 - delta) * (P₀ w).toReal ≤ (P w).toReal) ∧
      (∀ w, (1 - delta) * (Q₀ w).toReal ≤ (Q w).toReal) := by
  have ht0 : t ≠ 0 := ne_of_gt ht_pos
  have hsumP : ∑ w, f w / t = 1 := by
    rw [← Finset.sum_div, hf_sum, div_self ht0]
  have hsumQ : ∑ w, g w / t = 1 := by
    rw [← Finset.sum_div, hg_sum, div_self ht0]
  have hnnP : ∀ i ∈ Finset.univ, 0 ≤ f i / t :=
    fun i _ => div_nonneg (hf_nonneg i) (le_of_lt ht_pos)
  have hnnQ : ∀ i ∈ Finset.univ, 0 ≤ g i / t :=
    fun i _ => div_nonneg (hg_nonneg i) (le_of_lt ht_pos)
  have hofP := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (f := fun w => f w / t) hnnP
  have hofQ := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (f := fun w => g w / t) hnnQ
  rw [hsumP, ENNReal.ofReal_one] at hofP
  rw [hsumQ, ENNReal.ofReal_one] at hofQ
  set P₀ : PMF Outcome :=
    PMF.ofFintype (fun w => ENNReal.ofReal (f w / t)) hofP.symm with hP₀def
  set Q₀ : PMF Outcome :=
    PMF.ofFintype (fun w => ENNReal.ofReal (g w / t)) hofQ.symm with hQ₀def
  have hP₀toReal : ∀ w : Outcome, (P₀ w).toReal = f w / t := by
    intro w
    simp only [hP₀def, PMF.ofFintype_apply]
    exact ENNReal.toReal_ofReal (div_nonneg (hf_nonneg w) (le_of_lt ht_pos))
  have hQ₀toReal : ∀ w : Outcome, (Q₀ w).toReal = g w / t := by
    intro w
    simp only [hQ₀def, PMF.ofFintype_apply]
    exact ENNReal.toReal_ofReal (div_nonneg (hg_nonneg w) (le_of_lt ht_pos))
  refine ⟨P₀, Q₀, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [hP₀toReal w, hQ₀toReal w]
    calc f w / t ≤ (Real.exp eps * g w) / t :=
            div_le_div_of_nonneg_right (hfg w) (le_of_lt ht_pos)
      _ = Real.exp eps * (g w / t) := mul_div_assoc _ _ _
  · intro w
    rw [hP₀toReal w, hQ₀toReal w]
    calc g w / t ≤ (Real.exp eps * f w) / t :=
            div_le_div_of_nonneg_right (hgf w) (le_of_lt ht_pos)
      _ = Real.exp eps * (f w / t) := mul_div_assoc _ _ _
  · intro w
    rw [hP₀toReal w]
    calc (1 - delta) * (f w / t) ≤ t * (f w / t) :=
            mul_le_mul_of_nonneg_right ht_le
              (div_nonneg (hf_nonneg w) (le_of_lt ht_pos))
      _ = f w := by rw [mul_comm, div_mul_cancel₀ _ ht0]
      _ ≤ (P w).toReal := hf_le w
  · intro w
    rw [hQ₀toReal w]
    calc (1 - delta) * (g w / t) ≤ t * (g w / t) :=
            mul_le_mul_of_nonneg_right ht_le
              (div_nonneg (hg_nonneg w) (le_of_lt ht_pos))
      _ = g w := by rw [mul_comm, div_mul_cancel₀ _ ht0]
      _ ≤ (Q w).toReal := hg_le w

theorem exists_dominated_pure_pair_of_approxMaxDivLE_both
{Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
(P Q : PMF Outcome) (eps delta : ℝ)
(heps : 0 ≤ eps) (hdelta : 0 ≤ delta) (hdelta_lt : delta < 1)
(hPQ : approxMaxDivLE P Q eps delta)
(hQP : approxMaxDivLE Q P eps delta) :
∃ P₀ Q₀ : PMF Outcome,
maxDivLE P₀ Q₀ eps ∧ maxDivLE Q₀ P₀ eps ∧
(∀ w, (1 - delta) * (P₀ w).toReal ≤ (P w).toReal) ∧
(∀ w, (1 - delta) * (Q₀ w).toReal ≤ (Q w).toReal) := by
  classical
  have ha1 : (1:ℝ) ≤ Real.exp eps := Real.one_le_exp heps
  have hapos : (0:ℝ) < Real.exp eps := Real.exp_pos eps
  have ha0 : (0:ℝ) ≤ Real.exp eps := le_of_lt hapos
  have hane : Real.exp eps ≠ 0 := ne_of_gt hapos
  have _hdelta_nonneg : 0 ≤ delta := hdelta
  have hp_nonneg : ∀ w : Outcome, 0 ≤ (P w).toReal :=
    fun w => ENNReal.toReal_nonneg
  have hq_nonneg : ∀ w : Outcome, 0 ≤ (Q w).toReal :=
    fun w => ENNReal.toReal_nonneg
  have hra_le_l : ∀ w : Outcome,
      capEnvelope Q P eps w / Real.exp eps ≤ capEnvelope P Q eps w := by
    intro w
    show min ((Q w).toReal) (Real.exp eps * (P w).toReal) / Real.exp eps ≤
      min ((P w).toReal) (Real.exp eps * (Q w).toReal)
    exact min_div_le_min_of_one_le _ _ _ ha1 hapos (hp_nonneg w) (hq_nonneg w)
  have hl_le_ar : ∀ w : Outcome,
      capEnvelope P Q eps w ≤ Real.exp eps * capEnvelope Q P eps w := by
    intro w
    show min ((P w).toReal) (Real.exp eps * (Q w).toReal) ≤
      Real.exp eps * min ((Q w).toReal) (Real.exp eps * (P w).toReal)
    exact min_le_mul_min_of_one_le _ _ _ ha1 hapos (hp_nonneg w) (hq_nonneg w)
  have hla_le_r : ∀ w : Outcome,
      capEnvelope P Q eps w / Real.exp eps ≤ capEnvelope Q P eps w := by
    intro w
    show min ((P w).toReal) (Real.exp eps * (Q w).toReal) / Real.exp eps ≤
      min ((Q w).toReal) (Real.exp eps * (P w).toReal)
    exact min_div_le_min_of_one_le _ _ _ ha1 hapos (hq_nonneg w) (hp_nonneg w)
  have hr_le_al : ∀ w : Outcome,
      capEnvelope Q P eps w ≤ Real.exp eps * capEnvelope P Q eps w := by
    intro w
    show min ((Q w).toReal) (Real.exp eps * (P w).toReal) ≤
      Real.exp eps * min ((P w).toReal) (Real.exp eps * (Q w).toReal)
    exact min_le_mul_min_of_one_le _ _ _ ha1 hapos (hq_nonneg w) (hp_nonneg w)
  have hsumL := sum_capEnvelope P Q eps
  have hsumR := sum_capEnvelope Q P eps
  have hexPQ := excessMass_le_delta P Q eps delta hPQ
  have hexQP := excessMass_le_delta Q P eps delta hQP
  have hu : 1 - delta ≤ ∑ w, capEnvelope P Q eps w := by linarith
  have hv : 1 - delta ≤ ∑ w, capEnvelope Q P eps w := by linarith
  have hm_pos : (0:ℝ) < 1 - delta := sub_pos.mpr hdelta_lt
  have hu_pos : (0:ℝ) < ∑ w, capEnvelope P Q eps w :=
    lt_of_lt_of_le hm_pos hu
  have hv_pos : (0:ℝ) < ∑ w, capEnvelope Q P eps w :=
    lt_of_lt_of_le hm_pos hv
  have hl_nonneg : ∀ w : Outcome, 0 ≤ capEnvelope P Q eps w :=
    fun w => capEnvelope_nonneg P Q eps w
  have hr_nonneg : ∀ w : Outcome, 0 ≤ capEnvelope Q P eps w :=
    fun w => capEnvelope_nonneg Q P eps w
  rcases lt_trichotomy (∑ w, capEnvelope P Q eps w)
      (∑ w, capEnvelope Q P eps w) with hlt | heq | hgt
  · have hva : (∑ w, capEnvelope P Q eps w) / Real.exp eps ≤
        ∑ w, capEnvelope P Q eps w := by
      rw [div_le_iff₀ hapos]
      exact le_mul_of_one_le_right (le_of_lt hu_pos) ha1
    have hD_pos : (0:ℝ) < (∑ w, capEnvelope Q P eps w) -
        (∑ w, capEnvelope P Q eps w) / Real.exp eps :=
      sub_pos.mpr (lt_of_le_of_lt hva hlt)
    have hD0 : (∑ w, capEnvelope Q P eps w) -
        (∑ w, capEnvelope P Q eps w) / Real.exp eps ≠ 0 := ne_of_gt hD_pos
    set θ : ℝ := ((∑ w, capEnvelope P Q eps w) -
        (∑ w, capEnvelope P Q eps w) / Real.exp eps) /
        ((∑ w, capEnvelope Q P eps w) -
          (∑ w, capEnvelope P Q eps w) / Real.exp eps) with hθdef
    have hN_nonneg : (0:ℝ) ≤ (∑ w, capEnvelope P Q eps w) -
        (∑ w, capEnvelope P Q eps w) / Real.exp eps :=
      sub_nonneg.mpr hva
    have hθ0 : 0 ≤ θ := by
      rw [hθdef]
      exact div_nonneg hN_nonneg (le_of_lt hD_pos)
    have hθ1 : θ ≤ 1 := by
      rw [hθdef, div_le_one hD_pos]
      exact sub_le_sub_right (le_of_lt hlt) _
    have hθD : θ * ((∑ w, capEnvelope Q P eps w) -
        (∑ w, capEnvelope P Q eps w) / Real.exp eps) =
        (∑ w, capEnvelope P Q eps w) -
          (∑ w, capEnvelope P Q eps w) / Real.exp eps := by
      rw [hθdef]
      exact div_mul_cancel₀ _ hD0
    have hsplit : (∑ w, (θ * capEnvelope Q P eps w + (1 - θ) *
        (capEnvelope P Q eps w / Real.exp eps))) =
        θ * (∑ w, capEnvelope Q P eps w) + (1 - θ) *
          ((∑ w, capEnvelope P Q eps w) / Real.exp eps) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.sum_div]
    have hsum_g1 : (∑ w, (θ * capEnvelope Q P eps w + (1 - θ) *
        (capEnvelope P Q eps w / Real.exp eps))) =
        ∑ w, capEnvelope P Q eps w := by
      rw [hsplit]
      exact shrink_sum_eq _ _ _ _ hθD
    have hg1_nonneg : ∀ w : Outcome, 0 ≤ θ * capEnvelope Q P eps w +
        (1 - θ) * (capEnvelope P Q eps w / Real.exp eps) := by
      intro w
      apply add_nonneg
      · exact mul_nonneg hθ0 (hr_nonneg w)
      · apply mul_nonneg (sub_nonneg.mpr hθ1)
        exact div_nonneg (hl_nonneg w) ha0
    have hg1_ge : ∀ w : Outcome, capEnvelope P Q eps w / Real.exp eps ≤
        θ * capEnvelope Q P eps w +
          (1 - θ) * (capEnvelope P Q eps w / Real.exp eps) := by
      intro w
      exact le_convex_of_le θ _ _ hθ0 hθ1 (hla_le_r w)
    have hg1_le : ∀ w : Outcome, θ * capEnvelope Q P eps w +
        (1 - θ) * (capEnvelope P Q eps w / Real.exp eps) ≤
        capEnvelope Q P eps w := by
      intro w
      exact convex_le_of_le θ _ _ hθ0 hθ1 (hla_le_r w)
    have hfg : ∀ w : Outcome, capEnvelope P Q eps w ≤ Real.exp eps *
        (θ * capEnvelope Q P eps w + (1 - θ) *
          (capEnvelope P Q eps w / Real.exp eps)) := by
      intro w
      have hcancel : Real.exp eps * (capEnvelope P Q eps w / Real.exp eps) =
          capEnvelope P Q eps w := by
        rw [mul_comm, div_mul_cancel₀ _ hane]
      calc capEnvelope P Q eps w
          = Real.exp eps * (capEnvelope P Q eps w / Real.exp eps) :=
            hcancel.symm
        _ ≤ Real.exp eps * (θ * capEnvelope Q P eps w + (1 - θ) *
            (capEnvelope P Q eps w / Real.exp eps)) :=
            mul_le_mul_of_nonneg_left (hg1_ge w) ha0
    have hgf : ∀ w : Outcome, (θ * capEnvelope Q P eps w + (1 - θ) *
        (capEnvelope P Q eps w / Real.exp eps)) ≤
        Real.exp eps * capEnvelope P Q eps w := by
      intro w
      exact (hg1_le w).trans (hr_le_al w)
    have hf_le : ∀ w : Outcome, capEnvelope P Q eps w ≤ (P w).toReal :=
      fun w => capEnvelope_le_left P Q eps w
    have hg_le : ∀ w : Outcome, (θ * capEnvelope Q P eps w + (1 - θ) *
        (capEnvelope P Q eps w / Real.exp eps)) ≤ (Q w).toReal := by
      intro w
      exact (hg1_le w).trans (capEnvelope_le_left Q P eps w)
    exact exists_dominated_of_common P Q eps delta _ _ _
      hl_nonneg hg1_nonneg rfl hsum_g1 hu hu_pos hfg hgf hf_le hg_le
  · have hfg : ∀ w : Outcome, capEnvelope P Q eps w ≤
        Real.exp eps * capEnvelope Q P eps w := hl_le_ar
    have hgf : ∀ w : Outcome, capEnvelope Q P eps w ≤
        Real.exp eps * capEnvelope P Q eps w := hr_le_al
    have hf_le : ∀ w : Outcome, capEnvelope P Q eps w ≤ (P w).toReal :=
      fun w => capEnvelope_le_left P Q eps w
    have hg_le : ∀ w : Outcome, capEnvelope Q P eps w ≤ (Q w).toReal :=
      fun w => capEnvelope_le_left Q P eps w
    exact exists_dominated_of_common P Q eps delta _ _ _
      hl_nonneg hr_nonneg rfl heq.symm hu hu_pos hfg hgf hf_le hg_le
  · have hva : (∑ w, capEnvelope Q P eps w) / Real.exp eps ≤
        ∑ w, capEnvelope Q P eps w := by
      rw [div_le_iff₀ hapos]
      exact le_mul_of_one_le_right (le_of_lt hv_pos) ha1
    have hD_pos : (0:ℝ) < (∑ w, capEnvelope P Q eps w) -
        (∑ w, capEnvelope Q P eps w) / Real.exp eps :=
      sub_pos.mpr (lt_of_le_of_lt hva hgt)
    have hD0 : (∑ w, capEnvelope P Q eps w) -
        (∑ w, capEnvelope Q P eps w) / Real.exp eps ≠ 0 := ne_of_gt hD_pos
    set θ : ℝ := ((∑ w, capEnvelope Q P eps w) -
        (∑ w, capEnvelope Q P eps w) / Real.exp eps) /
        ((∑ w, capEnvelope P Q eps w) -
          (∑ w, capEnvelope Q P eps w) / Real.exp eps) with hθdef
    have hN_nonneg : (0:ℝ) ≤ (∑ w, capEnvelope Q P eps w) -
        (∑ w, capEnvelope Q P eps w) / Real.exp eps :=
      sub_nonneg.mpr hva
    have hθ0 : 0 ≤ θ := by
      rw [hθdef]
      exact div_nonneg hN_nonneg (le_of_lt hD_pos)
    have hθ1 : θ ≤ 1 := by
      rw [hθdef, div_le_one hD_pos]
      exact sub_le_sub_right (le_of_lt hgt) _
    have hθD : θ * ((∑ w, capEnvelope P Q eps w) -
        (∑ w, capEnvelope Q P eps w) / Real.exp eps) =
        (∑ w, capEnvelope Q P eps w) -
          (∑ w, capEnvelope Q P eps w) / Real.exp eps := by
      rw [hθdef]
      exact div_mul_cancel₀ _ hD0
    have hsplit : (∑ w, (θ * capEnvelope P Q eps w + (1 - θ) *
        (capEnvelope Q P eps w / Real.exp eps))) =
        θ * (∑ w, capEnvelope P Q eps w) + (1 - θ) *
          ((∑ w, capEnvelope Q P eps w) / Real.exp eps) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.sum_div]
    have hsum_f1 : (∑ w, (θ * capEnvelope P Q eps w + (1 - θ) *
        (capEnvelope Q P eps w / Real.exp eps))) =
        ∑ w, capEnvelope Q P eps w := by
      rw [hsplit]
      exact shrink_sum_eq _ _ _ _ hθD
    have hf1_nonneg : ∀ w : Outcome, 0 ≤ θ * capEnvelope P Q eps w +
        (1 - θ) * (capEnvelope Q P eps w / Real.exp eps) := by
      intro w
      apply add_nonneg
      · exact mul_nonneg hθ0 (hl_nonneg w)
      · apply mul_nonneg (sub_nonneg.mpr hθ1)
        exact div_nonneg (hr_nonneg w) ha0
    have hf1_ge : ∀ w : Outcome, capEnvelope Q P eps w / Real.exp eps ≤
        θ * capEnvelope P Q eps w +
          (1 - θ) * (capEnvelope Q P eps w / Real.exp eps) := by
      intro w
      exact le_convex_of_le θ _ _ hθ0 hθ1 (hra_le_l w)
    have hf1_le : ∀ w : Outcome, θ * capEnvelope P Q eps w +
        (1 - θ) * (capEnvelope Q P eps w / Real.exp eps) ≤
        capEnvelope P Q eps w := by
      intro w
      exact convex_le_of_le θ _ _ hθ0 hθ1 (hra_le_l w)
    have hfg : ∀ w : Outcome, (θ * capEnvelope P Q eps w + (1 - θ) *
        (capEnvelope Q P eps w / Real.exp eps)) ≤
        Real.exp eps * capEnvelope Q P eps w := by
      intro w
      exact (hf1_le w).trans (hl_le_ar w)
    have hgf : ∀ w : Outcome, capEnvelope Q P eps w ≤ Real.exp eps *
        (θ * capEnvelope P Q eps w + (1 - θ) *
          (capEnvelope Q P eps w / Real.exp eps)) := by
      intro w
      have hcancel : Real.exp eps * (capEnvelope Q P eps w / Real.exp eps) =
          capEnvelope Q P eps w := by
        rw [mul_comm, div_mul_cancel₀ _ hane]
      calc capEnvelope Q P eps w
          = Real.exp eps * (capEnvelope Q P eps w / Real.exp eps) :=
            hcancel.symm
        _ ≤ Real.exp eps * (θ * capEnvelope P Q eps w + (1 - θ) *
            (capEnvelope Q P eps w / Real.exp eps)) :=
            mul_le_mul_of_nonneg_left (hf1_ge w) ha0
    have hf_le : ∀ w : Outcome, (θ * capEnvelope P Q eps w + (1 - θ) *
        (capEnvelope Q P eps w / Real.exp eps)) ≤ (P w).toReal := by
      intro w
      exact (hf1_le w).trans (capEnvelope_le_left P Q eps w)
    have hg_le : ∀ w : Outcome, capEnvelope Q P eps w ≤ (Q w).toReal :=
      fun w => capEnvelope_le_left Q P eps w
    exact exists_dominated_of_common P Q eps delta _ _ _
      hf1_nonneg hr_nonneg hsum_f1 rfl hv hv_pos hfg hgf hf_le hg_le

/-- Common-mass transfer: an `alpha`-fraction of ideal mass satisfying the
approximate bound transfers it to the outer distributions, charging the
residual mass `1 - alpha`. No `alpha ≤ 1` hypothesis is needed. -/
theorem approxMaxDivLE_of_common_mass {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P Q P₀ Q₀ : PMF Outcome) (alpha E beta : ℝ)
    (halpha : 0 ≤ alpha)
    (hP : ∀ w, alpha * (P₀ w).toReal ≤ (P w).toReal)
    (hQ : ∀ w, alpha * (Q₀ w).toReal ≤ (Q w).toReal)
    (hideal : approxMaxDivLE P₀ Q₀ E beta) :
    approxMaxDivLE P Q E (alpha * beta + 1 - alpha) := by
  classical
  intro s
  have hres_le : (∑ w ∈ s, ((P w).toReal - alpha * (P₀ w).toReal)) ≤ 1 - alpha := by
    have hsub : (∑ w ∈ s, ((P w).toReal - alpha * (P₀ w).toReal)) ≤
        ∑ w, ((P w).toReal - alpha * (P₀ w).toReal) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (by
        intro w _ _
        have h := hP w
        linarith)
    have htot : (∑ w, ((P w).toReal - alpha * (P₀ w).toReal)) = 1 - alpha := by
      rw [Finset.sum_sub_distrib, pmf_toReal_sum_univ P, ← Finset.mul_sum,
        pmf_toReal_sum_univ P₀, mul_one]
    linarith
  have hPsplit : (∑ w ∈ s, (P w).toReal) =
      alpha * (∑ w ∈ s, (P₀ w).toReal) +
        ∑ w ∈ s, ((P w).toReal - alpha * (P₀ w).toReal) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    ring
  have hideal_s := hideal s
  have hscaled : alpha * (∑ w ∈ s, (P₀ w).toReal) ≤
      alpha * (Real.exp E * ∑ w ∈ s, (Q₀ w).toReal + beta) :=
    mul_le_mul_of_nonneg_left hideal_s halpha
  have hQs : alpha * (∑ w ∈ s, (Q₀ w).toReal) ≤ ∑ w ∈ s, (Q w).toReal := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun w _ => hQ w)
  have hexp : 0 ≤ Real.exp E := (Real.exp_pos E).le
  rw [hPsplit]
  have h2 : Real.exp E * (alpha * ∑ w ∈ s, (Q₀ w).toReal) ≤
      Real.exp E * ∑ w ∈ s, (Q w).toReal :=
    mul_le_mul_of_nonneg_left hQs hexp
  linarith

end CSLibExt.Privacy.MaxDivergenceDecomposition
