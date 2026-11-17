/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.KarushKuhnTucker
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Filter.Extr

/-!
# Water-filling certificate

The parallel Gaussian channel rate `∑ log (1 + λᵢ pᵢ) / (2 log 2)`
over nonnegative powers with total budget `P` is maximized by
water-filling: modes with positive gain receive
`max (ν - 1/λᵢ, 0)` for a water level `ν` chosen so the powers
sum to `P`, and zero-gain modes receive nothing. The KKT
certificate is stated explicitly; zero power and all-zero-gain
cases are handled separately.

-/

@[expose] public section

open Finset
namespace MathlibExt.Analysis.Convex.WaterFillingCertificate

/-! ### Definitions -/

/-- Sum rate in bits of parallel Gaussian modes with gains `lam i` and powers `p i`:
`∑ i, log (1 + lam i * p i) / (2 * log 2)` (natural log, explicit bits conversion). -/
noncomputable def sumRateBits {ι : Type*} [Fintype ι] (lam p : ι → ℝ) : ℝ :=
  ∑ i, Real.log (1 + lam i * p i) / (2 * Real.log 2)

/-- Admissible power allocations: `p i ≥ 0` for every mode and `∑ i, p i ≤ P`. -/
def powerFeasible {ι : Type*} [Fintype ι] (P : ℝ) : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i ≤ P}

/-- Water-level power sum `∑_{lam i > 0} max (ν - 1 / lam i) 0`; the inverse `1 / lam i` is only
formed on modes with `0 < lam i`. -/
noncomputable def waterLevelSum {ι : Type*} [Fintype ι] (lam : ι → ℝ) (ν : ℝ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => 0 < lam i), max (ν - 1 / lam i) 0

/-- Water-filling allocation at level `ν`: `max (ν - 1 / lam i) 0` on modes with `0 < lam i`,
and zero power on every other mode (in particular on zero modes). -/
noncomputable def waterFilling {ι : Type*} (lam : ι → ℝ) (ν : ℝ) : ι → ℝ :=
  fun i => if 0 < lam i then max (ν - 1 / lam i) 0 else 0

/-! ### The allocation -/

/-- Water-filling powers are nonnegative. -/
theorem waterFilling_nonneg {ι : Type*} (lam : ι → ℝ) (ν : ℝ) (i : ι) :
    0 ≤ waterFilling lam ν i := by
  unfold waterFilling
  by_cases h : 0 < lam i
  · simp only [h, ite_eq_left]
    exact le_max_right _ _
  · simp only [h, ite_false]
    exact le_refl 0

/-- Zero modes receive zero power. -/
theorem waterFilling_eq_zero_of_lam_eq_zero {ι : Type*} {lam : ι → ℝ} (ν : ℝ) {i : ι}
    (hi : lam i = 0) :
    waterFilling lam ν i = 0 := by
  have h : ¬ 0 < lam i := by
    rw [hi]
    exact lt_irrefl _
  unfold waterFilling
  simp only [h, ite_false]

/-- The total water-filling power is the water-level sum. -/
theorem sum_waterFilling {ι : Type*} [Fintype ι] (lam : ι → ℝ) (ν : ℝ) :
    ∑ i, waterFilling lam ν i = waterLevelSum lam ν := by
  have h1 : ∀ i ∈ Finset.univ.filter (fun i => 0 < lam i),
      waterFilling lam ν i = max (ν - 1 / lam i) 0 := by
    intro i hi
    unfold waterFilling
    simp only [(Finset.mem_filter.mp hi).2, ite_eq_left]
  have h2 : ∀ i ∈ (Finset.univ : Finset ι),
      i ∉ Finset.univ.filter (fun i => 0 < lam i) → waterFilling lam ν i = 0 := by
    intro i _ hi
    have h : ¬ 0 < lam i :=
      fun hlt => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
    unfold waterFilling
    simp only [h, ite_false]
  unfold waterLevelSum
  rw [← Finset.sum_subset (Finset.filter_subset _ _) h2]
  exact Finset.sum_congr rfl h1

/-- At a level solving `waterLevelSum lam ν = P`, the water-filling allocation is admissible. -/
theorem waterFilling_mem_powerFeasible {ι : Type*} [Fintype ι] {lam : ι → ℝ} {ν P : ℝ}
    (hν : waterLevelSum lam ν = P) :
    waterFilling lam ν ∈ powerFeasible P := by
  refine ⟨fun i => waterFilling_nonneg _ _ _, ?_⟩
  rw [sum_waterFilling, hν]

/-! ### Constructing the water level -/

/-- **Existence of the water level.** If `P > 0` and some mode has `lam i > 0`, there is a level
`ν` with `∑_{lam i > 0} max (ν - 1 / lam i) 0 = P`. -/
theorem exists_waterLevelSum_eq {ι : Type*} [Fintype ι] {lam : ι → ℝ} {P : ℝ} (hP : 0 < P)
    (hlam : ∃ i, 0 < lam i) :
    ∃ ν, waterLevelSum lam ν = P := by
  obtain ⟨j, hj⟩ := hlam
  have hcont : Continuous (fun ν : ℝ => waterLevelSum lam ν) := by
    unfold waterLevelSum
    apply continuous_finsetSum
    intro i _
    exact (Continuous.sub continuous_id continuous_const).max continuous_const
  have hF0 : waterLevelSum lam 0 = 0 := by
    unfold waterLevelSum
    apply Finset.sum_eq_zero
    intro i hi
    have hlam : 0 < lam i := (Finset.mem_filter.mp hi).2
    have hpos : (0 : ℝ) < 1 / lam i := one_div_pos.mpr hlam
    have h1 : (0 : ℝ) - 1 / lam i ≤ 0 := by linarith
    exact max_eq_right h1
  have hjmem : j ∈ Finset.univ.filter (fun i => 0 < lam i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have hnonneg : ∀ i ∈ Finset.univ.filter (fun i => 0 < lam i),
      0 ≤ max ((P + 1 / lam j) - 1 / lam i) 0 :=
    fun i _ => le_max_right _ _
  have hle := Finset.single_le_sum hnonneg hjmem
  have hterm : max ((P + 1 / lam j) - 1 / lam j) 0 = P := by
    have hring : (P + 1 / lam j) - 1 / lam j = P := by ring
    rw [hring]
    exact max_eq_left (le_of_lt hP)
  rw [hterm] at hle
  have hM : (0 : ℝ) ≤ P + 1 / lam j := by
    have hpos : (0 : ℝ) < 1 / lam j := one_div_pos.mpr hj
    linarith
  have hmem : P ∈ Set.Icc (waterLevelSum lam 0) (waterLevelSum lam (P + 1 / lam j)) := by
    rw [hF0]
    exact ⟨le_of_lt hP, hle⟩
  have hsub := intermediate_value_Icc hM hcont.continuousOn
  obtain ⟨ν, _, hνeq⟩ := hsub hmem
  exact ⟨ν, hνeq⟩

/-- A level solving `waterLevelSum lam ν = P` for `P > 0` is positive. -/
theorem pos_of_waterLevelSum_eq {ι : Type*} [Fintype ι] {lam : ι → ℝ} {ν P : ℝ} (hP : 0 < P)
    (hν : waterLevelSum lam ν = P) :
    0 < ν := by
  by_contra hcon
  have hle : ν ≤ 0 := le_of_not_gt hcon
  have h0 : waterLevelSum lam ν = 0 := by
    unfold waterLevelSum
    apply Finset.sum_eq_zero
    intro i hi
    have hlam : 0 < lam i := (Finset.mem_filter.mp hi).2
    have h1 : (1 : ℝ) / lam i > 0 := one_div_pos.mpr hlam
    have h2 : ν - 1 / lam i ≤ 0 := by linarith
    exact max_eq_right h2
  rw [h0] at hν
  linarith

/-! ### KKT certificate -/

/-- **KKT conditions of the water-filling allocation.** With `w = waterFilling lam ν` and
`ν > 0`, every mode has marginal gain `lam i / (1 + lam i * w i) ≤ ν⁻¹`, with equality on every
mode that receives positive power. -/
theorem waterFilling_kkt {ι : Type*} (lam : ι → ℝ) {ν : ℝ} (hν : 0 < ν) (i : ι) :
    lam i / (1 + lam i * waterFilling lam ν i) ≤ ν⁻¹ ∧
      (0 < waterFilling lam ν i → lam i / (1 + lam i * waterFilling lam ν i) = ν⁻¹) := by
  by_cases h : 0 < lam i
  · have hw : waterFilling lam ν i = max (ν - 1 / lam i) 0 := by
      unfold waterFilling
      simp only [h, ite_eq_left]
    by_cases h2 : ν ≤ 1 / lam i
    · have hw0 : waterFilling lam ν i = 0 := by
        rw [hw]
        exact max_eq_right (sub_nonpos.mpr h2)
      have hle : lam i / (1 + lam i * waterFilling lam ν i) ≤ ν⁻¹ := by
        rw [hw0]
        simp only [mul_zero, add_zero, div_one]
        have h2' : ν * lam i ≤ 1 := (le_div_iff₀ h).mp h2
        have hgoal : lam i * ν ≤ 1 :=
          calc lam i * ν = ν * lam i := mul_comm _ _
            _ ≤ 1 := h2'
        calc lam i ≤ 1 / ν := (le_div_iff₀ hν).mpr hgoal
          _ = ν⁻¹ := one_div ν
      refine ⟨hle, ?_⟩
      intro hpos
      rw [hw0] at hpos
      exact absurd hpos (lt_irrefl 0)
    · have h2' : 1 / lam i < ν := not_le.mp h2
      have hwpos : waterFilling lam ν i = ν - 1 / lam i := by
        rw [hw]
        exact max_eq_left (le_of_lt (sub_pos.mpr h2'))
      have heq : lam i / (1 + lam i * waterFilling lam ν i) = ν⁻¹ := by
        rw [hwpos]
        have hne : lam i ≠ 0 := ne_of_gt h
        have hcancel : lam i * (1 / lam i) = 1 := mul_one_div_cancel hne
        have hmul : lam i * (ν - 1 / lam i) = lam i * ν - 1 := by
          rw [mul_sub, hcancel]
        have hden : 1 + lam i * (ν - 1 / lam i) = lam i * ν := by
          rw [hmul]
          ring
        rw [hden, div_eq_mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      exact ⟨le_of_eq heq, fun _ => heq⟩
  · have hw0 : waterFilling lam ν i = 0 := by
      unfold waterFilling
      simp only [h, ite_false]
    have hle : lam i / (1 + lam i * waterFilling lam ν i) ≤ ν⁻¹ := by
      rw [hw0]
      simp only [mul_zero, add_zero, div_one]
      have hlam0 : lam i ≤ 0 := le_of_not_gt h
      have hνinv : (0 : ℝ) < ν⁻¹ := inv_pos.mpr hν
      linarith
    refine ⟨hle, ?_⟩
    intro hpos
    rw [hw0] at hpos
    exact absurd hpos (lt_irrefl 0)

/-- **Convex/KKT sufficient condition for the sum-rate problem.** For gains `lam i ≥ 0`, a
nonnegative allocation `p` spending the whole budget (`∑ i, p i = P`) whose marginal gains satisfy
the KKT conditions at level `ν > 0` maximizes `sumRateBits lam` on `powerFeasible P`. To be derived
from Atlas `KarushKuhnTucker.isMinOn_of_karush_kuhn_tucker_convex` (multipliers
`(2 log 2 ν)⁻¹` for the budget and `(ν⁻¹ - lam i / (1 + lam i * p i)) / (2 log 2)` for `p i ≥ 0`). -/
theorem isMaxOn_sumRateBits_of_kkt {ι : Type*} [Fintype ι] {lam p : ι → ℝ} {ν P : ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hν : 0 < ν) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = P)
    (hkkt : ∀ i, lam i / (1 + lam i * p i) ≤ ν⁻¹ ∧
      (0 < p i → lam i / (1 + lam i * p i) = ν⁻¹)) :
    IsMaxOn (sumRateBits lam) (powerFeasible P) p := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < 2 * Real.log 2 := by linarith
  intro q hq
  simp only [powerFeasible, Set.mem_ofPred_eq] at hq
  obtain ⟨hq0, hqsum⟩ := hq
  show sumRateBits lam q ≤ sumRateBits lam p
  have key : ∀ i, Real.log (1 + lam i * q i) - Real.log (1 + lam i * p i)
      ≤ (lam i / (1 + lam i * p i)) * (q i - p i) := by
    intro i
    have h1 : 0 ≤ lam i * p i := mul_nonneg (hlam i) (hp i)
    have h2 : 0 ≤ lam i * q i := mul_nonneg (hlam i) (hq0 i)
    have ha : 0 < 1 + lam i * p i := by linarith
    have hb : 0 < 1 + lam i * q i := by linarith
    have hdiv : 0 < (1 + lam i * q i) / (1 + lam i * p i) := div_pos hb ha
    have hlog := Real.log_le_sub_one_of_pos hdiv
    rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at hlog
    have heq : (1 + lam i * q i) / (1 + lam i * p i) - 1
        = (lam i / (1 + lam i * p i)) * (q i - p i) := by
      have ha0 : (1 + lam i * p i) ≠ 0 := ne_of_gt ha
      field_simp
      ring
    rw [heq] at hlog
    exact hlog
  have hsumle : (∑ i, Real.log (1 + lam i * q i)) - (∑ i, Real.log (1 + lam i * p i))
      ≤ ∑ i, (lam i / (1 + lam i * p i)) * (q i - p i) := by
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => key i)
    rwa [Finset.sum_sub_distrib] at hle
  have hlin : ∀ i, (lam i / (1 + lam i * p i)) * (q i - p i) ≤ ν⁻¹ * (q i - p i) := by
    intro i
    obtain ⟨hmle, hmeq⟩ := hkkt i
    by_cases hpi : 0 < p i
    · simp only [hmeq hpi, le_rfl]
    · have hpi0 : p i = 0 := le_antisymm (le_of_not_gt hpi) (hp i)
      have hdiff : 0 ≤ q i - p i := by
        rw [hpi0, sub_zero]
        exact hq0 i
      exact mul_le_mul_of_nonneg_right hmle hdiff
  have hlinle : ∑ i, (lam i / (1 + lam i * p i)) * (q i - p i)
      ≤ ν⁻¹ * ((∑ i, q i) - P) := by
    have h1 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlin i)
    have h2 : ∑ i, ν⁻¹ * (q i - p i) = ν⁻¹ * ((∑ i, q i) - P) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
    rw [h2] at h1
    exact h1
  have hnonpos : ν⁻¹ * ((∑ i, q i) - P) ≤ 0 := by
    have hνinv : 0 ≤ ν⁻¹ := le_of_lt (inv_pos.mpr hν)
    have hdiff : (∑ i, q i) - P ≤ 0 := sub_nonpos.mpr hqsum
    exact mul_nonpos_of_nonneg_of_nonpos hνinv hdiff
  have hS : (∑ i, Real.log (1 + lam i * q i)) - (∑ i, Real.log (1 + lam i * p i)) ≤ 0 :=
    le_trans (le_trans hsumle hlinle) hnonpos
  have hdiv : ∀ f : ι → ℝ,
      (∑ i, f i / (2 * Real.log 2)) = (∑ i, f i) / (2 * Real.log 2) := by
    intro f
    simp only [div_eq_mul_inv]
    exact (Finset.sum_mul _ _ _).symm
  unfold sumRateBits
  rw [hdiv, hdiv]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (inv_pos.mpr hC))
  linarith [hS]

/-- **Water-filling is optimal.** For gains `lam i ≥ 0`, `P > 0` and a level `ν` with
`waterLevelSum lam ν = P`, the water-filling allocation is admissible and maximizes the sum rate
in bits. -/
theorem isMaxOn_waterFilling {ι : Type*} [Fintype ι] {lam : ι → ℝ} {ν P : ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hP : 0 < P) (hν : waterLevelSum lam ν = P) :
    waterFilling lam ν ∈ powerFeasible P ∧
      IsMaxOn (sumRateBits lam) (powerFeasible P) (waterFilling lam ν) := by
  have hνpos : 0 < ν := pos_of_waterLevelSum_eq hP hν
  have hmem : waterFilling lam ν ∈ powerFeasible P := waterFilling_mem_powerFeasible hν
  have hsum : ∑ i, waterFilling lam ν i = P := by rw [sum_waterFilling, hν]
  refine ⟨hmem, isMaxOn_sumRateBits_of_kkt hlam hνpos (fun i => waterFilling_nonneg _ _ _)
    hsum ?_⟩
  intro i
  exact waterFilling_kkt lam hνpos i

/-! ### Degenerate cases: zero power and all-zero modes -/

/-- With zero budget the only admissible allocation is zero. -/
theorem powerFeasible_zero {ι : Type*} [Fintype ι] :
    powerFeasible (ι := ι) 0 = {0} := by
  ext p
  simp only [powerFeasible, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨h0, hsum⟩ := h
    have hge : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => h0 i)
    have heq : ∑ i, p i = 0 := le_antisymm hsum hge
    have hall : ∀ i ∈ Finset.univ, p i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h0 i)).mp heq
    funext i
    simpa using hall i (Finset.mem_univ i)
  · rintro rfl
    simp

/-- With zero budget, zero power is optimal (for any gains). -/
theorem isMaxOn_zero_of_power_eq_zero {ι : Type*} [Fintype ι] (lam : ι → ℝ) :
    IsMaxOn (sumRateBits lam) (powerFeasible 0) 0 := by
  rw [powerFeasible_zero]
  intro y hy
  have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
  subst hy0
  show sumRateBits lam 0 ≤ sumRateBits lam 0
  exact le_rfl

/-- If every mode is a zero mode, the sum rate vanishes for every allocation. -/
theorem sumRateBits_of_forall_lam_eq_zero {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (h0 : ∀ i, lam i = 0) (p : ι → ℝ) :
    sumRateBits lam p = 0 := by
  unfold sumRateBits
  simp [h0]

/-- If every mode is a zero mode and `P ≥ 0`, zero power is admissible and optimal. -/
theorem isMaxOn_zero_of_forall_lam_eq_zero {ι : Type*} [Fintype ι] {lam : ι → ℝ} {P : ℝ}
    (h0 : ∀ i, lam i = 0) (hP : 0 ≤ P) :
    (0 : ι → ℝ) ∈ powerFeasible P ∧ IsMaxOn (sumRateBits lam) (powerFeasible P) 0 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    exact le_refl 0
  · simpa using hP
  · intro y _
    show sumRateBits lam y ≤ sumRateBits lam 0
    rw [sumRateBits_of_forall_lam_eq_zero h0 y, sumRateBits_of_forall_lam_eq_zero h0 0]

/-! ### Headline -/

/-- **Water-filling solves the finite parallel Gaussian power allocation problem.** For gains
`lam i ≥ 0` and budget `P ≥ 0` there is an admissible allocation `p` maximizing
`∑ i, log (1 + lam i * p i) / (2 * log 2)` over `p i ≥ 0`, `∑ i, p i ≤ P`, such that zero modes
receive zero power; if `P > 0` and some `lam i > 0`, then `p` is the water-filling allocation at a
level `ν > 0` with `∑_{lam i > 0} max (ν - 1 / lam i) 0 = P`, certified by the KKT conditions;
and if `P = 0` or all modes are zero, then `p = 0`. -/
theorem exists_isMaxOn_sumRateBits {ι : Type*} [Fintype ι] {lam : ι → ℝ} {P : ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hP : 0 ≤ P) :
    ∃ p ∈ powerFeasible P, IsMaxOn (sumRateBits lam) (powerFeasible P) p ∧
      (∀ i, lam i = 0 → p i = 0) ∧
      ((0 < P ∧ ∃ i, 0 < lam i) →
        ∃ ν, 0 < ν ∧ waterLevelSum lam ν = P ∧ p = waterFilling lam ν ∧
          ∀ i, lam i / (1 + lam i * p i) ≤ ν⁻¹ ∧
            (0 < p i → lam i / (1 + lam i * p i) = ν⁻¹)) ∧
      ((P = 0 ∨ ∀ i, lam i = 0) → p = 0) := by
  by_cases h : 0 < P ∧ ∃ i, 0 < lam i
  · obtain ⟨hP, hex⟩ := h
    obtain ⟨ν, hν⟩ := exists_waterLevelSum_eq hP hex
    have hνpos : 0 < ν := pos_of_waterLevelSum_eq hP hν
    obtain ⟨hmem, hmax⟩ := isMaxOn_waterFilling hlam hP hν
    refine ⟨waterFilling lam ν, hmem, hmax,
      (fun i hi => waterFilling_eq_zero_of_lam_eq_zero ν hi), ?_, ?_⟩
    · intro _
      exact ⟨ν, hνpos, hν, rfl, fun i => waterFilling_kkt lam hνpos i⟩
    · intro hcon
      rcases hcon with rfl | hall
      · exfalso
        linarith
      · obtain ⟨j, hj⟩ := hex
        have hj0 := hall j
        exfalso
        linarith
  · have hdegen : P = 0 ∨ ∀ i, lam i = 0 := by
      by_cases hP0 : P = 0
      · exact Or.inl hP0
      · have hPpos : 0 < P := lt_of_le_of_ne hP (Ne.symm hP0)
        right
        intro i
        have h1 : ¬ 0 < lam i := fun hi => h ⟨hPpos, ⟨i, hi⟩⟩
        exact le_antisymm (le_of_not_gt h1) (hlam i)
    have hmem0 : (0 : ι → ℝ) ∈ powerFeasible P := by
      refine ⟨?_, ?_⟩
      · intro i
        exact le_refl 0
      · simpa using hP
    have hmax0 : IsMaxOn (sumRateBits lam) (powerFeasible P) 0 := by
      rcases hdegen with rfl | hall
      · exact isMaxOn_zero_of_power_eq_zero lam
      · exact (isMaxOn_zero_of_forall_lam_eq_zero hall hP).2
    refine ⟨0, hmem0, hmax0, (fun i _ => rfl), ?_, ?_⟩
    · intro hcon
      exact False.elim (h hcon)
    · intro _
      rfl

/-! ### Validation cases -/

/-- Two unequal positive modes with an inactive low-gain mode: gains `(2, 1, 1/4)`, budget
`3/2`, level `ν = 3/2` (`1/2 + 1 = ν - 1/2 + ν - 1`), allocation `(1, 1/2, 0)`; the third mode is
inactive since `3/2 < 4 = 1 / (1/4)`. -/
theorem waterFilling_twoActive_oneInactive :
    waterLevelSum ![(2 : ℝ), 1, 1 / 4] (3 / 2) = 3 / 2 ∧
      waterFilling ![(2 : ℝ), 1, 1 / 4] (3 / 2) = ![1, 1 / 2, 0] := by
  have g0 : ![(2 : ℝ), 1, 1 / 4] 0 = 2 := rfl
  have g1 : ![(2 : ℝ), 1, 1 / 4] 1 = 1 := rfl
  have g2 : ![(2 : ℝ), 1, 1 / 4] 2 = 1 / 4 := rfl
  have m1 : max ((3 : ℝ) / 2 - 1 / 2) 0 = 1 := by
    rw [max_eq_left (by norm_num : (0 : ℝ) ≤ 3 / 2 - 1 / 2)]
    norm_num
  have m2 : max ((3 : ℝ) / 2 - 1 / 1) 0 = 1 / 2 := by
    rw [max_eq_left (by norm_num : (0 : ℝ) ≤ 3 / 2 - 1 / 1)]
    norm_num
  have m3 : max ((3 : ℝ) / 2 - 1 / (1 / 4)) 0 = 0 :=
    max_eq_right (by norm_num : (3 : ℝ) / 2 - 1 / (1 / 4) ≤ 0)
  have w0 : (if 0 < (2 : ℝ) then max ((3 : ℝ) / 2 - 1 / 2) 0 else 0) = 1 := by
    have hc : (0 : ℝ) < 2 := by norm_num
    simp only [hc, ite_eq_left]
    exact m1
  have w1 : (if 0 < (1 : ℝ) then max ((3 : ℝ) / 2 - 1 / 1) 0 else 0) = 1 / 2 := by
    have hc : (0 : ℝ) < 1 := by norm_num
    simp only [hc, ite_eq_left]
    exact m2
  have w2 : (if 0 < ((1 : ℝ) / 4) then max ((3 : ℝ) / 2 - 1 / (1 / 4)) 0 else 0) = 0 := by
    have hc : (0 : ℝ) < 1 / 4 := by norm_num
    simp only [hc, ite_eq_left]
    exact m3
  constructor
  · unfold waterLevelSum
    rw [Finset.sum_filter, Fin.sum_univ_three, g0, g1, g2]
    have c0 : (0 : ℝ) < 2 := by norm_num
    have c1 : (0 : ℝ) < 1 := by norm_num
    have c2 : (0 : ℝ) < 1 / 4 := by norm_num
    simp only [c0, c1, c2, ite_eq_left]
    rw [m1, m2, m3]
    norm_num
  · funext i
    fin_cases i
    · show (if 0 < (2 : ℝ) then max ((3 : ℝ) / 2 - 1 / 2) 0 else 0) = (1 : ℝ)
      exact w0
    · show (if 0 < (1 : ℝ) then max ((3 : ℝ) / 2 - 1 / 1) 0 else 0) = (1 / 2 : ℝ)
      exact w1
    · show (if 0 < ((1 : ℝ) / 4) then max ((3 : ℝ) / 2 - 1 / (1 / 4)) 0 else 0)
          = (0 : ℝ)
      exact w2

/-- The allocation `(1, 1/2, 0)` is optimal for gains `(2, 1, 1/4)` and budget `3/2`. -/
theorem isMaxOn_twoActive_oneInactive :
    IsMaxOn (sumRateBits ![(2 : ℝ), 1, 1 / 4]) (powerFeasible (3 / 2)) ![1, 1 / 2, 0] := by
  have h := waterFilling_twoActive_oneInactive
  have hlam : ∀ i, 0 ≤ ![(2 : ℝ), 1, 1 / 4] i := by
    intro i
    fin_cases i
    · show (0 : ℝ) ≤ 2; norm_num
    · show (0 : ℝ) ≤ 1; norm_num
    · show (0 : ℝ) ≤ 1 / 4; norm_num
  rw [← h.2]
  exact (isMaxOn_waterFilling hlam (by norm_num) h.1).2

/-- Its value is `log (3 · 3/2 · 1) / (2 log 2) = log (9/2) / (2 log 2)` bits. -/
theorem sumRateBits_twoActive_oneInactive :
    sumRateBits ![(2 : ℝ), 1, 1 / 4] ![1, 1 / 2, 0] = Real.log (9 / 2) / (2 * Real.log 2) := by
  have g0 : ![(2 : ℝ), 1, 1 / 4] 0 = 2 := rfl
  have g1 : ![(2 : ℝ), 1, 1 / 4] 1 = 1 := rfl
  have g2 : ![(2 : ℝ), 1, 1 / 4] 2 = 1 / 4 := rfl
  have p0 : ![1, 1 / 2, 0] 0 = (1 : ℝ) := rfl
  have p1 : ![1, 1 / 2, 0] 1 = (1 / 2 : ℝ) := rfl
  have p2 : ![1, 1 / 2, 0] 2 = (0 : ℝ) := rfl
  unfold sumRateBits
  rw [Fin.sum_univ_three, g0, g1, g2, p0, p1, p2]
  have e1 : (1 : ℝ) + 2 * 1 = 3 := by norm_num
  have e2 : (1 : ℝ) + 1 * (1 / 2) = 3 / 2 := by norm_num
  have e3 : (1 : ℝ) + 1 / 4 * 0 = 1 := by norm_num
  rw [e1, e2, e3, Real.log_one, zero_div, add_zero]
  have h92 : (9 : ℝ) / 2 = 3 * (3 / 2) := by norm_num
  rw [h92, Real.log_mul (by norm_num) (by norm_num), add_div]

/-- `P = 0` with positive gains: zero power is optimal. -/
theorem isMaxOn_zeroPower_example :
    IsMaxOn (sumRateBits ![(2 : ℝ), 1]) (powerFeasible 0) 0 := by
  exact isMaxOn_zero_of_power_eq_zero _

/-- One zero mode: gains `(1, 0)`, budget `1`, level `ν = 2`; the zero mode gets zero power and
the allocation `(1, 0)` is optimal. -/
theorem isMaxOn_oneZeroMode :
    waterLevelSum ![(1 : ℝ), 0] 2 = 1 ∧ waterFilling ![(1 : ℝ), 0] 2 = ![1, 0] ∧
      IsMaxOn (sumRateBits ![(1 : ℝ), 0]) (powerFeasible 1) ![1, 0] := by
  have g0 : ![(1 : ℝ), 0] 0 = (1 : ℝ) := rfl
  have g1 : ![(1 : ℝ), 0] 1 = (0 : ℝ) := rfl
  have h1 : waterLevelSum ![(1 : ℝ), 0] 2 = 1 := by
    unfold waterLevelSum
    rw [Finset.sum_filter, Fin.sum_univ_two, g0, g1]
    have c0 : (0 : ℝ) < 1 := by norm_num
    have c1 : ¬ (0 : ℝ) < 0 := lt_irrefl 0
    simp only [c0, ite_eq_left, c1, ite_false]
    rw [max_eq_left (by norm_num : (0 : ℝ) ≤ (2 : ℝ) - 1 / 1)]
    norm_num
  have h2 : waterFilling ![(1 : ℝ), 0] 2 = ![1, 0] := by
    funext i
    fin_cases i
    · show (if 0 < (1 : ℝ) then max ((2 : ℝ) - 1 / 1) 0 else 0) = (1 : ℝ)
      have hc : (0 : ℝ) < 1 := by norm_num
      simp only [hc, ite_eq_left]
      rw [max_eq_left (by norm_num : (0 : ℝ) ≤ (2 : ℝ) - 1 / 1)]
      norm_num
    · show (if 0 < (0 : ℝ) then max ((2 : ℝ) - 1 / 0) 0 else 0) = (0 : ℝ)
      have hc : ¬ (0 : ℝ) < 0 := lt_irrefl 0
      simp only [hc, ite_false]
  have hlam : ∀ i, 0 ≤ ![(1 : ℝ), 0] i := by
    intro i
    fin_cases i
    · show (0 : ℝ) ≤ 1; norm_num
    · show (0 : ℝ) ≤ 0; norm_num
  have h3 : IsMaxOn (sumRateBits ![(1 : ℝ), 0]) (powerFeasible 1) ![1, 0] := by
    have hmain := (isMaxOn_waterFilling hlam (by norm_num) h1).2
    rwa [h2] at hmain
  exact ⟨h1, h2, h3⟩

/-- All modes zero: with budget `1`, zero power is optimal. -/
theorem isMaxOn_allZeroModes :
    IsMaxOn (sumRateBits (0 : Fin 2 → ℝ)) (powerFeasible 1) 0 := by
  exact (isMaxOn_zero_of_forall_lam_eq_zero (fun i => rfl) (by norm_num)).2

/-- Violated premise (the inverse formula evaluated at a zero gain): for gains `(1, 0)` and budget
`1`, the unguarded equation `∑ i, max (ν - 1 / lam i) 0 = 1` over all modes (with Lean's
`1 / 0 = 0`) is solved by `ν = 1` and allocates `(0, 1)`, all power on the zero mode; that
allocation is not optimal. -/
theorem unguarded_waterFilling_not_isMaxOn :
    ∑ i, max ((1 : ℝ) - 1 / ![(1 : ℝ), 0] i) 0 = 1 ∧
      (fun i => max ((1 : ℝ) - 1 / ![(1 : ℝ), 0] i) 0) = ![0, 1] ∧
      ¬ IsMaxOn (sumRateBits ![(1 : ℝ), 0]) (powerFeasible 1) ![0, 1] := by
  have g0 : ![(1 : ℝ), 0] 0 = (1 : ℝ) := rfl
  have g1 : ![(1 : ℝ), 0] 1 = (0 : ℝ) := rfl
  have q0 : ![0, 1] 0 = (0 : ℝ) := rfl
  have q1 : ![0, 1] 1 = (1 : ℝ) := rfl
  have m1 : max ((1 : ℝ) - 1 / 1) 0 = 0 :=
    max_eq_right (by norm_num : (1 : ℝ) - 1 / 1 ≤ 0)
  have m2 : max ((1 : ℝ) - 1 / 0) 0 = 1 := by
    rw [div_zero, sub_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
  have part1 : ∑ i, max ((1 : ℝ) - 1 / ![(1 : ℝ), 0] i) 0 = 1 := by
    rw [Fin.sum_univ_two, g0, g1, m1, m2]
    norm_num
  have part2 : (fun i => max ((1 : ℝ) - 1 / ![(1 : ℝ), 0] i) 0) = ![0, 1] := by
    funext i
    fin_cases i
    · show max ((1 : ℝ) - 1 / 1) 0 = (0 : ℝ)
      exact m1
    · show max ((1 : ℝ) - 1 / 0) 0 = (1 : ℝ)
      exact m2
  have part3 : ¬ IsMaxOn (sumRateBits ![(1 : ℝ), 0]) (powerFeasible 1) ![0, 1] := by
    intro hcon
    have hmem : ![(1 : ℝ), 0] ∈ powerFeasible (1 : ℝ) := by
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i
        · show (0 : ℝ) ≤ 1; norm_num
        · show (0 : ℝ) ≤ 0; norm_num
      · rw [Fin.sum_univ_two, g0, g1]
        norm_num
    have hle : sumRateBits ![(1 : ℝ), 0] ![1, 0]
        ≤ sumRateBits ![(1 : ℝ), 0] ![0, 1] := hcon hmem
    have e1 : sumRateBits ![(1 : ℝ), 0] ![1, 0]
        = Real.log 2 / (2 * Real.log 2) := by
      unfold sumRateBits
      rw [Fin.sum_univ_two, g0, g1]
      have a1 : (1 : ℝ) + 1 * 1 = 2 := by norm_num
      have a2 : (1 : ℝ) + 0 * 0 = 1 := by norm_num
      rw [a1, a2, Real.log_one, zero_div, add_zero]
    have e2 : sumRateBits ![(1 : ℝ), 0] ![0, 1] = 0 := by
      unfold sumRateBits
      rw [Fin.sum_univ_two, g0, g1, q0, q1]
      have b1 : (1 : ℝ) + 1 * 0 = 1 := by norm_num
      have b2 : (1 : ℝ) + 0 * 1 = 1 := by norm_num
      rw [b1, b2, Real.log_one, zero_div, add_zero]
    rw [e1, e2] at hle
    have hpos : 0 < Real.log 2 / (2 * Real.log 2) := by
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hC : 0 < 2 * Real.log 2 := by linarith
      exact div_pos hl2 hC
    linarith
  exact ⟨part1, part2, part3⟩

end MathlibExt.Analysis.Convex.WaterFillingCertificate
