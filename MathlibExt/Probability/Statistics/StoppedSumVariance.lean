/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Variance of a stopped sum with bounded count

Finite collective model: for i.i.d. `MemLp`-2 severities independent of the
bounded count `N`, the variance of the stopped sum splits into `E[N] * Var[X]`
plus `Var[N] * (E[X]) ^ 2`.
-/
open MeasureTheory ProbabilityTheory
namespace MathlibExt.Probability.Finance.FiniteCollectiveVariance
private theorem variance_congr_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (h : f =ᵐ[μ] g) :
    ProbabilityTheory.variance f μ = ProbabilityTheory.variance g μ :=
  ProbabilityTheory.variance_congr h
private theorem indepFun_integral_mul_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {G H : Ω → ℝ} (h : ProbabilityTheory.IndepFun G H μ)
    (hG : AEStronglyMeasurable G μ) (hH : AEStronglyMeasurable H μ) :
    ∫ ω, G ω * H ω ∂μ = (∫ ω, G ω ∂μ) * ∫ ω, H ω ∂μ :=
  ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral h hG hH
private theorem indepFun_N_bridge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (X : ℕ → Ω → ℝ)
    (hindepN : ProbabilityTheory.Indep (MeasurableSpace.comap N inferInstance)
      (⨆ i, MeasurableSpace.comap (X i) inferInstance) μ)
    (G : Ω → ℝ) (φ : ℕ → ℝ)
    (hG : @Measurable Ω ℝ (⨆ i, MeasurableSpace.comap (X i) inferInstance) inferInstance G)
    (hφ : Measurable φ) :
    ProbabilityTheory.IndepFun G (φ ∘ N) μ := by
  have hsym : ProbabilityTheory.Indep
      (⨆ i, MeasurableSpace.comap (X i) inferInstance)
      (MeasurableSpace.comap N inferInstance) μ :=
    hindepN.symm
  have hleG : MeasurableSpace.comap G inferInstance ≤
      (⨆ i, MeasurableSpace.comap (X i) inferInstance) :=
    hG.comap_le
  have hleN : MeasurableSpace.comap (φ ∘ N) inferInstance ≤
      MeasurableSpace.comap N inferInstance :=
    MeasurableSpace.comap_le_comap_of_eq_comp φ hφ rfl
  rw [ProbabilityTheory.IndepFun_iff_Indep]
  exact ProbabilityTheory.Kernel.indep_of_indep_of_le hsym hleG hleN
/-- Variance of a stopped sum with bounded count (finite collective model). -/
theorem variance_stopped_sum_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ) (hN : Measurable N)
    (nmax : ℕ) (hNb : ∀ᵐ ω ∂μ, N ω ≤ nmax) (X : ℕ → Ω → ℝ)
    (hX2 : ∀ i, MemLp (X i) 2 μ) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hindepX : iIndepFun X μ)
    (hindepN : ProbabilityTheory.Indep (MeasurableSpace.comap N inferInstance)
      (⨆ i, MeasurableSpace.comap (X i) inferInstance) μ) :
    ProbabilityTheory.variance (fun ω => ∑ i ∈ Finset.range (N ω), X i ω) μ =
      (∫ ω, (N ω : ℝ) ∂μ) * ProbabilityTheory.variance (X 0) μ +
        ProbabilityTheory.variance (fun ω => (N ω : ℝ)) μ *
          (∫ ω, X 0 ω ∂μ) ^ 2 := by
  have hφmeas : ∀ i : ℕ, Measurable (fun n : ℕ => if i < n then (1 : ℝ) else (0 : ℝ)) := by
    intro i
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_const measurable_id'
  have ha_meas : ∀ i : ℕ, Measurable (fun ω => if i < N ω then (1 : ℝ) else (0 : ℝ)) := by
    intro i
    exact (hφmeas i).comp hN
  have hY_meas : ∀ i : ℕ,
      Measurable (fun ω => X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) :=
    fun i => (hmeas i).mul (ha_meas i)
  have hA_meas : Measurable
      (fun ω => ∑ i ∈ Finset.range nmax, (if i < N ω then (1 : ℝ) else (0 : ℝ))) :=
    Finset.measurable_sum _ (fun i _ => ha_meas i)
  have hXX_meas : ∀ i j : ℕ, Measurable (fun ω => X i ω * X j ω) :=
    fun i j => (hmeas i).mul (hmeas j)
  have hAA_meas : ∀ i j : ℕ, Measurable (fun ω => (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
      (if j < N ω then (1 : ℝ) else (0 : ℝ))) :=
    fun i j => (ha_meas i).mul (ha_meas j)
  have hA_N : (fun ω => ∑ i ∈ Finset.range nmax, (if i < N ω then (1 : ℝ) else (0 : ℝ))) =ᵐ[μ]
      (fun ω => (N ω : ℝ)) := by
    filter_upwards [hNb] with ω hω
    show (∑ i ∈ Finset.range nmax, (if i < N ω then (1 : ℝ) else (0 : ℝ))) = (N ω : ℝ)
    have hsub : Finset.range (N ω) ⊆ Finset.range nmax := by
      intro x hx
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hω)
    have hz : ∀ x ∈ Finset.range nmax, x ∉ Finset.range (N ω) →
        (if x < N ω then (1 : ℝ) else (0 : ℝ)) = 0 :=
      fun x _ hx => ite_eq_right (fun hlt => hx (Finset.mem_range.mpr hlt))
    have hcongr : ∑ i ∈ Finset.range (N ω), (if i < N ω then (1 : ℝ) else (0 : ℝ))
        = ∑ i ∈ Finset.range (N ω), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ite_eq_left (Finset.mem_range.mp hi)
    have hcard : ∑ i ∈ Finset.range (N ω), (1 : ℝ) = (N ω : ℝ) := by simp
    calc (∑ i ∈ Finset.range nmax, (if i < N ω then (1 : ℝ) else (0 : ℝ)))
        = ∑ i ∈ Finset.range (N ω), (if i < N ω then (1 : ℝ) else (0 : ℝ)) :=
          (Finset.sum_subset hsub hz).symm
      _ = ∑ i ∈ Finset.range (N ω), (1 : ℝ) := hcongr
      _ = (N ω : ℝ) := hcard
  have hF_S : (fun ω => ∑ i ∈ Finset.range nmax,
      X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) =ᵐ[μ]
      (fun ω => ∑ i ∈ Finset.range (N ω), X i ω) := by
    filter_upwards [hNb] with ω hω
    show (∑ i ∈ Finset.range nmax, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ)))
      = ∑ i ∈ Finset.range (N ω), X i ω
    have hsub : Finset.range (N ω) ⊆ Finset.range nmax := by
      intro x hx
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hω)
    have hYif : ∀ k : ℕ, X k ω * (if k < N ω then (1 : ℝ) else (0 : ℝ))
        = (if k < N ω then X k ω else (0 : ℝ)) := by
      intro k
      by_cases hk : k < N ω <;> simp [hk]
    have hz : ∀ x ∈ Finset.range nmax, x ∉ Finset.range (N ω) →
        X x ω * (if x < N ω then (1 : ℝ) else (0 : ℝ)) = 0 := by
      intro x _ hx
      rw [hYif x, ite_eq_right (fun hlt => hx (Finset.mem_range.mpr hlt))]
    rw [← Finset.sum_subset hsub hz]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hYif i, ite_eq_left (Finset.mem_range.mp hi)]
  have hXint : ∀ i : ℕ, Integrable (X i) μ :=
    fun i => (hX2 i).integrable (by simp)
  have hYint : ∀ i : ℕ,
      Integrable (fun ω => X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) μ := by
    intro i
    have hbdd : ∀ᵐ ω ∂μ, ‖(if i < N ω then (1 : ℝ) else (0 : ℝ))‖ ≤ 1 := by
      apply Filter.Eventually.of_forall
      intro ω
      by_cases h : i < N ω <;> simp [h]
    exact (hXint i).mul_bdd (ha_meas i).aestronglyMeasurable hbdd
  have hXXint : ∀ i j : ℕ, Integrable (fun ω => X i ω * X j ω) μ :=
    fun i j => MemLp.integrable_mul (hX2 i) (hX2 j)
  have hYXYint : ∀ i j : ℕ, Integrable
      (fun ω => (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
        (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ)))) μ := by
    intro i j
    have hbdd : ∀ᵐ ω ∂μ, ‖(if i < N ω then (1 : ℝ) else (0 : ℝ)) *
        (if j < N ω then (1 : ℝ) else (0 : ℝ))‖ ≤ 1 := by
      apply Filter.Eventually.of_forall
      intro ω
      by_cases hi : i < N ω <;> by_cases hj : j < N ω <;> simp [hi, hj]
    have hmul := (hXXint i j).mul_bdd (hAA_meas i j).aestronglyMeasurable hbdd
    refine Integrable.congr hmul ?_
    apply Filter.Eventually.of_forall
    intro ω
    ring
  have haint : ∀ i : ℕ, Integrable (fun ω => if i < N ω then (1 : ℝ) else (0 : ℝ)) μ := by
    intro i
    have hbdd : ∀ᵐ ω ∂μ, ‖(if i < N ω then (1 : ℝ) else (0 : ℝ))‖ ≤ 1 := by
      apply Filter.Eventually.of_forall
      intro ω
      by_cases h : i < N ω <;> simp [h]
    have hmul := (integrable_const (1 : ℝ)).mul_bdd (ha_meas i).aestronglyMeasurable hbdd
    refine Integrable.congr hmul ?_
    apply Filter.Eventually.of_forall
    intro ω
    exact one_mul _
  have haaint : ∀ i j : ℕ, Integrable (fun ω => (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
      (if j < N ω then (1 : ℝ) else (0 : ℝ))) μ := by
    intro i j
    have hbdd : ∀ᵐ ω ∂μ, ‖(if i < N ω then (1 : ℝ) else (0 : ℝ)) *
        (if j < N ω then (1 : ℝ) else (0 : ℝ))‖ ≤ 1 := by
      apply Filter.Eventually.of_forall
      intro ω
      by_cases hi : i < N ω <;> by_cases hj : j < N ω <;> simp [hi, hj]
    have hmul := (integrable_const (1 : ℝ)).mul_bdd (hAA_meas i j).aestronglyMeasurable hbdd
    refine Integrable.congr hmul ?_
    apply Filter.Eventually.of_forall
    intro ω
    exact one_mul _
  have hYmem : ∀ i : ℕ,
      MemLp (fun ω => X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) 2 μ := by
    intro i
    have hbdd : ∀ᵐ ω ∂μ, ‖(if i < N ω then (1 : ℝ) else (0 : ℝ))‖ ≤ 1 := by
      apply Filter.Eventually.of_forall
      intro ω
      by_cases h : i < N ω <;> simp [h]
    have ha_top : MemLp (fun ω => if i < N ω then (1 : ℝ) else (0 : ℝ)) ⊤ μ :=
      MemLp.of_bound (ha_meas i).aestronglyMeasurable 1 hbdd
    exact MemLp.mul (hX2 i) ha_top
  have hFmem : MemLp
      (fun ω => ∑ i ∈ Finset.range nmax, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) 2 μ :=
    memLp_finsetSum _ (fun i _ => hYmem i)
  have hNmeas : Measurable (fun ω => (N ω : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hN
  have hNmem : MemLp (fun ω => (N ω : ℝ)) 2 μ := by
    refine MemLp.of_bound hNmeas.aestronglyMeasurable (nmax : ℝ) ?_
    refine Filter.Eventually.mono hNb (fun ω hω => ?_)
    change ‖(N ω : ℝ)‖ ≤ (nmax : ℝ)
    calc ‖(N ω : ℝ)‖ = (N ω : ℝ) := norm_natCast _
      _ ≤ (nmax : ℝ) := Nat.cast_le.mpr hω
  have hmean : ∀ i : ℕ, ∫ ω, X i ω ∂μ = ∫ ω, X 0 ω ∂μ :=
    fun i => (hident i).integral_eq
  have hsq : ∀ i : ℕ, ∫ ω, (X i ω) ^ 2 ∂μ = ∫ ω, (X 0 ω) ^ 2 ∂μ := by
    intro i
    have hφ : Measurable (fun x : ℝ => x ^ 2) := measurable_id'.pow_const 2
    have hcomp := (hident i).comp hφ
    have heq := hcomp.integral_eq
    have e1 : ∫ ω, (X i ω) ^ 2 ∂μ = ∫ ω, ((fun x : ℝ => x ^ 2) ∘ X i) ω ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      simp only [Function.comp_apply]
    have e0 : ∫ ω, (X 0 ω) ^ 2 ∂μ = ∫ ω, ((fun x : ℝ => x ^ 2) ∘ X 0) ω ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      simp only [Function.comp_apply]
    rw [e1, e0]
    exact heq
  have hVarX0 : ProbabilityTheory.variance (X 0) μ
      = ∫ ω, (X 0 ω) ^ 2 ∂μ - (∫ ω, X 0 ω ∂μ) ^ 2 :=
    ProbabilityTheory.variance_eq_sub (hX2 0)
  have hpair : ∀ i j : ℕ, i ≠ j → ProbabilityTheory.IndepFun (X i) (X j) μ :=
    fun i j hij => hindepX.indepFun hij
  have hYint_eq : ∀ i : ℕ, ∫ ω, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ
      = (∫ ω, X 0 ω ∂μ) * ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ := by
    intro i
    have hXmeas : @Measurable Ω ℝ (⨆ k, MeasurableSpace.comap (X k) inferInstance)
        inferInstance (X i) :=
      measurable_iff_comap_le.mpr
        (le_iSup (fun k => MeasurableSpace.comap (X k) inferInstance) i)
    have hbridge := indepFun_N_bridge μ N X hindepN (X i)
      (fun n : ℕ => if i < n then (1 : ℝ) else (0 : ℝ)) hXmeas (hφmeas i)
    have hfact := indepFun_integral_mul_eq hbridge (hmeas i).aestronglyMeasurable
      ((hφmeas i).comp hN).aestronglyMeasurable
    have c1 : ∫ ω, X i ω * ((fun n : ℕ => if i < n then (1 : ℝ) else (0 : ℝ)) ∘ N) ω ∂μ
        = ∫ ω, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      simp only [Function.comp_apply]
    have c2 : ∫ ω, ((fun n : ℕ => if i < n then (1 : ℝ) else (0 : ℝ)) ∘ N) ω ∂μ
        = ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      simp only [Function.comp_apply]
    rw [c1, c2, hmean i] at hfact
    exact hfact
  have hYYint_eq : ∀ i j : ℕ, ∫ ω, (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
      (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ
      = (∫ ω, X i ω * X j ω ∂μ) * ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
        (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ := by
    intro i j
    have hXmeas_i : @Measurable Ω ℝ (⨆ k, MeasurableSpace.comap (X k) inferInstance)
        inferInstance (X i) :=
      measurable_iff_comap_le.mpr
        (le_iSup (fun k => MeasurableSpace.comap (X k) inferInstance) i)
    have hXmeas_j : @Measurable Ω ℝ (⨆ k, MeasurableSpace.comap (X k) inferInstance)
        inferInstance (X j) :=
      measurable_iff_comap_le.mpr
        (le_iSup (fun k => MeasurableSpace.comap (X k) inferInstance) j)
    have hGmeas : @Measurable Ω ℝ (⨆ k, MeasurableSpace.comap (X k) inferInstance)
        inferInstance (fun ω => X i ω * X j ω) :=
      hXmeas_i.mul hXmeas_j
    have hψmeas : Measurable (fun n : ℕ => (if i < n then (1 : ℝ) else (0 : ℝ)) *
        (if j < n then (1 : ℝ) else (0 : ℝ))) :=
      (hφmeas i).mul (hφmeas j)
    have hbridge := indepFun_N_bridge μ N X hindepN (fun ω => X i ω * X j ω)
      (fun n : ℕ => (if i < n then (1 : ℝ) else (0 : ℝ)) * (if j < n then (1 : ℝ) else (0 : ℝ)))
      hGmeas hψmeas
    have hfact := indepFun_integral_mul_eq hbridge (hXX_meas i j).aestronglyMeasurable
      ((hψmeas.comp hN).aestronglyMeasurable)
    have c1 : ∫ ω, (fun ω => X i ω * X j ω) ω *
        ((fun n : ℕ => (if i < n then (1 : ℝ) else (0 : ℝ)) *
          (if j < n then (1 : ℝ) else (0 : ℝ))) ∘ N) ω ∂μ
        = ∫ ω, (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
          (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      simp only [Function.comp_apply]
      ring
    have c3 : ∫ ω, ((fun n : ℕ => (if i < n then (1 : ℝ) else (0 : ℝ)) *
        (if j < n then (1 : ℝ) else (0 : ℝ))) ∘ N) ω ∂μ
        = ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
          (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      simp only [Function.comp_apply]
    rw [c1, c3] at hfact
    exact hfact
  have hXX_eq : ∀ i j : ℕ, ∫ ω, X i ω * X j ω ∂μ
      = (∫ ω, X 0 ω ∂μ) ^ 2 + (if i = j then ProbabilityTheory.variance (X 0) μ else 0) := by
    intro i j
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      have c : ∫ ω, X i ω * X j ω ∂μ = ∫ ω, (X j ω) ^ 2 ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro ω
        rw [hij]
        ring
      rw [c, hsq j, hVarX0]
      ring
    · rw [ite_eq_right hij]
      have hfact := indepFun_integral_mul_eq (hpair i j hij) (hmeas i).aestronglyMeasurable
        (hmeas j).aestronglyMeasurable
      rw [hmean i, hmean j] at hfact
      rw [hfact]
      ring
  have hAint_eq : ∫ ω, (N ω : ℝ) ∂μ
      = ∑ i ∈ Finset.range nmax, ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ := by
    have hexpand : ∫ ω, ∑ i ∈ Finset.range nmax, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ
        = ∑ i ∈ Finset.range nmax, ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ :=
      integral_finsetSum _ (fun i _ => haint i)
    have hcongr : ∫ ω, (N ω : ℝ) ∂μ
        = ∫ ω, ∑ i ∈ Finset.range nmax, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ :=
      integral_congr_ae hA_N.symm
    rw [hcongr, hexpand]
  have hF_expand : ∫ ω, ∑ i ∈ Finset.range nmax, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ
      = ∑ i ∈ Finset.range nmax, ∫ ω, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ :=
    integral_finsetSum _ (fun i _ => hYint i)
  have hF2int_eq : ∫ ω, (∑ i ∈ Finset.range nmax,
      X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) ^ 2 ∂μ
      = ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
        ∫ ω, (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
          (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ := by
    have hpoint : ∀ ω : Ω, (∑ i ∈ Finset.range nmax,
        X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) ^ 2
        = ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
          (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
          (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) := by
      intro ω
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    have hinner : ∀ i : ℕ, ∫ ω, ∑ j ∈ Finset.range nmax,
        (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
        (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ
        = ∑ j ∈ Finset.range nmax, ∫ ω, (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
          (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ :=
      fun i => integral_finsetSum _ (fun j _ => hYXYint i j)
    have hexpand : ∫ ω, ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
        (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
        (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ
        = ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
          ∫ ω, (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
            (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hYXYint i j))]
      simp only [hinner]
    have hcongr : ∫ ω, (∑ i ∈ Finset.range nmax,
        X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) ^ 2 ∂μ
        = ∫ ω, ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
          (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
          (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    rw [hcongr, hexpand]
  have hAAint_eq : ∫ ω, ((N ω : ℝ)) ^ 2 ∂μ
      = ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
        ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
          (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ := by
    have hAsq : (fun ω => (∑ i ∈ Finset.range nmax,
        (if i < N ω then (1 : ℝ) else (0 : ℝ))) ^ 2) =ᵐ[μ]
        (fun ω => ((N ω : ℝ)) ^ 2) := by
      filter_upwards [hA_N] with ω hω
      simp only [hω]
    have hpoint : ∀ ω : Ω, (∑ i ∈ Finset.range nmax, (if i < N ω then (1 : ℝ) else (0 : ℝ))) ^ 2
        = ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
          (if i < N ω then (1 : ℝ) else (0 : ℝ)) * (if j < N ω then (1 : ℝ) else (0 : ℝ)) := by
      intro ω
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    have hinner : ∀ i : ℕ, ∫ ω, ∑ j ∈ Finset.range nmax,
        (if i < N ω then (1 : ℝ) else (0 : ℝ)) * (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ
        = ∑ j ∈ Finset.range nmax, ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
          (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ :=
      fun i => integral_finsetSum _ (fun j _ => haaint i j)
    have hexpand : ∫ ω, ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
        (if i < N ω then (1 : ℝ) else (0 : ℝ)) * (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ
        = ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
          ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
            (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => haaint i j))]
      simp only [hinner]
    have hcongr : ∫ ω, (∑ i ∈ Finset.range nmax, (if i < N ω then (1 : ℝ) else (0 : ℝ))) ^ 2 ∂μ
        = ∫ ω, ((N ω : ℝ)) ^ 2 ∂μ :=
      integral_congr_ae hAsq
    have hcongr2 : ∫ ω, (∑ i ∈ Finset.range nmax, (if i < N ω then (1 : ℝ) else (0 : ℝ))) ^ 2 ∂μ
        = ∫ ω, ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
          (if i < N ω then (1 : ℝ) else (0 : ℝ)) * (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    rw [← hcongr, hcongr2, hexpand]
  have hterm : ∀ i j : ℕ, ∫ ω, (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
      (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ
      - (∫ ω, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
        (∫ ω, X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)
      = (∫ ω, X 0 ω ∂μ) ^ 2 * ((∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
          (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)
          - (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
            (∫ ω, (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ))
        + (if i = j then ProbabilityTheory.variance (X 0) μ *
          (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) * (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)
          else 0) := by
    intro i j
    rw [hYYint_eq i j, hYint_eq i, hYint_eq j, hXX_eq i j]
    split_ifs with hij <;> ring
  have hsum : ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
      (∫ ω, (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
        (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ
        - (∫ ω, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
          (∫ ω, X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ))
      = (∫ ω, X 0 ω ∂μ) ^ 2 * ProbabilityTheory.variance (fun ω => (N ω : ℝ)) μ
        + ProbabilityTheory.variance (X 0) μ * ∫ ω, (N ω : ℝ) ∂μ := by
    simp only [hterm]
    simp only [Finset.sum_add_distrib]
    have hA : ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
        (∫ ω, X 0 ω ∂μ) ^ 2 * ((∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
          (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)
          - (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
            (∫ ω, (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ))
        = (∫ ω, X 0 ω ∂μ) ^ 2 * (∫ ω, ((N ω : ℝ)) ^ 2 ∂μ - (∫ ω, (N ω : ℝ) ∂μ) ^ 2) := by
      have hQQ : ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
          ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) * (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ
          = ∫ ω, ((N ω : ℝ)) ^ 2 ∂μ :=
        hAAint_eq.symm
      have hPP : ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
          (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
          (∫ ω, (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)
          = (∫ ω, (N ω : ℝ) ∂μ) ^ 2 := by
        have h1 : ∀ i : ℕ, ∑ j ∈ Finset.range nmax,
            (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
            (∫ ω, (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)
            = (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
              ∑ j ∈ Finset.range nmax, ∫ ω, (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ :=
          fun i => by rw [Finset.mul_sum]
        simp only [h1]
        have h2 : ∑ i ∈ Finset.range nmax, (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
            ∑ j ∈ Finset.range nmax, ∫ ω, (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ
            = (∑ i ∈ Finset.range nmax, ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
              (∑ j ∈ Finset.range nmax, ∫ ω, (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) := by
          rw [Finset.sum_mul]
        rw [h2]
        simp only [← hAint_eq]
        ring
      simp only [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_sub_distrib]
      rw [hQQ, hPP]
    have hB : ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
        (if i = j then ProbabilityTheory.variance (X 0) μ *
          (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) * (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)
          else 0)
        = ProbabilityTheory.variance (X 0) μ * ∫ ω, (N ω : ℝ) ∂μ := by
      have hinner : ∀ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
          (if i = j then ProbabilityTheory.variance (X 0) μ *
            (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
              (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)
            else 0)
          = ProbabilityTheory.variance (X 0) μ *
            (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
              (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) := by
        intro i hi
        have h0 : ∀ b ∈ Finset.range nmax, b ≠ i →
            (if i = b then ProbabilityTheory.variance (X 0) μ *
              (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
                (if b < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)
              else (0 : ℝ)) = 0 := by
          intro b _ hb
          exact ite_eq_right (Ne.symm hb)
        have h1 : i ∉ Finset.range nmax →
            (if i = i then ProbabilityTheory.variance (X 0) μ *
              (∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
                (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)
              else (0 : ℝ)) = 0 :=
          fun hi' => absurd hi hi'
        have hsingle := Finset.sum_eq_single i h0 h1
        simpa using hsingle
      refine (Finset.sum_congr rfl hinner).trans ?_
      rw [← Finset.mul_sum]
      congr 1
      have haa : ∀ i : ℕ, ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) *
          (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ
          = ∫ ω, (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ := by
        intro i
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro ω
        by_cases h : i < N ω <;> simp [h]
      simp only [haa]
      exact hAint_eq.symm
    have hVN : ∫ ω, ((N ω : ℝ)) ^ 2 ∂μ - (∫ ω, (N ω : ℝ) ∂μ) ^ 2
        = ProbabilityTheory.variance (fun ω => (N ω : ℝ)) μ :=
      (ProbabilityTheory.variance_eq_sub hNmem).symm
    rw [hA, hB, hVN]
  have hVarF : ProbabilityTheory.variance
      (fun ω => ∑ i ∈ Finset.range nmax, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) μ
      = ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
        (∫ ω, (X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) *
          (X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ))) ∂μ
          - (∫ ω, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
            (∫ ω, X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ)) := by
    have hsub := ProbabilityTheory.variance_eq_sub hFmem
    have hsq_expand : (∑ i ∈ Finset.range nmax,
        ∫ ω, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) ^ 2
        = ∑ i ∈ Finset.range nmax, ∑ j ∈ Finset.range nmax,
          (∫ ω, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) *
          (∫ ω, X j ω * (if j < N ω then (1 : ℝ) else (0 : ℝ)) ∂μ) := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    simp only [hsub, Pi.pow_apply, hF2int_eq, hF_expand, hsq_expand,
      ← Finset.sum_sub_distrib]
  have hmain : ProbabilityTheory.variance
      (fun ω => ∑ i ∈ Finset.range nmax, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) μ
      = (∫ ω, X 0 ω ∂μ) ^ 2 * ProbabilityTheory.variance (fun ω => (N ω : ℝ)) μ
        + ProbabilityTheory.variance (X 0) μ * ∫ ω, (N ω : ℝ) ∂μ := by
    rw [hVarF, hsum]
  have hcongr : ProbabilityTheory.variance (fun ω => ∑ i ∈ Finset.range (N ω), X i ω) μ
      = ProbabilityTheory.variance
        (fun ω => ∑ i ∈ Finset.range nmax, X i ω * (if i < N ω then (1 : ℝ) else (0 : ℝ))) μ :=
    variance_congr_ae hF_S.symm
  rw [hcongr, hmain]
  ring
end MathlibExt.Probability.Finance.FiniteCollectiveVariance
