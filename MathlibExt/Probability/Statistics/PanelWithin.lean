/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Analysis.Matrix.MeasurableSpace

import Mathlib.Topology.Instances.Matrix

/-!
# Within (fixed-effects) estimator consistency

Static panel with strict exogeneity conditional on individual effects.
Balanced panel with finite nonempty periods `τ`, finite regressors `k`,
clusters indexed by `ℕ`. Cluster `i` has regressors `X i`, errors `u i`,
individual effect `c i` (time-invariant parts removed by within transform).

Main results:
* `centering` and `centering_mulVec_const`: time-demeaning eliminates effects.
* `withinGram`, `withinScore`, `withinEstimator`: within estimator.
* `withinEstimator_eq_add`: algebra decomposing estimator around truth.
* `tendsto_withinEstimator`: consistency under independent clusters.
* `integral_withinScore_eq_zero_of_uncorrelated`: strict exogeneity moments.
* `integral_mul_eq_zero_of_condExp`: conditional form gives moment form.

Asymptotic normality (needs PL4 error variance) and unbalanced panels are
not covered.

## References

* K. Schmidheiny, _Panel Data: Fixed and Random Effects_, Short Guides to
  Microeconometrics, University of Basel (2025), Sections 2 and 5.
* J. M. Wooldridge, _Econometric Analysis of Cross Section and Panel Data_,
  2nd ed., MIT Press (2010), Chapter 10.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.PanelWithin

open MeasureTheory ProbabilityTheory Topology Filter Matrix

/-- Time-demeaning matrix `Q = 1 - T⁻¹ • J`. -/
noncomputable def centering (τ : Type*) [Fintype τ] [DecidableEq τ] :
    Matrix τ τ ℝ :=
  1 - (Fintype.card τ : ℝ)⁻¹ • Matrix.of fun _ _ => 1

/-- Centering eliminates individual (constant) effects. -/
theorem centering_mulVec_const {τ : Type*} [Fintype τ] [DecidableEq τ]
    [Nonempty τ] (a : ℝ) : centering τ *ᵥ (fun _ => a) = 0 := by
  have hcard : (Fintype.card τ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hJ : ((Matrix.of fun _ _ => (1 : ℝ) : Matrix τ τ ℝ) *ᵥ
      (fun _ : τ => a) = fun _ : τ => (Fintype.card τ : ℝ) * a) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold centering
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hJ]
  have hsmul : (Fintype.card τ : ℝ)⁻¹ •
      (fun _ : τ => (Fintype.card τ : ℝ) * a) = (fun _ : τ => a) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [hsmul, sub_self]

/-- Within Gram matrix: sum of demeaned `X'X` over clusters. -/
noncomputable def withinGram {τ k Ω : Type*} [Fintype τ] [DecidableEq τ]
    (X : ℕ → Ω → Matrix τ k ℝ) (N : ℕ) (ω : Ω) : Matrix k k ℝ :=
  ∑ i ∈ Finset.range N, (centering τ * X i ω)ᵀ * (centering τ * X i ω)

/-- Within score vector: sum of demeaned `X'y` over clusters. -/
noncomputable def withinScore {τ k Ω : Type*} [Fintype τ] [DecidableEq τ]
    (X : ℕ → Ω → Matrix τ k ℝ) (v : ℕ → Ω → τ → ℝ) (N : ℕ)
    (ω : Ω) : k → ℝ :=
  ∑ i ∈ Finset.range N, (centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ v i ω)

/-- Within estimator via Mathlib matrix inverse. -/
noncomputable def withinEstimator {τ k Ω : Type*} [Fintype τ] [DecidableEq τ]
    [Fintype k] [DecidableEq k] (X : ℕ → Ω → Matrix τ k ℝ)
    (y : ℕ → Ω → τ → ℝ) (N : ℕ) (ω : Ω) : k → ℝ :=
  (withinGram X N ω)⁻¹ *ᵥ withinScore X y N ω

/-- `*ᵥ` distributes over sums of matrices. -/
private theorem sum_mulVec {ι k l : Type*} [Fintype l]
    (M : ι → Matrix k l ℝ) (v : l → ℝ) (s : Finset ι) :
    (∑ i ∈ s, M i) *ᵥ v = ∑ i ∈ s, M i *ᵥ v := by
  apply Matrix.sum_mulVec

/-- Within estimator equals truth plus noise term when Gram is a unit. -/
theorem withinEstimator_eq_add {τ k Ω : Type*} [Fintype τ] [DecidableEq τ]
    [Nonempty τ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → Matrix τ k ℝ} {y : ℕ → Ω → τ → ℝ} {c : ℕ → Ω → ℝ}
    {u : ℕ → Ω → τ → ℝ} {β : k → ℝ} {N : ℕ} {ω : Ω}
    (hy : ∀ i ω, y i ω = X i ω *ᵥ β + (fun _ => c i ω) + u i ω)
    (hG : IsUnit (withinGram X N ω).det) :
    withinEstimator X y N ω
      = β + (withinGram X N ω)⁻¹ *ᵥ withinScore X u N ω := by
  have hQy : ∀ i, centering τ *ᵥ y i ω
      = (centering τ * X i ω) *ᵥ β + centering τ *ᵥ u i ω := by
    intro i
    have hconst := centering_mulVec_const (τ := τ) (c i ω)
    rw [hy i ω, Matrix.mulVec_add, Matrix.mulVec_add, hconst, add_zero,
      Matrix.mulVec_mulVec]
  have hsum : ∀ i, (centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ y i ω)
      = ((centering τ * X i ω)ᵀ * (centering τ * X i ω)) *ᵥ β
        + (centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ u i ω) := by
    intro i
    rw [hQy i, Matrix.mulVec_add, Matrix.mulVec_mulVec]
  have hScore : withinScore X y N ω
      = (withinGram X N ω) *ᵥ β + withinScore X u N ω := by
    unfold withinScore withinGram
    have hcongr : (∑ i ∈ Finset.range N,
          (centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ y i ω))
        = ∑ i ∈ Finset.range N,
          (((centering τ * X i ω)ᵀ * (centering τ * X i ω)) *ᵥ β
            + (centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ u i ω)) :=
      Finset.sum_congr rfl (fun i _ => hsum i)
    rw [hcongr, Finset.sum_add_distrib, ← sum_mulVec]
  have hGG : (withinGram X N ω)⁻¹ * withinGram X N ω = 1 := by
    apply Matrix.nonsing_inv_mul
    exact hG
  unfold withinEstimator
  rw [hScore, Matrix.mulVec_add, Matrix.mulVec_mulVec, hGG,
    Matrix.one_mulVec]

/-- Scaling Gram and score by nonzero `c` preserves `G⁻¹ *ᵥ S`. -/
private theorem inv_smul_cancel {k : Type*} [Fintype k] [DecidableEq k]
    (G : Matrix k k ℝ) (S : k → ℝ) (c : ℝ) (_hc : c ≠ 0)
    (hG : IsUnit G.det) (hGc : IsUnit (c • G).det) :
    (c • G)⁻¹ *ᵥ (c • S) = G⁻¹ *ᵥ S := by
  have hGGinv : G * G⁻¹ = 1 := by
    apply Matrix.mul_nonsing_inv
    exact hG
  have h1 : (c • G) *ᵥ (G⁻¹ *ᵥ S) = c • S := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, hGGinv,
      Matrix.one_mulVec]
  have hGcInv : (c • G)⁻¹ * (c • G) = 1 := by
    apply Matrix.nonsing_inv_mul
    exact hGc
  have h2 : (c • G)⁻¹ *ᵥ ((c • G) *ᵥ (G⁻¹ *ᵥ S)) = G⁻¹ *ᵥ S := by
    rw [Matrix.mulVec_mulVec, hGcInv, Matrix.one_mulVec]
  rw [h1] at h2
  exact h2

/-- Convergent Gram with invertible limit gives `G⁻¹ *ᵥ S → 0`. -/
private theorem tendsto_inv_mulVec_zero {k : Type*} [Fintype k]
    [DecidableEq k] {G : ℕ → Matrix k k ℝ} {S : ℕ → k → ℝ}
    {G_lim : Matrix k k ℝ} (hG : Tendsto G atTop (𝓝 G_lim))
    (hS : Tendsto S atTop (𝓝 0)) (hlim : IsUnit G_lim.det) :
    (∀ᶠ N in atTop, IsUnit (G N).det)
      ∧ Tendsto (fun N => (G N)⁻¹ *ᵥ S N) atTop (𝓝 0) := by
  have hdet : Tendsto (fun N => (G N).det) atTop (𝓝 G_lim.det) :=
    ((continuous_id.matrix_det).tendsto _).comp hG
  have hlim_ne : G_lim.det ≠ 0 := isUnit_iff_ne_zero.mp hlim
  have hev_ne : ∀ᶠ N in atTop, (G N).det ≠ 0 :=
    hdet.eventually (eventually_ne_nhds hlim_ne)
  have hev_unit : ∀ᶠ N in atTop, IsUnit (G N).det :=
    hev_ne.mono fun N hN => isUnit_iff_ne_zero.mpr hN
  have hdet_inv : Tendsto (fun N => ((G N).det)⁻¹) atTop
      (𝓝 (G_lim.det)⁻¹) :=
    hdet.inv₀ hlim_ne
  have hring : Tendsto (fun N => Ring.inverse (G N).det) atTop
      (𝓝 (Ring.inverse G_lim.det)) := by
    simpa [Ring.inverse_eq_inv'] using hdet_inv
  have hadj : Tendsto (fun N => (G N).adjugate) atTop
      (𝓝 G_lim.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto _).comp hG
  have hinv : Tendsto (fun N => (G N)⁻¹) atTop (𝓝 G_lim⁻¹) := by
    simp only [Matrix.inv_def]
    exact hring.smul hadj
  have hmul : Tendsto (fun N => (G N)⁻¹ *ᵥ S N) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro j
    simp only [Matrix.mulVec, dotProduct]
    have h_each : ∀ l, Tendsto (fun N => (G N)⁻¹ j l * S N l) atTop
        (𝓝 ((G_lim⁻¹ j l) * 0)) := by
      intro l
      have hInv_jl : Tendsto (fun N => (G N)⁻¹ j l) atTop
          (𝓝 (G_lim⁻¹ j l)) :=
        (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hinv) j)) l
      have hS_l : Tendsto (fun N => S N l) atTop (𝓝 (0 : ℝ)) :=
        (tendsto_pi_nhds.mp hS) l
      exact hInv_jl.mul hS_l
    have hsum := tendsto_finsetSum Finset.univ (fun l _ => h_each l)
    have hsum0 : (∑ l ∈ Finset.univ, (G_lim⁻¹ j l) * 0) = 0 := by simp
    simpa [hsum0] using hsum
  exact ⟨hev_unit, hmul⟩

/-- Gram entry map is measurable in the joint cluster variable. -/
private theorem measurable_gram_entry {τ k : Type*} [Fintype τ]
    [DecidableEq τ] (j l : k) :
    Measurable (fun p : Matrix τ k ℝ × (τ → ℝ) =>
      ((centering τ * p.1)ᵀ * (centering τ * p.1)) j l) := by
  have hP1 : ∀ s a, Measurable
      (fun p : Matrix τ k ℝ × (τ → ℝ) => p.1 s a) :=
    fun s a => (measurable_pi_apply a).comp
      ((measurable_pi_apply s).comp measurable_fst)
  have hSum : Measurable (fun p : Matrix τ k ℝ × (τ → ℝ) =>
      ∑ t, (∑ s, p.1 s j * centering τ t s)
        * ∑ s, centering τ t s * p.1 s l) := by
    apply Finset.measurable_sum
    intro t _
    apply Measurable.mul
    · apply Finset.measurable_sum
      intro s _
      exact (hP1 s j).mul measurable_const
    · apply Finset.measurable_sum
      intro s _
      exact measurable_const.mul (hP1 s l)
  simpa [Matrix.mul_apply, Matrix.transpose_apply] using hSum

/-- Score entry map is measurable in the joint cluster variable. -/
private theorem measurable_score_entry {τ k : Type*} [Fintype τ]
    [DecidableEq τ] (j : k) :
    Measurable (fun p : Matrix τ k ℝ × (τ → ℝ) =>
      ((centering τ * p.1)ᵀ *ᵥ (centering τ *ᵥ p.2)) j) := by
  have hP1 : ∀ s a, Measurable
      (fun p : Matrix τ k ℝ × (τ → ℝ) => p.1 s a) :=
    fun s a => (measurable_pi_apply a).comp
      ((measurable_pi_apply s).comp measurable_fst)
  have hP2 : ∀ s, Measurable
      (fun p : Matrix τ k ℝ × (τ → ℝ) => p.2 s) :=
    fun s => (measurable_pi_apply s).comp measurable_snd
  have hQ1 : ∀ t s, Measurable
      (fun p : Matrix τ k ℝ × (τ → ℝ) =>
        centering τ t s * p.1 s j) :=
    fun t s => measurable_const.mul (hP1 s j)
  have hQ2 : ∀ t s, Measurable
      (fun p : Matrix τ k ℝ × (τ → ℝ) =>
        centering τ t s * p.2 s) :=
    fun t s => measurable_const.mul (hP2 s)
  have hA : ∀ t, Measurable
      (fun p : Matrix τ k ℝ × (τ → ℝ) =>
        ∑ s, centering τ t s * p.1 s j) := by
    intro t
    measurability
  have hW : ∀ t, Measurable
      (fun p : Matrix τ k ℝ × (τ → ℝ) =>
        ∑ s, centering τ t s * p.2 s) := by
    intro t
    measurability
  have hProd : ∀ t, Measurable
      (fun p : Matrix τ k ℝ × (τ → ℝ) =>
        (∑ s, centering τ t s * p.1 s j)
          * (∑ s, centering τ t s * p.2 s)) := by
    intro t
    exact (hA t).mul (hW t)
  have hSum : Measurable
      (fun p : Matrix τ k ℝ × (τ → ℝ) => ∑ t,
        (∑ s, centering τ t s * p.1 s j)
          * (∑ s, centering τ t s * p.2 s)) := by
    measurability
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply] using hSum

/-- Consistency of the within estimator under independent clusters. -/
theorem tendsto_withinEstimator {τ k Ω : Type*} [Fintype τ] [DecidableEq τ]
    [Nonempty τ] [Fintype k] [DecidableEq k] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → Matrix τ k ℝ} {y : ℕ → Ω → τ → ℝ} {c : ℕ → Ω → ℝ}
    {u : ℕ → Ω → τ → ℝ} {β : k → ℝ}
    (hy : ∀ i ω, y i ω = X i ω *ᵥ β + (fun _ => c i ω) + u i ω)
    (hmeas : ∀ i, Measurable fun ω => (X i ω, u i ω))
    (hindep : Pairwise fun i j =>
      IndepFun (fun ω => (X i ω, u i ω)) (fun ω => (X j ω, u j ω)) P)
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, u i ω))
      (fun ω => (X 0 ω, u 0 ω)) P P)
    (hintG : ∀ j l, Integrable
      (fun ω => ((centering τ * X 0 ω)ᵀ * (centering τ * X 0 ω)) j l) P)
    (hintS : ∀ j, Integrable
      (fun ω => ((centering τ * X 0 ω)ᵀ *ᵥ (centering τ *ᵥ u 0 ω)) j) P)
    (hlim : IsUnit (Matrix.of fun j l =>
      ∫ ω, ((centering τ * X 0 ω)ᵀ * (centering τ * X 0 ω)) j l ∂P).det)
    (hEE : ∀ j, ∫ ω,
      ((centering τ * X 0 ω)ᵀ *ᵥ (centering τ *ᵥ u 0 ω)) j ∂P = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun N => withinEstimator X y N ω) atTop (𝓝 β) := by
  have hG_meas : ∀ j l, Measurable (fun p : Matrix τ k ℝ × (τ → ℝ) =>
      ((centering τ * p.1)ᵀ * (centering τ * p.1)) j l) :=
    fun j l => measurable_gram_entry j l
  have hS_meas : ∀ j, Measurable (fun p : Matrix τ k ℝ × (τ → ℝ) =>
      ((centering τ * p.1)ᵀ *ᵥ (centering τ *ᵥ p.2)) j) :=
    fun j => measurable_score_entry j
  have hintG' : ∀ j l, Integrable
      (fun ω => ((centering τ * X 0 ω)ᵀ * (centering τ * X 0 ω)) j l) P :=
    fun j l =>
      ⟨((hG_meas j l).comp (hmeas 0)).aestronglyMeasurable,
        (hintG j l).hasFiniteIntegral⟩
  have hintS' : ∀ j, Integrable
      (fun ω => ((centering τ * X 0 ω)ᵀ *ᵥ (centering τ *ᵥ u 0 ω)) j) P :=
    fun j =>
      ⟨((hS_meas j).comp (hmeas 0)).aestronglyMeasurable,
        (hintS j).hasFiniteIntegral⟩
  have hindepG : ∀ j l, Pairwise fun i i' => IndepFun
      (fun ω => ((centering τ * X i ω)ᵀ * (centering τ * X i ω)) j l)
      (fun ω => ((centering τ * X i' ω)ᵀ * (centering τ * X i' ω)) j l)
      P := by
    intro j l i i' hij
    exact (hindep hij).comp (hG_meas j l) (hG_meas j l)
  have hidentG : ∀ j l i, IdentDistrib
      (fun ω => ((centering τ * X i ω)ᵀ * (centering τ * X i ω)) j l)
      (fun ω => ((centering τ * X 0 ω)ᵀ * (centering τ * X 0 ω)) j l)
      P P := by
    intro j l i
    exact (hident i).comp (hG_meas j l)
  have hindepS : ∀ j, Pairwise fun i i' => IndepFun
      (fun ω => ((centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ u i ω)) j)
      (fun ω => ((centering τ * X i' ω)ᵀ *ᵥ (centering τ *ᵥ u i' ω)) j)
      P := by
    intro j i i' hij
    exact (hindep hij).comp (hS_meas j) (hS_meas j)
  have hidentS : ∀ j i, IdentDistrib
      (fun ω => ((centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ u i ω)) j)
      (fun ω => ((centering τ * X 0 ω)ᵀ *ᵥ (centering τ *ᵥ u 0 ω)) j)
      P P := by
    intro j i
    exact (hident i).comp (hS_meas j)
  have hsllnG : ∀ j l, ∀ᵐ ω ∂P, Tendsto
      (fun N => (∑ i ∈ Finset.range N,
        ((centering τ * X i ω)ᵀ * (centering τ * X i ω)) j l) / (N : ℝ))
      atTop (𝓝 (∫ ω,
        ((centering τ * X 0 ω)ᵀ * (centering τ * X 0 ω)) j l ∂P)) :=
    fun j l =>
      ProbabilityTheory.strong_law_ae_real
        (fun i ω => ((centering τ * X i ω)ᵀ * (centering τ * X i ω)) j l)
        (hintG' j l) (hindepG j l) (hidentG j l)
  have hsllnS : ∀ j, ∀ᵐ ω ∂P, Tendsto
      (fun N => (∑ i ∈ Finset.range N,
        ((centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ u i ω)) j) / (N : ℝ))
      atTop (𝓝 (∫ ω,
        ((centering τ * X 0 ω)ᵀ *ᵥ (centering τ *ᵥ u 0 ω)) j ∂P)) :=
    fun j =>
      ProbabilityTheory.strong_law_ae_real
        (fun i ω => ((centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ u i ω)) j)
        (hintS' j) (hindepS j) (hidentS j)
  have hallG : ∀ᵐ ω ∂P, ∀ j l, Tendsto
      (fun N => (∑ i ∈ Finset.range N,
        ((centering τ * X i ω)ᵀ * (centering τ * X i ω)) j l) / (N : ℝ))
      atTop (𝓝 (∫ ω,
        ((centering τ * X 0 ω)ᵀ * (centering τ * X 0 ω)) j l ∂P)) := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro l
    exact hsllnG j l
  have hallS : ∀ᵐ ω ∂P, ∀ j, Tendsto
      (fun N => (∑ i ∈ Finset.range N,
        ((centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ u i ω)) j) / (N : ℝ))
      atTop (𝓝 (∫ ω,
        ((centering τ * X 0 ω)ᵀ *ᵥ (centering τ *ᵥ u 0 ω)) j ∂P)) := by
    rw [ae_all_iff]
    intro j
    exact hsllnS j
  have hall := hallG.and hallS
  refine hall.mono fun ω hω => ?_
  obtain ⟨hGconv, hSconv⟩ := hω
  have hSconv0 : ∀ j, Tendsto
      (fun N => (∑ i ∈ Finset.range N,
        ((centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ u i ω)) j) / (N : ℝ))
      atTop (𝓝 0) := by
    intro j
    have h := hSconv j
    rw [hEE j] at h
    exact h
  have hGram_entry : ∀ (N : ℕ) (j l : k),
      (withinGram X N ω) j l = ∑ i ∈ Finset.range N,
        ((centering τ * X i ω)ᵀ * (centering τ * X i ω)) j l := by
    intro N j l
    simp only [withinGram, Matrix.sum_apply]
  have hScore_entry : ∀ (N : ℕ) (j : k),
      (withinScore X u N ω) j = ∑ i ∈ Finset.range N,
        ((centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ u i ω)) j := by
    intro N j
    simp [withinScore]
  have hG_tendsto : Tendsto
      (fun (N : ℕ) => (N : ℝ)⁻¹ • withinGram X N ω) atTop
      (𝓝 (Matrix.of fun j l => ∫ ω,
        ((centering τ * X 0 ω)ᵀ * (centering τ * X 0 ω)) j l ∂P)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_pi_nhds.mpr
    intro l
    have hconv := hGconv j l
    have heq : (fun (N : ℕ) => ((N : ℝ)⁻¹ • withinGram X N ω) j l)
        = (fun (N : ℕ) => (∑ i ∈ Finset.range N,
          ((centering τ * X i ω)ᵀ * (centering τ * X i ω)) j l)
          / (N : ℝ)) := by
      funext N
      rw [Matrix.smul_apply, hGram_entry N j l, smul_eq_mul, div_eq_mul_inv,
        mul_comm]
    have hlim_eq : (Matrix.of fun j l => ∫ ω,
          ((centering τ * X 0 ω)ᵀ * (centering τ * X 0 ω)) j l ∂P) j l
        = ∫ ω, ((centering τ * X 0 ω)ᵀ * (centering τ * X 0 ω)) j l ∂P :=
      rfl
    rw [heq, hlim_eq]
    exact hconv
  have hS_tendsto : Tendsto
      (fun (N : ℕ) => (N : ℝ)⁻¹ • withinScore X u N ω) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro j
    have hconv := hSconv0 j
    have heq : (fun (N : ℕ) => ((N : ℝ)⁻¹ • withinScore X u N ω) j)
        = (fun (N : ℕ) => (∑ i ∈ Finset.range N,
          ((centering τ * X i ω)ᵀ *ᵥ (centering τ *ᵥ u i ω)) j)
          / (N : ℝ)) := by
      funext N
      simp only [Pi.smul_apply, smul_eq_mul, hScore_entry N j,
        div_eq_mul_inv, mul_comm]
    rw [heq]
    exact hconv
  obtain ⟨hev_Gunit, hscaled⟩ :=
    tendsto_inv_mulVec_zero hG_tendsto hS_tendsto hlim
  have hev_Nne : ∀ᶠ (N : ℕ) in atTop, N ≠ 0 := eventually_ne_atTop 0
  have hev_raw : ∀ᶠ (N : ℕ) in atTop, IsUnit (withinGram X N ω).det := by
    filter_upwards [hev_Gunit, hev_Nne] with N hGunit hNne
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNne
    have hc_ne : (N : ℝ)⁻¹ ≠ 0 := inv_ne_zero hNR
    have hdet_eq : ((N : ℝ)⁻¹ • withinGram X N ω).det
        = (N : ℝ)⁻¹ ^ Fintype.card k * (withinGram X N ω).det := by
      simp only [Matrix.det_smul]
    have hdetG_ne : ((N : ℝ)⁻¹ • withinGram X N ω).det ≠ 0 :=
      isUnit_iff_ne_zero.mp hGunit
    have hpow_ne : (N : ℝ)⁻¹ ^ Fintype.card k ≠ 0 :=
      pow_ne_zero _ hc_ne
    have hraw_ne : (withinGram X N ω).det ≠ 0 := by
      intro h0
      rw [hdet_eq, h0, mul_zero] at hdetG_ne
      exact hdetG_ne rfl
    exact isUnit_iff_ne_zero.mpr hraw_ne
  have hev_eq : ∀ᶠ (N : ℕ) in atTop,
      ((N : ℝ)⁻¹ • withinGram X N ω)⁻¹ *ᵥ ((N : ℝ)⁻¹ • withinScore X u N ω)
        = (withinGram X N ω)⁻¹ *ᵥ withinScore X u N ω := by
    filter_upwards [hev_raw, hev_Gunit, hev_Nne] with N hraw hGunit hNne
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNne
    have hc_ne : (N : ℝ)⁻¹ ≠ 0 := inv_ne_zero hNR
    exact inv_smul_cancel _ _ _ hc_ne hraw hGunit
  have hev_est : ∀ᶠ (N : ℕ) in atTop, withinEstimator X y N ω
      = β + (withinGram X N ω)⁻¹ *ᵥ withinScore X u N ω := by
    filter_upwards [hev_raw] with N hraw
    exact withinEstimator_eq_add hy hraw
  have hev_est2 : (fun (N : ℕ) => β + ((N : ℝ)⁻¹ • withinGram X N ω)⁻¹ *ᵥ
          ((N : ℝ)⁻¹ • withinScore X u N ω))
        =ᶠ[atTop] fun N => withinEstimator X y N ω := by
    filter_upwards [hev_est, hev_eq] with N h1 h2
    show β + ((N : ℝ)⁻¹ • withinGram X N ω)⁻¹ *ᵥ
        ((N : ℝ)⁻¹ • withinScore X u N ω) = withinEstimator X y N ω
    rw [h2, ← h1]
  have hlim_add : Tendsto
      (fun (N : ℕ) => β + ((N : ℝ)⁻¹ • withinGram X N ω)⁻¹ *ᵥ
        ((N : ℝ)⁻¹ • withinScore X u N ω)) atTop (𝓝 β) := by
    have hlim0 : Tendsto
        (fun (N : ℕ) => β + ((N : ℝ)⁻¹ • withinGram X N ω)⁻¹ *ᵥ
          ((N : ℝ)⁻¹ • withinScore X u N ω)) atTop (𝓝 (β + 0)) :=
      tendsto_const_nhds.add hscaled
    simpa [add_zero] using hlim0
  exact Tendsto.congr' hev_est2 hlim_add

/-- Strict exogeneity in moment form gives the estimating equation. -/
theorem integral_withinScore_eq_zero_of_uncorrelated {τ k Ω : Type*}
    [Fintype τ] [DecidableEq τ] [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → Matrix τ k ℝ} {u : ℕ → Ω → τ → ℝ}
    (hint : ∀ r s j, Integrable (fun ω => X 0 ω r j * u 0 ω s) P)
    (hzero : ∀ r s j, ∫ ω, X 0 ω r j * u 0 ω s ∂P = 0) :
    ∀ j, ∫ ω, ((centering τ * X 0 ω)ᵀ *ᵥ (centering τ *ᵥ u 0 ω)) j ∂P
      = 0 := by
  intro j
  have hpoint : ∀ ω, ((centering τ * X 0 ω)ᵀ *ᵥ (centering τ *ᵥ u 0 ω)) j
      = ∑ r, ∑ t, ∑ s, centering τ r t * centering τ r s
        * (X 0 ω t j * u 0 ω s) := by
    intro ω
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hint_c : ∀ r t s, Integrable
      (fun ω => centering τ r t * centering τ r s
        * (X 0 ω t j * u 0 ω s)) P :=
    fun r t s => (hint t s j).const_mul _
  have hint_s : ∀ r t, Integrable
      (fun ω => ∑ s, centering τ r t * centering τ r s
        * (X 0 ω t j * u 0 ω s)) P := by
    intro r t
    apply integrable_finsetSum
    intro s _
    exact hint_c r t s
  have hint_t : ∀ r, Integrable
      (fun ω => ∑ t, ∑ s, centering τ r t * centering τ r s
        * (X 0 ω t j * u 0 ω s)) P := by
    intro r
    apply integrable_finsetSum
    intro t _
    exact hint_s r t
  have hint_r : Integrable
      (fun ω => ∑ r, ∑ t, ∑ s, centering τ r t * centering τ r s
        * (X 0 ω t j * u 0 ω s)) P := by
    apply integrable_finsetSum
    intro r _
    exact hint_t r
  have hInt_r : ∫ ω, (∑ r, ∑ t, ∑ s, centering τ r t * centering τ r s
      * (X 0 ω t j * u 0 ω s)) ∂P
      = ∑ r, ∫ ω, (∑ t, ∑ s, centering τ r t * centering τ r s
        * (X 0 ω t j * u 0 ω s)) ∂P := by
    apply integral_finsetSum
    intro r _
    exact hint_t r
  have hInt_t : ∀ r, ∫ ω, (∑ t, ∑ s, centering τ r t * centering τ r s
      * (X 0 ω t j * u 0 ω s)) ∂P
      = ∑ t, ∫ ω, (∑ s, centering τ r t * centering τ r s
        * (X 0 ω t j * u 0 ω s)) ∂P := by
    intro r
    apply integral_finsetSum
    intro t _
    exact hint_s r t
  have hInt_s : ∀ r t, ∫ ω, (∑ s, centering τ r t * centering τ r s
      * (X 0 ω t j * u 0 ω s)) ∂P
      = ∑ s, centering τ r t * centering τ r s
        * (∫ ω, X 0 ω t j * u 0 ω s ∂P) := by
    intro r t
    have h1 : ∫ ω, (∑ s, centering τ r t * centering τ r s
        * (X 0 ω t j * u 0 ω s)) ∂P
        = ∑ s, ∫ ω, centering τ r t * centering τ r s
          * (X 0 ω t j * u 0 ω s) ∂P := by
      apply integral_finsetSum
      intro s _
      exact hint_c r t s
    rw [h1]
    apply Finset.sum_congr rfl
    intro s _
    rw [integral_const_mul]
  have hEq : (fun ω => ((centering τ * X 0 ω)ᵀ *ᵥ
      (centering τ *ᵥ u 0 ω)) j)
      = (fun ω => ∑ r, ∑ t, ∑ s, centering τ r t * centering τ r s
        * (X 0 ω t j * u 0 ω s)) :=
    funext hpoint
  rw [hEq, hInt_r]
  apply Finset.sum_eq_zero
  intro r _
  rw [hInt_t r]
  apply Finset.sum_eq_zero
  intro t _
  rw [hInt_s r t]
  apply Finset.sum_eq_zero
  intro s _
  rw [hzero t s j, mul_zero]

/-- Conditional strict exogeneity gives the uncorrelated moment form.

Conditioning on `X_i` alone suffices: the source condition
`E[u_it | X_i, z_i, c_i] = 0` implies it by the tower property. -/
theorem integral_mul_eq_zero_of_condExp {τ k Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : ℕ → Ω → Matrix τ k ℝ} {u : ℕ → Ω → τ → ℝ} {r s : τ} {j : k}
    (hX : Measurable (X 0))
    (hcond : P[fun ω => u 0 ω s
      | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P] 0)
    (hint_u : Integrable (fun ω => u 0 ω s) P)
    (hint_mul : Integrable (fun ω => X 0 ω r j * u 0 ω s) P) :
    ∫ ω, X 0 ω r j * u 0 ω s ∂P = 0 := by
  have hm_le : MeasurableSpace.comap (X 0) inferInstance ≤
      (inferInstance : MeasurableSpace Ω) :=
    hX.comap_le
  have hInt_eq : ∫ ω, P[fun ω => X 0 ω r j * u 0 ω s
      | MeasurableSpace.comap (X 0) inferInstance] ω ∂P
      = ∫ ω, X 0 ω r j * u 0 ω s ∂P := by
    apply MeasureTheory.integral_condExp
    all_goals assumption
  have hproj : Measurable (fun M : Matrix τ k ℝ => M r j) := by
    fun_prop
  have hg_m : AEStronglyMeasurable (m := MeasurableSpace.comap (X 0) inferInstance)
      (fun ω => X 0 ω r j) P :=
    (hproj.comp (comap_measurable (X 0))).aestronglyMeasurable
  have hpull : P[fun ω => X 0 ω r j * u 0 ω s
      | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun ω => X 0 ω r j * P[fun ω => u 0 ω s
        | MeasurableSpace.comap (X 0) inferInstance] ω := by
    apply MeasureTheory.condExp_mul_of_aestronglyMeasurable_left hg_m
    all_goals assumption
  have hzero_ae : (fun ω => X 0 ω r j * P[fun ω => u 0 ω s
      | MeasurableSpace.comap (X 0) inferInstance] ω) =ᵐ[P] 0 := by
    filter_upwards [hcond] with ω hω
    simp [hω]
  have h1 : ∫ ω, X 0 ω r j * u 0 ω s ∂P
      = ∫ ω, P[fun ω => X 0 ω r j * u 0 ω s
        | MeasurableSpace.comap (X 0) inferInstance] ω ∂P :=
    hInt_eq.symm
  have h2 : ∫ ω, P[fun ω => X 0 ω r j * u 0 ω s
      | MeasurableSpace.comap (X 0) inferInstance] ω ∂P
      = ∫ ω, X 0 ω r j * P[fun ω => u 0 ω s
        | MeasurableSpace.comap (X 0) inferInstance] ω ∂P :=
    integral_congr_ae hpull
  have h3 : ∫ ω, X 0 ω r j * P[fun ω => u 0 ω s
      | MeasurableSpace.comap (X 0) inferInstance] ω ∂P
      = ∫ ω, (0 : Ω → ℝ) ω ∂P :=
    integral_congr_ae hzero_ae
  rw [h1, h2, h3]
  simp

end MathlibExt.Probability.Statistics.PanelWithin

end
