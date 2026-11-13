/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Bootstrap
public import MathlibExt.Probability.Statistics.Survival.KaplanMeier

/-!
# Bootstrap validity for the Kaplan–Meier estimator on a finite grid

Fix a finite grid of times `t₀ < t₁ < ⋯ < t_{k-1}` and observations `o = (T, δ) ∈ ℝ × ℝ` whose
observed time `T` lies on the grid (`δ = 1` marks an observed death, any other value a
censoring). The Kaplan–Meier estimate of the first `n` observations at the grid is
`kmGrid ht y n j = Ŝₙ(tⱼ)`, computed by `CensoredData.kmSurvival` from the grouped data
`gridData ht y n` (deaths and censorings counted at each grid time).

**The bootstrap procedure.** Given the data `x`, draw a resample `ω n 0, …, ω n (n - 1)` iid
from the empirical law of `x 0, …, x (n - 1)` (the row `ω n` of `ProbabilityTheory.Bootstrap.world
x`), and recompute the Kaplan–Meier estimate on it: `Ŝ*ₙ = kmGrid ht (ω n) n`. Laws under
`world x` are conditional laws given the data.

## Main results

* `kmGrid_eq_kmMap`: on the grid, `Ŝₙ(tⱼ) = ∏_{l ≤ j} (1 - D̄ₙ(l) / Ȳₙ(l))` is a fixed function
  `kmMap` of the sample mean of the indicator vectors `obsVec t o`, with
  `D̄ₙ(l) = (1 / n) #{i < n : xᵢ = (t_l, 1)}` and `Ȳₙ(l) = (1 / n) #{i < n : t_l ≤ Tᵢ}`.
* `hasStrictFDerivAt_kmMap`: `kmMap` is strictly differentiable wherever every at-risk
  coordinate is nonzero.
* `tendstoInDistribution_bootstrap_kmGrid`: **bootstrap validity for fixed data**: under the
  conditions of the bootstrap delta method for the indicator means, conditionally on the data,
  `√n (Ŝ*ₙ - Ŝₙ) ⇒ L Z` with `L = fderiv kmMap θ`.
* `kmGrid_bootstrap_consistent`: for iid observations, `√n (Ŝₙ - S) ⇒ L Z` (with
  `S = kmMap θ`, `θ` the mean indicator vector) and, for almost every data sequence, the
  conditional law of `√n (Ŝ*ₙ - Ŝₙ)` has the same limit.
* `ae_tendstoInDistribution_bootstrap_kmGrid_of_limit`: taking the Kaplan–Meier limit as a
  hypothesis, `√n (Ŝₙ - S) ⇒ W`, the bootstrap law converges to the law of `W` almost surely.

## Scope

* Fixed finite grid that contains every observed time; continuous-time (process-level)
  Kaplan–Meier and grids depending on `n` are out of scope.
* Every at-risk probability `P(T ≥ tⱼ)` must be positive (`hpos`). At a grid point beyond the
  support (no mass at or after it) `kmMap` is not even continuous, and no bootstrap validity is
  claimed there; the test file exhibits the discontinuity.
* Observation times are positive (`ht0`): the bootstrap world's unused row zero is the point
  mass at `0 ∈ ℝ × ℝ`, and the indicator encoding must send it to `0`.

## References

* B. Efron, *Censored data and the bootstrap*, J. Amer. Statist. Assoc. 76 (1981), 312–319.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Chapter 23 (bootstrap delta method).
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal RealInnerProductSpace
open MathlibExt.Probability.Statistics.KaplanMeier ProbabilityTheory.Bootstrap

namespace MathlibExt.Probability.Statistics.KMBootstrap

variable {k : ℕ}

/-- The coordinate space of the indicator encoding: coordinate `Sum.inl j` is the death
indicator at `t j`, coordinate `Sum.inr j` the at-risk indicator at `t j`. -/
abbrev Coord (k : ℕ) := EuclideanSpace ℝ (Fin k ⊕ Fin k)

open Classical in
/-- The indicator encoding of one observation `o = (T, δ)` on the grid `t`:
`𝟙{o = (t j, 1)}` (death at `t j`) and `𝟙{t j ≤ T}` (at risk at `t j`). -/
noncomputable def obsVec (t : Fin k → ℝ) (o : ℝ × ℝ) : Coord k :=
  WithLp.toLp 2 (Sum.elim (fun j => if o = (t j, 1) then 1 else 0)
    (fun j => if t j ≤ o.1 then 1 else 0))

/-- The grid Kaplan–Meier map: `kmMap m j = ∏_{l ≤ j} (1 - m (inl l) / m (inr l))`. -/
noncomputable def kmMap (m : Coord k) : Fin k → ℝ :=
  fun j => ∏ l with l ≤ j, (1 - m (Sum.inl l) / m (Sum.inr l))

open Classical in
/-- The first `n` observations `y 0, …, y (n - 1)`, grouped at the grid `t`: `deaths j` counts
observations equal to `(t j, 1)`, `censored j` the other observations with time `t j`. -/
noncomputable def gridData {t : Fin k → ℝ} (ht : StrictMono t) (y : ℕ → ℝ × ℝ) (n : ℕ) :
    CensoredData k where
  time := t
  strictMono_time := ht
  deaths j := #{i ∈ range n | y i = (t j, 1)}
  censored j := #{i ∈ range n | (y i).1 = t j ∧ y i ≠ (t j, 1)}

/-- The **Kaplan–Meier estimate on the grid** of the first `n` observations:
`kmGrid ht y n j = Ŝₙ(t j)`. -/
noncomputable def kmGrid {t : Fin k → ℝ} (ht : StrictMono t) (y : ℕ → ℝ × ℝ) (n : ℕ) :
    Fin k → ℝ :=
  fun j => (gridData ht y n).kmSurvival (t j)

@[simp]
theorem obsVec_inl (t : Fin k → ℝ) (o : ℝ × ℝ) (j : Fin k) [Decidable (o = (t j, 1))] :
    obsVec t o (Sum.inl j) = if o = (t j, 1) then 1 else 0 := by
  simp only [obsVec, PiLp.toLp_apply, Sum.elim_inl]
  congr

@[simp]
theorem obsVec_inr (t : Fin k → ℝ) (o : ℝ × ℝ) (j : Fin k) [Decidable (t j ≤ o.1)] :
    obsVec t o (Sum.inr j) = if t j ≤ o.1 then 1 else 0 := by
  simp only [obsVec, PiLp.toLp_apply, Sum.elim_inr]
  congr

/-- For positive grid times the encoding sends `0` to `0`. -/
theorem obsVec_zero {t : Fin k → ℝ} (ht0 : ∀ j, 0 < t j) : obsVec t 0 = 0 := by
  classical
  ext i
  rcases i with j | j
  · simp [Prod.ext_iff]
  · simp [not_le.2 (ht0 j)]

theorem measurable_obsVec (t : Fin k → ℝ) : Measurable (obsVec t) := by
  classical
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun i => ?_)
  rcases i with j | j
  · exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const
  · exact Measurable.ite (measurableSet_le measurable_const measurable_fst) measurable_const
      measurable_const

theorem measurable_kmMap : Measurable (kmMap (k := k)) := by
  refine measurable_pi_iff.2 fun j => Finset.measurable_prod _ fun l _ => ?_
  exact measurable_const.sub ((PiLp.continuous_apply 2 _ _).measurable.div
    (PiLp.continuous_apply 2 _ _).measurable)

/-- Every encoded coordinate is `0` or `1`, so the encoding is bounded. -/
theorem norm_obsVec_le (t : Fin k → ℝ) (o : ℝ × ℝ) :
    ‖obsVec t o‖ ≤ √(∑ _i : Fin k ⊕ Fin k, (1 : ℝ)) := by
  classical
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rcases i with j | j <;> simp only [obsVec_inl, obsVec_inr] <;> split_ifs <;> norm_num

/-- **Kaplan–Meier is strictly differentiable in the indicator means** wherever every at-risk
coordinate is nonzero. -/
theorem hasStrictFDerivAt_kmMap {θ : Coord k} (hpos : ∀ j, θ (Sum.inr j) ≠ 0) :
    HasStrictFDerivAt kmMap (fderiv ℝ kmMap θ) θ := by
  have hc : ∀ i : Fin k ⊕ Fin k, ContDiff ℝ 1 fun m : Coord k => m i := fun i => by
    convert (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff using 1
    funext m
    rfl
  have h : ContDiffAt ℝ 1 kmMap θ := contDiffAt_pi.2 fun j => contDiffAt_prod fun l _ =>
    contDiffAt_const.sub (((hc _).contDiffAt).div (hc _).contDiffAt (hpos l))
  exact h.hasStrictFDerivAt one_ne_zero

section Bridge

variable {t : Fin k → ℝ} (ht : StrictMono t)

theorem sampleMeanVec_apply (y : ℕ → ℝ × ℝ) (n : ℕ) (i : Fin k ⊕ Fin k) :
    sampleMeanVec (fun i => obsVec t (y i)) n i = (n : ℝ)⁻¹ * ∑ m ∈ range n, obsVec t (y m) i := by
  simp [sampleMeanVec]

theorem cast_deaths (y : ℕ → ℝ × ℝ) (n : ℕ) (j : Fin k) :
    ((gridData ht y n).deaths j : ℝ) = ∑ m ∈ range n, obsVec t (y m) (Sum.inl j) := by
  classical
  simp only [gridData, Finset.natCast_card_filter, obsVec_inl]

theorem cast_atRisk (y : ℕ → ℝ × ℝ) (n : ℕ) (hgrid : ∀ i < n, (y i).1 ∈ Set.range t)
    (j : Fin k) :
    ((gridData ht y n).atRisk j : ℝ) = ∑ m ∈ range n, obsVec t (y m) (Sum.inr j) := by
  classical
  have hdc : ∀ l, ((gridData ht y n).deaths l + (gridData ht y n).censored l : ℝ) =
      ∑ m ∈ range n, if (y m).1 = t l then 1 else 0 := fun l => by
    simp only [gridData, Finset.natCast_card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h1 : y m = (t l, 1)
    · simp [h1]
    · by_cases h2 : (y m).1 = t l <;> simp [h1, h2]
  simp only [CensoredData.atRisk, Nat.cast_sum, Nat.cast_add, hdc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨p, hp⟩ := hgrid m (Finset.mem_range.1 hm)
  simp only [obsVec_inr, ← hp, ht.le_iff_le, ht.injective.eq_iff]
  rw [Finset.sum_ite_eq]
  simp

/-- **Kaplan–Meier on the grid is a smooth function of the indicator mean.** If the first `n`
observed times lie on the grid, then `Ŝₙ(tⱼ) = kmMap (x̄ₙ) j` with `x̄ₙ` the mean of the
encoded observations. -/
theorem kmGrid_eq_kmMap (y : ℕ → ℝ × ℝ) (n : ℕ) (hgrid : ∀ i < n, (y i).1 ∈ Set.range t) :
    kmGrid ht y n = kmMap (sampleMeanVec (fun i => obsVec t (y i)) n) := by
  classical
  funext j
  simp only [kmGrid, CensoredData.kmSurvival, kmMap, sampleMeanVec_apply]
  rw [Finset.filter_congr (q := fun l => l ≤ j) fun l _ => by
    simp only [gridData, ht.le_iff_le]]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [CensoredData.kmFactor, cast_deaths ht, cast_atRisk ht y n hgrid]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [mul_div_mul_left _ _ (inv_ne_zero (Nat.cast_ne_zero.2 hn))]

end Bridge

section Resample

variable {α : Type*} [MeasurableSpace α] [Zero α]

/-- Almost surely under the bootstrap world, every draw of the size-`n` resample lies in any
measurable set containing the first `n` data points. -/
theorem ae_resample_mem (x : ℕ → α) {S : Set α} (hS : MeasurableSet S) {n : ℕ}
    (hx : ∀ i < n, x i ∈ S) : ∀ᵐ ω ∂world x, ∀ i < n, ω n i ∈ S := by
  rw [ae_all_iff]
  intro i
  by_cases hi : i < n
  · have hn : n ≠ 0 := by omega
    have hemp : ∀ᵐ o ∂empirical x n, o ∈ S := by
      rw [ae_iff, empirical_of_ne_zero hn]
      simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_eq_zero fun m hm => ?_, mul_zero]
      rw [show {a | a ∉ S} = Sᶜ from rfl, Measure.dirac_apply' _ hS.compl]
      simp [hx m (Finset.mem_range.1 hm)]
    filter_upwards [(measurePreserving_world_eval x n i).quasiMeasurePreserving.ae hemp]
      with ω h _ using h
  · exact ae_of_all _ fun ω h => absurd h hi

end Resample

section Transfer

/-- Transfer convergence in distribution along a measure-preserving map. -/
private theorem tendstoInDistribution_comp_of_map_eq {Ω₁ Ω₂ Ω' F : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] [MeasurableSpace Ω'] [TopologicalSpace F] [MeasurableSpace F]
    [OpensMeasurableSpace F] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    {μ' : Measure Ω'} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure μ'] {Φ : Ω₁ → Ω₂} (hΦ : Measurable Φ) (hmap : μ₁.map Φ = μ₂)
    {Y : ℕ → Ω₂ → F} (hY : ∀ n, Measurable (Y n)) {Z : Ω' → F}
    (h : TendstoInDistribution Y atTop Z (fun _ => μ₂) μ') :
    TendstoInDistribution (fun n ω => Y n (Φ ω)) atTop Z (fun _ => μ₁) μ' := by
  refine ⟨fun n => ((hY n).comp hΦ).aemeasurable, h.aemeasurable_limit, ?_⟩
  refine h.tendsto.congr fun n => Subtype.ext ?_
  change μ₂.map (Y n) = μ₁.map (Y n ∘ Φ)
  rw [← hmap, Measure.map_map (hY n) hΦ]

/-- Replace the limit variable of a convergence in distribution by one with the same law. -/
private theorem tendstoInDistribution_of_map_limit_eq {Ω₁ Ω₁' Ω₂' F : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₁'] [MeasurableSpace Ω₂'] [TopologicalSpace F]
    [MeasurableSpace F] [OpensMeasurableSpace F] {μ₁ : Measure Ω₁} {ν₁ : Measure Ω₁'}
    {ν₂ : Measure Ω₂'} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] {Y : ℕ → Ω₁ → F} {Z₁ : Ω₁' → F} {Z₂ : Ω₂' → F}
    (h : TendstoInDistribution Y atTop Z₁ (fun _ => μ₁) ν₁) (hZ₂ : AEMeasurable Z₂ ν₂)
    (heq : ν₁.map Z₁ = ν₂.map Z₂) :
    TendstoInDistribution Y atTop Z₂ (fun _ => μ₁) ν₂ := by
  refine ⟨h.forall_aemeasurable, hZ₂, ?_⟩
  have hlim : (⟨ν₂.map Z₂, inferInstance⟩ : ProbabilityMeasure F) =
      ⟨ν₁.map Z₁, inferInstance⟩ := Subtype.ext heq.symm
  rw [hlim]
  exact h.tendsto

variable {t : Fin k → ℝ} (ht : StrictMono t)

/-- The bootstrap Kaplan–Meier statistic on the bootstrap world of the data equals, almost
surely, the smooth statistic `kmMap` of the bootstrap indicator mean on the bootstrap world of
the encoded data; so their convergence in distribution is equivalent. -/
private theorem tendstoInDistribution_kmGrid_of_kmMap (ht0 : ∀ j, 0 < t j) {x : ℕ → ℝ × ℝ}
    (hgrid : ∀ i, (x i).1 ∈ Set.range t) {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {W : Ω' → Fin k → ℝ}
    (h : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
        (kmMap (bootMeanVec n ω) - kmMap (sampleMeanVec (fun i => obsVec t (x i)) n)))
      atTop W (fun _ => world (fun i => obsVec t (x i))) μ') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (kmGrid ht (ω n) n - kmGrid ht x n))
      atTop W (fun _ => world x) μ' := by
  have hΦ : Measurable fun (ω : ℕ → ℕ → ℝ × ℝ) (n m : ℕ) => obsVec t (ω n m) :=
    measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun m =>
      (measurable_obsVec t).comp ((measurable_pi_apply m).comp (measurable_pi_apply n))
  have hY : ∀ n : ℕ, Measurable fun ω : ℕ → ℕ → Coord k => √(n : ℝ) •
      (kmMap (bootMeanVec n ω) - kmMap (sampleMeanVec (fun i => obsVec t (x i)) n)) :=
    fun n => by
      have h := ((measurable_kmMap.comp (measurable_bootMeanVec n)).sub
        (measurable_const (a := kmMap (sampleMeanVec (fun i => obsVec t (x i)) n)))).const_smul
        (√(n : ℝ))
      exact h
  have h1 := tendstoInDistribution_comp_of_map_eq hΦ
    (map_world x (measurable_obsVec t) (obsVec_zero ht0)) hY h
  refine h1.congr (fun n => ?_) (ae_of_all _ fun _ => rfl)
  have hS : MeasurableSet {o : ℝ × ℝ | o.1 ∈ Set.range t} :=
    measurable_fst (Set.finite_range t).measurableSet
  filter_upwards [ae_resample_mem x hS (n := n) fun i _ => hgrid i] with ω hω
  rw [kmGrid_eq_kmMap ht _ n hω, kmGrid_eq_kmMap ht x n fun i _ => hgrid i]
  rfl

end Transfer

section Deterministic

variable {t : Fin k → ℝ} (ht : StrictMono t)

/-- **Bootstrap validity for grid Kaplan–Meier, fixed data.** Let the data `x` have every
observed time on the positive grid `t`, and let `Z` be a random vector in the indicator space
whose projections are `N(0, v s)`. If, in every direction `s`, the plug-in variances of the
encoded data converge to `v s` and satisfy the Lindeberg condition, the encoded sample means
converge to `θ`, and every at-risk mean `θ (inr j)` is positive, then, conditionally on the data
(under `world x`), `√n (Ŝ*ₙ - Ŝₙ)` converges in distribution to `L Z`, `L = fderiv kmMap θ`.
This is the delta-method limit of `√n (Ŝₙ - kmMap θ)` when `√n (x̄ₙ - θ) ⇒ Z`. -/
theorem tendstoInDistribution_bootstrap_kmGrid (ht0 : ∀ j, 0 < t j) (x : ℕ → ℝ × ℝ)
    (hgrid : ∀ i, (x i).1 ∈ Set.range t) {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → Coord k} (hZ : AEMeasurable Z μ')
    (v : Coord k → ℝ≥0) (hZlaw : ∀ s, HasLaw (fun ω => ⟪Z ω, s⟫) (gaussianReal 0 (v s)) μ')
    (hvar : ∀ s, Tendsto (empiricalVar (fun i => ⟪obsVec t (x i), s⟫)) atTop (𝓝 (v s)))
    (hLind : ∀ s, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
        if ε * √n < |⟪obsVec t (x i), s⟫ -
            MathlibExt.Probability.Causality.sampleMean (fun i => ⟪obsVec t (x i), s⟫) (range n)|
        then (⟪obsVec t (x i), s⟫ -
            MathlibExt.Probability.Causality.sampleMean (fun i => ⟪obsVec t (x i), s⟫)
              (range n)) ^ 2
        else 0) atTop (𝓝 0))
    {θ : Coord k} (hθ : Tendsto (sampleMeanVec fun i => obsVec t (x i)) atTop (𝓝 θ))
    (hpos : ∀ j, 0 < θ (Sum.inr j)) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (kmGrid ht (ω n) n - kmGrid ht x n))
      atTop (fun ω => fderiv ℝ kmMap θ (Z ω)) (fun _ => world x) μ' :=
  tendstoInDistribution_kmGrid_of_kmMap ht ht0 hgrid
    (tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt _ hZ v hZlaw hvar hLind hθ
      (hasStrictFDerivAt_kmMap fun j => (hpos j).ne') measurable_kmMap)

end Deterministic

/-- `(√n)⁻¹ (S - n θ) = √n (S / n - θ)`, including `n = 0`. -/
private theorem inv_sqrt_smul_sum_sub_eq {E : Type*} [AddCommGroup E] [Module ℝ E] (S θ : E)
    (n : ℕ) : (√(n : ℝ))⁻¹ • (S - n • θ) = √(n : ℝ) • ((n : ℝ)⁻¹ • S - θ) := by
  have h1 : (√(n : ℝ))⁻¹ = √(n : ℝ) * (n : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]
  have h2 : (√(n : ℝ))⁻¹ * (n : ℝ) = √(n : ℝ) := by
    rw [← div_eq_inv_mul, Real.div_sqrt]
  rw [smul_sub, smul_sub, smul_smul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, h2, h1]

section IID

variable {t : Fin k → ℝ} (ht : StrictMono t)
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Bootstrap consistency for grid Kaplan–Meier.** Let `X 0, X 1, …` be iid observations
whose observed times lie almost surely on the positive grid `t`, let
`θ = E[obsVec t (X 0)]` (so `θ (inl j) = P(X = (t j, 1))` and `θ (inr j) = P(t j ≤ T)`), and
assume every at-risk probability `θ (inr j)` is positive. Let `Z` be a centred Gaussian vector
with the covariance of `obsVec t (X 0)` and `L = fderiv kmMap θ`. Then

* the Kaplan–Meier estimator satisfies `√n (Ŝₙ - S) ⇒ L Z`, `S = kmMap θ` the grid survival
  function `∏_{l ≤ j} (1 - P(X = (t l, 1)) / P(t l ≤ T))`;
* for almost every data sequence, the conditional law of `√n (Ŝ*ₙ - Ŝₙ)` given the data
  converges to the same limit `L Z`. -/
theorem kmGrid_bootstrap_consistent (ht0 : ∀ j, 0 < t j) (X : ℕ → Ω → ℝ × ℝ)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hgrid : ∀ i, ∀ᵐ ω ∂P, (X i ω).1 ∈ Set.range t)
    (hpos : ∀ j, 0 < (∫ ω, obsVec t (X 0 ω) ∂P) (Sum.inr j))
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → Coord k} (hZ : AEMeasurable Z μ')
    (hZlaw : ∀ s, HasLaw (fun ω => ⟪Z ω, s⟫)
      (gaussianReal 0 (Var[fun ω => ⟪obsVec t (X 0 ω), s⟫; P]).toNNReal) μ') :
    TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) •
          (kmGrid ht (fun i => X i ω) n - kmMap (∫ ω, obsVec t (X 0 ω) ∂P)))
        atTop (fun ω => fderiv ℝ kmMap (∫ ω, obsVec t (X 0 ω) ∂P) (Z ω)) (fun _ => P) μ' ∧
      ∀ᵐ ω ∂P, TendstoInDistribution
        (fun (n : ℕ) ω' => √(n : ℝ) • (kmGrid ht (ω' n) n - kmGrid ht (fun i => X i ω) n))
        atTop (fun ω' => fderiv ℝ kmMap (∫ ω, obsVec t (X 0 ω) ∂P) (Z ω'))
        (fun _ => world (fun i => X i ω)) μ' := by
  have hYm : ∀ i, AEMeasurable (fun ω => obsVec t (X i ω)) P := fun i =>
    (measurable_obsVec t).comp_aemeasurable (hident i).aemeasurable_fst
  have hmem : MemLp (fun ω => obsVec t (X 0 ω)) 2 P :=
    MemLp.of_bound (hYm 0).aestronglyMeasurable _ (ae_of_all _ fun ω => norm_obsVec_le t _)
  have hindep' : iIndepFun (fun i ω => obsVec t (X i ω)) P :=
    hindep.comp (fun _ => obsVec t) fun _ => measurable_obsVec t
  have hident' : ∀ i, IdentDistrib (fun ω => obsVec t (X i ω)) (fun ω => obsVec t (X 0 ω))
      P P := fun i => (hident i).comp (measurable_obsVec t)
  have hg := hasStrictFDerivAt_kmMap (θ := ∫ ω, obsVec t (X 0 ω) ∂P) fun j => (hpos j).ne'
  have hgridω : ∀ᵐ ω ∂P, ∀ i, (X i ω).1 ∈ Set.range t := ae_all_iff.2 hgrid
  have hmeanm : ∀ n : ℕ, AEMeasurable
      (fun ω => sampleMeanVec (fun i => obsVec t (X i ω)) n) P := fun n => by
    have h := (Finset.aemeasurable_fun_sum (range n) fun i _ => hYm i).const_smul ((n : ℝ)⁻¹)
    exact h
  refine ⟨?_, ?_⟩
  · -- sampling law: multivariate CLT, then the delta method, then the grid bridge
    have hclt := tendstoInDistribution_inv_sqrt_smul_sum_sub
      (X := fun i ω => obsVec t (X i ω)) hZ hZlaw hmem hindep' hident'
    have hclt' : TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) •
          (sampleMeanVec (fun i => obsVec t (X i ω)) n - ∫ ω, obsVec t (X 0 ω) ∂P))
        atTop Z (fun _ => P) μ' :=
      hclt.congr (fun n => ae_of_all _ fun ω => inv_sqrt_smul_sum_sub_eq _ _ n)
        (ae_of_all _ fun _ => rfl)
    have hdelta := TendstoInDistribution.delta_method_of_hasStrictFDerivAt hclt'
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) tendsto_const_nhds hg
      hmeanm (fun n => measurable_kmMap.comp_aemeasurable (hmeanm n))
    refine hdelta.congr (fun n => ?_) (ae_of_all _ fun _ => rfl)
    filter_upwards [hgridω] with ω hω
    rw [kmGrid_eq_kmMap ht _ n fun i _ => hω i]
  · -- bootstrap law: almost-sure bootstrap delta method, then the transfer to resampled data
    filter_upwards [ae_tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt
      (fun i ω => obsVec t (X i ω)) hmem (fun _ _ hij => hindep'.indepFun hij) hident' hZ
      hZlaw hg measurable_kmMap, hgridω] with ω h hω
    exact tendstoInDistribution_kmGrid_of_kmMap ht ht0 hω h

/-- **Bootstrap validity with the Kaplan–Meier limit as hypothesis.** Under the hypotheses of
`kmGrid_bootstrap_consistent`, if the Kaplan–Meier estimator satisfies
`√n (Ŝₙ - S) ⇒ W` for some limit `W` (on any probability space), then for almost every data
sequence the conditional law of the bootstrap statistic `√n (Ŝ*ₙ - Ŝₙ)` converges to the law
of `W`: the bootstrap reproduces the Kaplan–Meier limit law. -/
theorem ae_tendstoInDistribution_bootstrap_kmGrid_of_limit (ht0 : ∀ j, 0 < t j)
    (X : ℕ → Ω → ℝ × ℝ) (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hgrid : ∀ i, ∀ᵐ ω ∂P, (X i ω).1 ∈ Set.range t)
    (hpos : ∀ j, 0 < (∫ ω, obsVec t (X 0 ω) ∂P) (Sum.inr j))
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → Coord k} (hZ : AEMeasurable Z μ')
    (hZlaw : ∀ s, HasLaw (fun ω => ⟪Z ω, s⟫)
      (gaussianReal 0 (Var[fun ω => ⟪obsVec t (X 0 ω), s⟫; P]).toNNReal) μ')
    {Ω'' : Type*} [MeasurableSpace Ω''] {ν : Measure Ω''} [IsProbabilityMeasure ν]
    {W : Ω'' → Fin k → ℝ}
    (hKM : TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) •
          (kmGrid ht (fun i => X i ω) n - kmMap (∫ ω, obsVec t (X 0 ω) ∂P)))
        atTop W (fun _ => P) ν) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) ω' => √(n : ℝ) • (kmGrid ht (ω' n) n - kmGrid ht (fun i => X i ω) n))
      atTop W (fun _ => world (fun i => X i ω)) ν := by
  obtain ⟨hsamp, hboot⟩ :=
    kmGrid_bootstrap_consistent ht ht0 X hindep hident hgrid hpos hZ hZlaw
  have heq := tendsto_nhds_unique hsamp.tendsto hKM.tendsto
  filter_upwards [hboot] with ω h
  exact tendstoInDistribution_of_map_limit_eq h hKM.aemeasurable_limit
    (congrArg Subtype.val heq)

end IID

end MathlibExt.Probability.Statistics.KMBootstrap
