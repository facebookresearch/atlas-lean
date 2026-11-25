/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.WaldInequalities
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Moustakides' theorem: optimality of CUSUM under Lorden's criterion

For each change point `ν ≥ 1`, unknown and without a prior, let the observations be independent,
with law `P₀` before `X_ν` and law `P₁` from `X_ν` on (`changePointLaw P₀ P₁ ν`); `E_∞` is the
mean when no change occurs, every observation having law `P₀`.
`MeasureTheory.cusumTime_lordenDelay_le` states that the CUSUM alarm
`N_c = inf {n ≥ 1 : W_n ≥ c}` of `MathlibExt.Probability.Statistics.SequentialAnalysis`, raised
when Page's statistic reaches or exceeds the threshold `c > 0`, minimises Lorden's worst-case
detection delay among all stopping times `T` with `E_∞[T] ≥ E_∞[N_c]` (Moustakides 1986, as
stated in Lai 2001, §3, p. 316). Along the way,
`MeasureTheory.adapted_pageCusum` shows that Page's statistic is adapted to the observations and
`MeasureTheory.isStoppingTime_cusumTime` that the CUSUM alarm is a stopping time.

## Proof outline

Write `L = dP₁/dP₀`, `μ = P₀^ℕ`, `J = lordenDelay` and `D = E₁[N_c]`, the mean of `N_c` when every
observation has law `P₁`. CUSUM is read through the chain `U₀ = 0`,
`U_{n+1} = L(X_{n+1}) max(Uₙ, 1)`, for which `max(Uₙ, 1) = exp Wₙ`, so that
`N_c = inf {n ≥ 1 : Uₙ ≥ e^c}`. All expectations are lower integrals in `ℝ≥0∞`. Put
`A(T) = E_μ[∑_{k<T} max(U_k, 1)]`, `B(T) = E_μ[∑_{k<T} (1 - U_k)⁺]` and
`R(T) = E_μ[∑_{k<T} r(U_k)]` with `r(u) = max(u, 1) + D min(u, 1)`.

* **Lower bound for Lorden's criterion.** Since
  `max(Uₙ, 1) = ∑_{m ≤ n} (1 - U_m)⁺ ∏_{m ≤ i < n} L(X_{i+1})`, a change of measure gives
  `A(T) = ∑_m E_{m+1}[(1 - U_m)⁺ (T - m)⁺]` for every stopping time `T`, and the definition of
  `J` bounds each term: `A(T) ≤ J(T) B(T)`.
* **CUSUM restarts at a change point.** Page's statistic restarted at time `m` is at most the
  original one, and equals it when the original vanishes. As the shifted observations are
  independent of the past, `J(N_c) ≤ D` and `A(N_c) ≥ D B(N_c)`.
* **Finite means.** Since `P₀ ≠ P₁`, `log L ≥ δ` for some `δ > 0` with positive probability under
  `P₀` and under `P₁`, and a block of `⌈c/δ⌉ + 1` such observations raises the alarm. Hence
  `E_μ[N_c] < ∞` and `D < ∞`.
* **Discounted problems.** For a discount `0 < β < 1` and a cost `θ > 0`, backward induction gives
  the value function `V ≤ 1` of the problem with running cost `θ r(U)`, stopping cost `1` and
  discount `β`. The value and the continuation cost `C` are monotone in the state, and `C(e^c)` is
  continuous in `θ`, so the intermediate value theorem gives a cost with `C(e^c) = 1`. For this
  cost CUSUM observes where observing is optimal and stops where stopping is, so it attains the
  value. Turning the stopping cost into a running cost gives a multiplier `0 ≤ s ≤ r(e^c)` with
  `E_μ[∑_{k<N_c} βᵏ r(U_k)] + s E_μ[∑_{k<T} βᵏ] ≤ E_μ[∑_{k<T} βᵏ r(U_k)] + s E_μ[∑_{k<N_c} βᵏ]`
  for every stopping time `T`.
* **Vanishing discount.** Along `β_j = 1 - 1/(j + 2)` a subsequence of the multipliers converges
  to some `S`, and monotone convergence gives `R(N_c) + S E_μ[T] ≤ R(T) + S E_μ[N_c]` whenever
  `E_μ[T] < ∞`. The stopping time `T = 0` and `R(N_c) ≥ D E_μ[N_c]` give `S ≥ D`, so
  `E_μ[T] ≥ E_μ[N_c]` implies `R(T) ≥ D E_μ[T]`, that is `A(T) ≥ D B(T)`. As `B(T) > 0`,
  `J(T) ≥ D ≥ J(N_c)`.
* **Infinite mean.** A stopping time with `E_μ[T] = ∞` is truncated at a large time, which only
  lowers Lorden's criterion.

The backward induction, the choice of the cost and the verification argument of the discounted
problems adapt those of `MathlibExt.Probability.Statistics.ShiryaevOptimality` to the CUSUM
chain, its running cost and a free discount.

## References

* G. V. Moustakides, *Optimal stopping times for detecting changes in distributions*, Annals of
  Statistics 14 (1986) 1379–1387.
* T. L. Lai, *Sequential analysis: some classical problems and new challenges*, Statistica Sinica
  11 (2001) 303–408, §3 (p. 316).
* V. V. Veeravalli and T. Banerjee, *Quickest change detection*, arXiv:1210.5552 (revised
  version dated 27 November 2024).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-! ### Stopping times and expectations of random times -/

private theorem enat_toENNReal_eq_tsum (k : ℕ∞) :
    (k : ℝ≥0∞) = ∑' n : ℕ, if (n : ℕ∞) < k then 1 else 0 := by
  induction k using ENat.recTopCoe with
  | top =>
    simp only [ENat.natCast_lt_top, ite_true, ENat.toENNReal_top]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe m =>
    rw [tsum_eq_sum (s := range m)]
    · rw [sum_congr rfl (g := fun _ => (1 : ℝ≥0∞)) fun n hn => by simp [mem_range.1 hn]]
      simp
    · intro n hn
      simpa using hn

private theorem measurableSet_natCast_lt {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) (n : ℕ) :
    MeasurableSet[observationFiltration X n] {ω | (n : WithTop ℕ) < T ω} :=
  hT.measurableSet_gt n

private theorem enat_lt_sub_iff (t : ℕ∞) (j m : ℕ) :
    (j : ℕ∞) < t - (m : ℕ∞) ↔ ((j + m : ℕ) : ℕ∞) < t := by
  induction t using ENat.recTopCoe with
  | top => simp
  | coe t =>
    rw [← ENat.natCast_sub, Nat.cast_lt, Nat.cast_lt]
    omega

/-! ### Independence of the past and the shifted future -/

/-- **Independence of the past and the shifted future.** Under a product law, a function of the
first `m` coordinates and a function of the coordinates from `m` on are independent, and the
shifted path has the shifted product law. -/
private theorem lintegral_mul_comp_shift (μ : ℕ → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (m : ℕ) {φ : (ℕ → X) → ℝ≥0∞} (hφ : Measurable[observationFiltration X m] φ)
    {g : (ℕ → X) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, φ ω * g (fun i => ω (i + m)) ∂Measure.infinitePi μ =
      (∫⁻ ω, φ ω ∂Measure.infinitePi μ) *
        ∫⁻ ω, g ω ∂Measure.infinitePi (fun i => μ (i + m)) := by
  set M : ℕ → MeasurableSpace (ℕ → X) :=
    fun i => MeasurableSpace.comap (fun ω : ℕ → X => ω i) inferInstance with hM
  have hMle : ∀ i, M i ≤ MeasurableSpace.pi := fun i => (measurable_pi_apply i).comap_le
  have hind : iIndep M (Measure.infinitePi μ) := by
    have h := iIndepFun_infinitePi (P := μ) (X := fun _ (x : X) => x) (fun _ => measurable_id)
    exact (iIndepFun_iff_iIndep _ _ _).1 h
  have hindep := indep_iSup_of_disjoint hMle hind
    (S := {i : ℕ | i < m}) (T := {i : ℕ | m ≤ i})
    (Set.disjoint_left.2 fun i (hi : i < m) (hi' : m ≤ i) => absurd hi' (not_le.2 hi))
  have hS : (observationFiltration X m : MeasurableSpace (ℕ → X)) ≤
      ⨆ i ∈ {i : ℕ | i < m}, M i := by
    change MeasurableSpace.comap (range m).restrict MeasurableSpace.pi ≤ _
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun j => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun i (_ : i ∈ {i : ℕ | i < m}) => M i) j.1 (mem_range.1 j.2)
  have hshift : @Measurable (ℕ → X) (ℕ → X) (⨆ i ∈ {i : ℕ | m ≤ i}, M i) MeasurableSpace.pi
      fun ω : ℕ → X => fun i => ω (i + m) := by
    refine Measurable.of_comap_le ?_
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun j => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun i (_ : i ∈ {i : ℕ | m ≤ i}) => M i) (j + m) (Nat.le_add_left m j)
  have hshift' : Measurable fun ω : ℕ → X => fun i => ω (i + m) :=
    measurable_pi_iff.2 fun j => measurable_pi_apply (j + m)
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (g := fun ω : ℕ → X => g fun i => ω (i + m))
    (iSup₂_le fun i _ => hMle i) (iSup₂_le fun i _ => hMle i) hindep (hφ.mono hS le_rfl)
    (hg.comp hshift)]
  congr 1
  rw [← lintegral_map hg hshift', Measure.map_infinitePi_infinitePi_of_inj (add_left_injective m)]

/-! ### The likelihood ratio and the CUSUM chain -/

/-- The likelihood ratio `dP₁/dP₀`, read as `exp (log L)` through Mathlib's `llr`; it agrees
with `dP₁/dP₀` almost surely for mutually absolutely continuous laws. -/
private noncomputable def cusLr (P₀ P₁ : Measure X) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (llr P₁ P₀ x))

private theorem measurable_cusLr (P₀ P₁ : Measure X) : Measurable (cusLr P₀ P₁) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_llr _ _))

private theorem withDensity_cusLr (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) :
    P₀.withDensity (cusLr P₀ P₁) = P₁ := by
  calc P₀.withDensity (cusLr P₀ P₁) = P₀.withDensity (P₁.rnDeriv P₀) := by
        refine withDensity_congr_ae ?_
        filter_upwards [exp_llr_of_ac' P₁ P₀ h₀₁, Measure.rnDeriv_lt_top P₁ P₀] with x hx hx'
        rw [cusLr, hx, ENNReal.ofReal_toReal hx'.ne]
    _ = P₁ := Measure.withDensity_rnDeriv_eq P₁ P₀ h₁₀

/-- One step of the CUSUM chain in likelihood-ratio form: `U_{n+1} = L(X_{n+1}) max(Uₙ, 1)`. -/
private noncomputable def cusStep (P₀ P₁ : Measure X) (u : ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  cusLr P₀ P₁ x * max u 1

/-- The CUSUM chain `U₀ = 0`, `U_{n+1} = L(X_{n+1}) max(Uₙ, 1)`; `max(Uₙ, 1) = exp Wₙ`. -/
private noncomputable def cusU (P₀ P₁ : Measure X) : ℕ → (ℕ → X) → ℝ≥0∞
  | 0 => fun _ => 0
  | n + 1 => fun ω => cusStep P₀ P₁ (cusU P₀ P₁ n ω) (ω n)

private theorem cusStep_mono (P₀ P₁ : Measure X) {u u' : ℝ≥0∞} (h : u ≤ u') (x : X) :
    cusStep P₀ P₁ u x ≤ cusStep P₀ P₁ u' x := by
  unfold cusStep
  gcongr

private theorem measurable_cusStep (P₀ P₁ : Measure X) :
    Measurable (Function.uncurry (cusStep P₀ P₁)) :=
  ((measurable_cusLr P₀ P₁).comp measurable_snd).mul (measurable_fst.max measurable_const)

private theorem measurable_cusStep_right (P₀ P₁ : Measure X) (u : ℝ≥0∞) :
    Measurable (cusStep P₀ P₁ u) :=
  (measurable_cusLr P₀ P₁).mul_const _

private theorem measurable_cusU (P₀ P₁ : Measure X) (n : ℕ) :
    Measurable[observationFiltration X n] (cusU P₀ P₁ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_cusStep P₀ P₁).comp
      ((ih.mono ((observationFiltration X).mono (Nat.le_succ n)) le_rfl).prodMk
        (measurable_coord_observationFiltration (Nat.lt_add_one n)))

private theorem measurable_cusU' (P₀ P₁ : Measure X) (n : ℕ) : Measurable (cusU P₀ P₁ n) :=
  (measurable_cusU P₀ P₁ n).mono ((observationFiltration X).le n) le_rfl

private theorem cusU_ne_top (P₀ P₁ : Measure X) (n : ℕ) (ω : ℕ → X) : cusU P₀ P₁ n ω ≠ ∞ := by
  cases n with
  | zero => exact ENNReal.zero_ne_top
  | succ n =>
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (max_ne_top (cusU_ne_top P₀ P₁ n ω) ENNReal.one_ne_top)

/-- `max(Uₙ, 1) = exp Wₙ`, where `Wₙ` is Page's CUSUM statistic. -/
private theorem max_cusU_one (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (n : ℕ) (ω : ℕ → X) :
    max (cusU P₀ P₁ n ω) 1 = ENNReal.ofReal (Real.exp (pageCusum P₀ P₁ h₁₀ h₀₁ n ω)) := by
  induction n with
  | zero => simp [cusU, pageCusum]
  | succ n ih =>
    simp only [cusU, cusStep, cusLr, ih, pageCusum]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_max, ← Real.exp_zero,
      ← Monotone.map_max Real.exp_monotone, add_comm (llr P₁ P₀ (ω n))]

/-- The CUSUM alarm condition in terms of the chain: for `c > 0`, `Wₙ ≥ c` iff `Uₙ ≥ e^c`. -/
private theorem le_pageCusum_iff (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {c : ℝ} (hc : 0 < c) (n : ℕ)
    (ω : ℕ → X) :
    c ≤ pageCusum P₀ P₁ h₁₀ h₀₁ n ω ↔ ENNReal.ofReal (Real.exp c) ≤ cusU P₀ P₁ n ω := by
  have h1 : ¬ ENNReal.ofReal (Real.exp c) ≤ 1 := by
    rw [not_le, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos c)]
    exact Real.one_lt_exp_iff.2 hc
  rw [← Real.exp_le_exp, ← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
    ← max_cusU_one P₀ P₁ h₁₀ h₀₁ n ω, le_max_iff, or_iff_left h1]

/-! ### Change of measure for the change-point laws -/

private instance (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (ν : ℕ) : IsProbabilityMeasure (changePointLaw P₀ P₁ ν) := by
  unfold changePointLaw
  infer_instance

/-- Density of the law of the coordinate `i` under `changePointLaw P₀ P₁ ν`. -/
private noncomputable def cpDens (P₀ P₁ : Measure X) (ν i : ℕ) : X → ℝ≥0∞ :=
  if i + 1 < ν then 1 else cusLr P₀ P₁

private theorem measurable_cpDens (P₀ P₁ : Measure X) (ν i : ℕ) :
    Measurable (cpDens P₀ P₁ ν i) := by
  unfold cpDens
  split_ifs
  · exact measurable_const
  · exact measurable_cusLr P₀ P₁

/-- Change of measure from `P₀^ℕ` to a change-point law on the first `n` observations. -/
private theorem changePointLaw_apply_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (ν n : ℕ) {A : Set (ℕ → X)}
    (hA : MeasurableSet[observationFiltration X n] A) :
    changePointLaw P₀ P₁ ν A = ∫⁻ ω in A, ∏ i ∈ range n, cpDens P₀ P₁ ν i (ω i)
      ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  refine infinitePi_apply_eq_setLIntegral_prod P₀ _ (cpDens P₀ P₁ ν)
    (measurable_cpDens P₀ P₁ ν) (fun i => ?_) n hA
  unfold cpDens
  split_ifs
  · exact withDensity_one.symm
  · exact (withDensity_cusLr P₀ P₁ h₁₀ h₀₁).symm

/-- Change of measure for integrals of functions of the first `n` observations. -/
private theorem lintegral_changePointLaw_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (ν n : ℕ)
    {f : (ℕ → X) → ℝ≥0∞} (hf : Measurable[observationFiltration X n] f) :
    ∫⁻ ω, f ω ∂changePointLaw P₀ P₁ ν =
      ∫⁻ ω, f ω * ∏ i ∈ range n, cpDens P₀ P₁ ν i (ω i)
        ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  have hle := (observationFiltration X).le n
  have hρ : Measurable[observationFiltration X n]
      fun ω : ℕ → X => ∏ i ∈ range n, cpDens P₀ P₁ ν i (ω i) :=
    Finset.measurable_prod _ fun i hi => (measurable_cpDens P₀ P₁ ν i).comp
      (measurable_coord_observationFiltration (mem_range.1 hi))
  have htrim : (changePointLaw P₀ P₁ ν).trim hle =
      ((Measure.infinitePi fun _ : ℕ => P₀).withDensity
        fun ω => ∏ i ∈ range n, cpDens P₀ P₁ ν i (ω i)).trim hle := by
    refine @Measure.ext _ (observationFiltration X n) _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hle hA, trim_measurableSet_eq hle hA,
      withDensity_apply _ (hle A hA)]
    exact changePointLaw_apply_eq P₀ P₁ h₁₀ h₀₁ ν n hA
  rw [← lintegral_trim hle hf, htrim, lintegral_trim hle hf,
    lintegral_withDensity_eq_lintegral_mul _ (hρ.mono hle le_rfl) (hf.mono hle le_rfl)]
  simp_rw [Pi.mul_apply, mul_comm]

/-- Before the change, a change-point law integrates like `P₀^ℕ`. -/
private theorem lintegral_changePointLaw_eq_of_lt (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {ν n : ℕ} (hn : n < ν)
    {f : (ℕ → X) → ℝ≥0∞} (hf : Measurable[observationFiltration X n] f) :
    ∫⁻ ω, f ω ∂changePointLaw P₀ P₁ ν = ∫⁻ ω, f ω ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  rw [lintegral_changePointLaw_eq P₀ P₁ h₁₀ h₀₁ ν n hf]
  refine lintegral_congr fun ω => ?_
  rw [prod_eq_one fun i hi => ?_, mul_one]
  simp [cpDens, show i + 1 < ν by have := mem_range.1 hi; omega]

/-- After the change point `m + 1`, the density on the first `n ≥ m` observations is the
likelihood ratio of the observations `m, …, n - 1` (in coordinates). -/
private theorem prod_cpDens_eq (P₀ P₁ : Measure X) {m n : ℕ} (hmn : m ≤ n) (ω : ℕ → X) :
    ∏ i ∈ range n, cpDens P₀ P₁ (m + 1) i (ω i) = ∏ i ∈ Ico m n, cusLr P₀ P₁ (ω i) := by
  rw [← prod_range_mul_prod_Ico _ hmn, prod_eq_one fun i hi => ?_, one_mul]
  · refine prod_congr rfl fun i hi => ?_
    simp [cpDens, show ¬ i + 1 < m + 1 by have := (mem_Ico.1 hi).1; omega]
  · simp [cpDens, show i + 1 < m + 1 by have := mem_range.1 hi; omega]

/-! ### Lorden's criterion -/

/-- The delay `(T - m)⁺` counted in `ℝ≥0∞`, as a sum of indicators. -/
private theorem enat_sub_eq_tsum (t : WithTop ℕ) (m : ℕ) :
    (((show ℕ∞ from t) - m : ℕ∞) : ℝ≥0∞) =
      ∑' j : ℕ, if ((j + m : ℕ) : WithTop ℕ) < t then 1 else 0 := by
  rw [enat_toENNReal_eq_tsum]
  congr 1
  funext j
  have h := enat_lt_sub_iff t j m
  by_cases hj : ((j + m : ℕ) : WithTop ℕ) < t
  · rw [ite_eq_left (h.2 hj), ite_eq_left hj]
  · rw [ite_eq_right (mt h.1 hj), ite_eq_right hj]

private theorem measurable_enat_sub {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) (m : ℕ) :
    Measurable fun ω => (((show ℕ∞ from T ω) - m : ℕ∞) : ℝ≥0∞) := by
  simp_rw [enat_sub_eq_tsum]
  exact Measurable.tsum fun j => Measurable.ite
    ((observationFiltration X).le _ _ (measurableSet_natCast_lt hT (j + m)))
    measurable_const measurable_const

private theorem measurable_enat {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) :
    Measurable fun ω => ((show ℕ∞ from T ω) : ℝ≥0∞) := by
  have hpt : (fun ω => ((show ℕ∞ from T ω) : ℝ≥0∞)) =
      fun ω => ∑' n : ℕ, if (n : WithTop ℕ) < T ω then 1 else 0 :=
    funext fun ω => enat_toENNReal_eq_tsum (T ω)
  rw [hpt]
  exact Measurable.tsum fun n => Measurable.ite
    ((observationFiltration X).le _ _ (measurableSet_natCast_lt hT n))
    measurable_const measurable_const

private theorem enat_add_one_sub (t : ℕ∞) (m : ℕ) :
    t + 1 - ((m + 1 : ℕ) : ℕ∞) = t - m := by
  induction t using ENat.recTopCoe with
  | top => simp
  | coe t =>
    rw [← Nat.cast_one, ← Nat.cast_add, ← ENat.natCast_sub, ← ENat.natCast_sub]
    congr 1
    omega

private theorem enat_sub_eq_zero_of_not_lt {t : WithTop ℕ} {m : ℕ}
    (h : ¬ (m : WithTop ℕ) < t) : (((show ℕ∞ from t) - m : ℕ∞) : ℝ≥0∞) = 0 := by
  have h' : (show ℕ∞ from t) ≤ (m : ℕ∞) := not_lt.1 h
  simp [tsub_eq_zero_of_le h']

/-- **Lorden's criterion bounds every conditional delay.** -/
private theorem setLIntegral_le_lordenDelay (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (T : (ℕ → X) → WithTop ℕ) (m : ℕ) {F : Set (ℕ → X)}
    (hF : MeasurableSet[observationFiltration X m] F) :
    ∫⁻ ω in F, (((show ℕ∞ from T ω) - m : ℕ∞) : ℝ≥0∞) ∂changePointLaw P₀ P₁ (m + 1) ≤
      lordenDelay P₀ P₁ T * changePointLaw P₀ P₁ (m + 1) F := by
  by_cases hF0 : changePointLaw P₀ P₁ (m + 1) F = 0
  · rw [setLIntegral_measure_zero _ _ hF0]
    exact zero_le
  rw [← ENNReal.div_le_iff hF0 (measure_ne_top _ _)]
  have hint : ∫⁻ ω in F, (((show ℕ∞ from T ω) - m : ℕ∞) : ℝ≥0∞) ∂changePointLaw P₀ P₁ (m + 1) =
      ∫⁻ ω in F, (((show ℕ∞ from T ω) + 1 - ((m + 1 : ℕ) : ℕ∞) : ℕ∞) : ℝ≥0∞)
        ∂changePointLaw P₀ P₁ (m + 1) :=
    lintegral_congr fun ω =>
      congrArg (fun t : ℕ∞ => (t : ℝ≥0∞)) (enat_add_one_sub (T ω) m).symm
  rw [hint]
  exact le_iSup₂_of_le (m + 1) (Nat.le_add_left 1 m) <|
    le_iSup₂_of_le (f := fun F (_ : MeasurableSet[observationFiltration X (m + 1 - 1)] F) =>
      ⨆ (_ : 0 < changePointLaw P₀ P₁ (m + 1) F),
        (∫⁻ ω in F, (((show ℕ∞ from T ω) + 1 - ((m + 1 : ℕ) : ℕ∞) : ℕ∞) : ℝ≥0∞)
          ∂changePointLaw P₀ P₁ (m + 1)) / changePointLaw P₀ P₁ (m + 1) F) F hF <|
    le_iSup_of_le (pos_iff_ne_zero.2 hF0) le_rfl

/-- **Lorden's criterion bounds every weighted delay.** For a nonnegative weight `φ` of the
first `m` observations, `E_{m+1}[φ (T - m)⁺] ≤ lordenDelay(T) E_{m+1}[φ]`. -/
private theorem lintegral_mul_le_lordenDelay (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) (m : ℕ) {φ : (ℕ → X) → ℝ≥0∞}
    (hφ : Measurable[observationFiltration X m] φ) :
    ∫⁻ ω, φ ω * (((show ℕ∞ from T ω) - m : ℕ∞) : ℝ≥0∞) ∂changePointLaw P₀ P₁ (m + 1) ≤
      lordenDelay P₀ P₁ T * ∫⁻ ω, φ ω ∂changePointLaw P₀ P₁ (m + 1) := by
  set μ := changePointLaw P₀ P₁ (m + 1)
  set Δ : (ℕ → X) → ℝ≥0∞ := fun ω => (((show ℕ∞ from T ω) - m : ℕ∞) : ℝ≥0∞) with hΔ
  have hle := (observationFiltration X).le m
  have hΔm : Measurable Δ := measurable_enat_sub hT m
  have hmeas : (μ.withDensity Δ).trim hle ≤ lordenDelay P₀ P₁ T • μ.trim hle := by
    refine Measure.le_iff.2 fun F hF => ?_
    rw [trim_measurableSet_eq hle hF, smul_apply, trim_measurableSet_eq hle hF,
      withDensity_apply _ (hle F hF), smul_eq_mul]
    exact setLIntegral_le_lordenDelay P₀ P₁ T m hF
  calc ∫⁻ ω, φ ω * Δ ω ∂μ = ∫⁻ ω, φ ω ∂(μ.withDensity Δ) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hΔm (hφ.mono hle le_rfl)]
        simp_rw [Pi.mul_apply, mul_comm]
    _ = ∫⁻ ω, φ ω ∂((μ.withDensity Δ).trim hle) := (lintegral_trim hle hφ).symm
    _ ≤ ∫⁻ ω, φ ω ∂(lordenDelay P₀ P₁ T • μ.trim hle) := lintegral_mono' hmeas le_rfl
    _ = lordenDelay P₀ P₁ T * ∫⁻ ω, φ ω ∂μ := by
        rw [lintegral_smul_measure, lintegral_trim hle hφ, smul_eq_mul]

/-! ### Expected sums along the CUSUM chain -/

private theorem tsum_ite_le_eq (g : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑' n : ℕ, (if k ≤ n then g n else 0) = ∑' j : ℕ, g (j + k) := by
  rw [← (add_left_injective k).tsum_eq (f := fun n => if k ≤ n then g n else 0)]
  · exact tsum_congr fun j => ite_eq_left (Nat.le_add_left k j)
  · intro n hn
    have hkn : k ≤ n := by
      by_contra h
      exact hn (ite_eq_right h)
    exact ⟨n - k, Nat.sub_add_cancel hkn⟩

private theorem tsum_ite_lt_eq (g : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑' n : ℕ, (if n < k then g n else 0) = ∑ n ∈ range k, g n := by
  rw [tsum_eq_sum (s := range k) fun n hn => ite_eq_right (by simpa using hn)]
  exact sum_congr rfl fun n hn => ite_eq_left (mem_range.1 hn)

/-- `E_∞[∑_{k<T} f(U_k)]`, the expected sum of `f` along the CUSUM chain before `T`, under
`P₀^ℕ`. -/
private noncomputable def cusSum (P₀ P₁ : Measure X) (f : ℝ≥0∞ → ℝ≥0∞)
    (T : (ℕ → X) → WithTop ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < T ω}, f (cusU P₀ P₁ k ω)
    ∂Measure.infinitePi (fun _ : ℕ => P₀)

private theorem cusSum_add (P₀ P₁ : Measure X) {f g : ℝ≥0∞ → ℝ≥0∞} (hf : Measurable f)
    (T : (ℕ → X) → WithTop ℕ) :
    cusSum P₀ P₁ (fun u => f u + g u) T = cusSum P₀ P₁ f T + cusSum P₀ P₁ g T := by
  unfold cusSum
  rw [← tsum_add]
  refine tsum_congr fun k => ?_
  exact lintegral_add_left (hf.comp (measurable_cusU' P₀ P₁ k)) _

private theorem cusSum_const_mul (P₀ P₁ : Measure X) {f : ℝ≥0∞ → ℝ≥0∞} (hf : Measurable f)
    (c : ℝ≥0∞) (T : (ℕ → X) → WithTop ℕ) :
    cusSum P₀ P₁ (fun u => c * f u) T = c * cusSum P₀ P₁ f T := by
  unfold cusSum
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun k => lintegral_const_mul _ (hf.comp (measurable_cusU' P₀ P₁ k))

private theorem cusSum_mono (P₀ P₁ : Measure X) {f g : ℝ≥0∞ → ℝ≥0∞} (h : ∀ u, f u ≤ g u)
    (T : (ℕ → X) → WithTop ℕ) : cusSum P₀ P₁ f T ≤ cusSum P₀ P₁ g T :=
  tsum_le_tsum fun _ => lintegral_mono fun _ => h _

/-- `E_∞[T] = E_∞[∑_{k<T} 1]`. -/
private theorem cusSum_one (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    {T : (ℕ → X) → WithTop ℕ} (hT : IsStoppingTime (observationFiltration X) T) :
    cusSum P₀ P₁ (fun _ => 1) T =
      ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  rw [lintegral_enat_eq_tsum _ fun n =>
    (observationFiltration X).le n _ (measurableSet_natCast_lt hT n)]
  unfold cusSum
  simp only [setLIntegral_const, one_mul]

private theorem max_one_eq_add_tsub (a : ℝ≥0∞) : max a 1 = a + (1 - a) := by
  rcases le_total a 1 with h | h
  · rw [max_eq_right h, add_tsub_cancel_of_le h]
  · rw [max_eq_left h, tsub_eq_zero_of_le h, add_zero]

/-- **Decomposition of the CUSUM statistic over the change points.**
`max(Uₙ, 1) = ∑_{m ≤ n} (1 - U_m)⁺ ∏_{m ≤ i < n} L(ω i)`. -/
private theorem max_cusU_one_eq_sum (P₀ P₁ : Measure X) (n : ℕ) (ω : ℕ → X) :
    max (cusU P₀ P₁ n ω) 1 =
      ∑ m ∈ range (n + 1), (1 - cusU P₀ P₁ m ω) * ∏ i ∈ Ico m n, cusLr P₀ P₁ (ω i) := by
  induction n with
  | zero => simp [cusU]
  | succ n ih =>
    rw [max_one_eq_add_tsub, sum_range_succ, Ico_self, prod_empty, mul_one]
    congr 1
    change cusLr P₀ P₁ (ω n) * max (cusU P₀ P₁ n ω) 1 = _
    rw [ih, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [prod_Ico_succ_top (by have := mem_range.1 hm; omega)]
    ring

/-- **Lorden's criterion through change points.** For every stopping time `T`,
`E_∞[∑_{k<T} max(U_k, 1)] = ∑_m E_{m+1}[(1 - U_m)⁺ (T - m)⁺]`. -/
private theorem cusSum_max_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) :
    cusSum P₀ P₁ (fun u => max u 1) T = ∑' m : ℕ, ∫⁻ ω, (1 - cusU P₀ P₁ m ω) *
      (((show ℕ∞ from T ω) - m : ℕ∞) : ℝ≥0∞) ∂changePointLaw P₀ P₁ (m + 1) := by
  set μ := Measure.infinitePi (fun _ : ℕ => P₀)
  set g : ℕ → ℕ → ℝ≥0∞ := fun m n => ∫⁻ ω, (if (n : WithTop ℕ) < T ω then
    1 - cusU P₀ P₁ m ω else 0) * ∏ i ∈ Ico m n, cusLr P₀ P₁ (ω i) ∂μ with hg
  have hS : ∀ n : ℕ, MeasurableSet[observationFiltration X n] {ω | (n : WithTop ℕ) < T ω} :=
    measurableSet_natCast_lt hT
  -- each change point
  have hm : ∀ m : ℕ, ∫⁻ ω, (1 - cusU P₀ P₁ m ω) *
      (((show ℕ∞ from T ω) - m : ℕ∞) : ℝ≥0∞) ∂changePointLaw P₀ P₁ (m + 1) =
      ∑' j : ℕ, g m (j + m) := by
    intro m
    have hpt : ∀ ω, (1 - cusU P₀ P₁ m ω) * (((show ℕ∞ from T ω) - m : ℕ∞) : ℝ≥0∞) =
        ∑' j : ℕ, (if ((j + m : ℕ) : WithTop ℕ) < T ω then 1 - cusU P₀ P₁ m ω else 0) := by
      intro ω
      rw [enat_sub_eq_tsum, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun j => ?_
      split_ifs <;> simp
    simp_rw [hpt]
    have hmeas : ∀ j : ℕ, Measurable[observationFiltration X (j + m)] fun ω =>
        (if ((j + m : ℕ) : WithTop ℕ) < T ω then 1 - cusU P₀ P₁ m ω else 0) := by
      intro j
      refine Measurable.ite (hS (j + m)) ?_ measurable_const
      exact (measurable_const.sub (measurable_cusU P₀ P₁ m)).mono
        ((observationFiltration X).mono (Nat.le_add_left m j)) le_rfl
    rw [lintegral_tsum fun j =>
      ((hmeas j).mono ((observationFiltration X).le _) le_rfl).aemeasurable]
    refine tsum_congr fun j => ?_
    rw [lintegral_changePointLaw_eq P₀ P₁ h₁₀ h₀₁ (m + 1) (j + m) (hmeas j)]
    refine lintegral_congr fun ω => ?_
    rw [prod_cpDens_eq P₀ P₁ (Nat.le_add_left m j) ω]
  -- each time
  have hn : ∀ n : ℕ, ∑ m ∈ range (n + 1), g m n =
      ∫⁻ ω in {ω | (n : WithTop ℕ) < T ω}, max (cusU P₀ P₁ n ω) 1 ∂μ := by
    intro n
    have hmeas : ∀ m ∈ range (n + 1), Measurable fun ω : ℕ → X =>
        (if (n : WithTop ℕ) < T ω then 1 - cusU P₀ P₁ m ω else 0) *
          ∏ i ∈ Ico m n, cusLr P₀ P₁ (ω i) := by
      intro m _
      refine Measurable.mul (Measurable.ite ((observationFiltration X).le n _ (hS n))
        (measurable_const.sub (measurable_cusU' P₀ P₁ m)) measurable_const) ?_
      exact Finset.measurable_prod _ fun i _ => (measurable_cusLr P₀ P₁).comp
        (measurable_pi_apply i)
    rw [hg, ← lintegral_finsetSum _ hmeas,
      ← lintegral_indicator ((observationFiltration X).le n _ (hS n))]
    refine lintegral_congr fun ω => ?_
    by_cases hω : (n : WithTop ℕ) < T ω
    · rw [Set.indicator_of_mem (by exact hω), max_cusU_one_eq_sum]
      exact sum_congr rfl fun m _ => by rw [ite_eq_left hω]
    · rw [Set.indicator_of_notMem (by exact hω)]
      exact sum_eq_zero fun m _ => by rw [ite_eq_right hω, zero_mul]
  simp_rw [hm, ← tsum_ite_le_eq (g _)]
  rw [tsum_comm]
  unfold cusSum
  refine tsum_congr fun n => ?_
  rw [← hn, ← tsum_ite_lt_eq]
  exact tsum_congr fun m => by
    by_cases h : m < n + 1
    · rw [ite_eq_left (by omega : m ≤ n), ite_eq_left h]
    · rw [ite_eq_right (by omega : ¬ m ≤ n), ite_eq_right h]

/-- **Lower bound for Lorden's criterion.** For every stopping time `T`,
`E_∞[∑_{k<T} max(U_k, 1)] ≤ lordenDelay(T) · E_∞[∑_{k<T} (1 - U_k)⁺]`. -/
private theorem cusSum_max_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) :
    cusSum P₀ P₁ (fun u => max u 1) T ≤
      lordenDelay P₀ P₁ T * cusSum P₀ P₁ (fun u => 1 - u) T := by
  rw [cusSum_max_eq P₀ P₁ h₁₀ h₀₁ hT, cusSum, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun m => ?_
  set φ : (ℕ → X) → ℝ≥0∞ :=
    {ω | (m : WithTop ℕ) < T ω}.indicator fun ω => 1 - cusU P₀ P₁ m ω with hφ
  have hφm : Measurable[observationFiltration X m] φ :=
    (measurable_const.sub (measurable_cusU P₀ P₁ m)).indicator (measurableSet_natCast_lt hT m)
  have hpt : ∀ ω, (1 - cusU P₀ P₁ m ω) * (((show ℕ∞ from T ω) - m : ℕ∞) : ℝ≥0∞) =
      φ ω * (((show ℕ∞ from T ω) - m : ℕ∞) : ℝ≥0∞) := by
    intro ω
    by_cases hω : (m : WithTop ℕ) < T ω
    · rw [hφ, Set.indicator_of_mem (by exact hω)]
    · rw [enat_sub_eq_zero_of_not_lt hω, mul_zero, mul_zero]
  simp_rw [hpt]
  refine (lintegral_mul_le_lordenDelay P₀ P₁ hT m hφm).trans_eq ?_
  rw [lintegral_changePointLaw_eq_of_lt P₀ P₁ h₁₀ h₀₁ (Nat.lt_succ_self m) hφm, hφ,
    lintegral_indicator ((observationFiltration X).le m _ (measurableSet_natCast_lt hT m))]

/-! ### The CUSUM rule restarted at a change point -/

private theorem pageCusum_nonneg (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (n : ℕ) (ω : ℕ → X) :
    0 ≤ pageCusum P₀ P₁ h₁₀ h₀₁ n ω := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

/-- **Page's CUSUM statistic is adapted.** For probability laws `P₀` and `P₁`, mutually
absolutely continuous, `Wₙ` is measurable with respect to `σ(X₁, …, Xₙ)`, so CUSUM decides after
`n` observations from those observations only (Veeravalli–Banerjee, equation (45)). -/
theorem adapted_pageCusum (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) :
    Adapted (observationFiltration X) (pageCusum P₀ P₁ h₁₀ h₀₁) := by
  intro n
  change Measurable[observationFiltration X n] (pageCusum P₀ P₁ h₁₀ h₀₁ n)
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ((ih.mono ((observationFiltration X).mono (Nat.le_succ n)) le_rfl).add
      ((measurable_llr P₁ P₀).comp
        (measurable_coord_observationFiltration (Nat.lt_add_one n)))).max measurable_const

/-- **The CUSUM alarm is a stopping time** of the observations, possibly infinite, for probability
laws `P₀` and `P₁`, mutually absolutely continuous, and any threshold `c`
(Veeravalli–Banerjee, equation (43)). -/
theorem isStoppingTime_cusumTime (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (c : ℝ) :
    IsStoppingTime (observationFiltration X) (cusumTime P₀ P₁ h₁₀ h₀₁ c) :=
  (adapted_pageCusum P₀ P₁ h₁₀ h₀₁).isStoppingTime_hittingAfter measurableSet_Ici

/-- Started afresh at time `m`, Page's statistic is at most the original one. -/
private theorem pageCusum_shift_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (m n : ℕ) (ω : ℕ → X) :
    pageCusum P₀ P₁ h₁₀ h₀₁ n (fun i => ω (i + m)) ≤ pageCusum P₀ P₁ h₁₀ h₀₁ (n + m) ω := by
  induction n with
  | zero => simpa [pageCusum] using pageCusum_nonneg P₀ P₁ h₁₀ h₀₁ m ω
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [pageCusum]
    exact max_le_max (add_le_add_left ih _) le_rfl

/-- If Page's statistic vanishes at time `m`, restarting it there changes nothing. -/
private theorem pageCusum_shift_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {m : ℕ} {ω : ℕ → X}
    (h0 : pageCusum P₀ P₁ h₁₀ h₀₁ m ω = 0) (n : ℕ) :
    pageCusum P₀ P₁ h₁₀ h₀₁ n (fun i => ω (i + m)) = pageCusum P₀ P₁ h₁₀ h₀₁ (n + m) ω := by
  induction n with
  | zero => simp [pageCusum, h0]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [pageCusum, ih]

private theorem withTop_toENNReal_eq_tsum (t : WithTop ℕ) :
    ((show ℕ∞ from t) : ℝ≥0∞) = ∑' j : ℕ, if (j : WithTop ℕ) < t then 1 else 0 :=
  enat_toENNReal_eq_tsum t

private theorem toENNReal_sub_le {t t' : WithTop ℕ} {m : ℕ}
    (h : ∀ j : ℕ, ((j + m : ℕ) : WithTop ℕ) < t → (j : WithTop ℕ) < t') :
    (((show ℕ∞ from t) - m : ℕ∞) : ℝ≥0∞) ≤ ((show ℕ∞ from t') : ℝ≥0∞) := by
  rw [enat_sub_eq_tsum, withTop_toENNReal_eq_tsum]
  refine tsum_le_tsum fun j => ?_
  by_cases hj : ((j + m : ℕ) : WithTop ℕ) < t
  · rw [ite_eq_left hj, ite_eq_left (h j hj)]
  · rw [ite_eq_right hj]
    exact zero_le

private theorem le_toENNReal_sub {t t' : WithTop ℕ} {m : ℕ}
    (h : ∀ j : ℕ, (j : WithTop ℕ) < t' → ((j + m : ℕ) : WithTop ℕ) < t) :
    ((show ℕ∞ from t') : ℝ≥0∞) ≤ (((show ℕ∞ from t) - m : ℕ∞) : ℝ≥0∞) := by
  rw [enat_sub_eq_tsum, withTop_toENNReal_eq_tsum]
  refine tsum_le_tsum fun j => ?_
  by_cases hj : (j : WithTop ℕ) < t'
  · rw [ite_eq_left hj, ite_eq_left (h j hj)]
  · rw [ite_eq_right hj]
    exact zero_le

/-- The remaining delay of CUSUM after time `m` is at most the delay of CUSUM restarted at
time `m`. -/
private theorem lt_cusumTime_shift (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (c : ℝ) (m : ℕ) (ω : ℕ → X)
    (j : ℕ) (hj : ((j + m : ℕ) : WithTop ℕ) < cusumTime P₀ P₁ h₁₀ h₀₁ c ω) :
    (j : WithTop ℕ) < cusumTime P₀ P₁ h₁₀ h₀₁ c (fun i => ω (i + m)) := by
  set u := pageCusum P₀ P₁ h₁₀ h₀₁
  change ((j + m : ℕ) : WithTop ℕ) < hittingAfter u (Set.Ici c) 1 ω at hj
  change (j : WithTop ℕ) < hittingAfter u (Set.Ici c) 1 (fun i => ω (i + m))
  by_contra hcon
  obtain ⟨i, hi, hiu⟩ := hittingAfter_le_iff.1 (not_lt.1 hcon)
  simp only [Set.mem_Icc, Nat.cast_id] at hi
  have hc : c ≤ u (i + m) ω := (Set.mem_Ici.1 hiu).trans (pageCusum_shift_le P₀ P₁ h₁₀ h₀₁ m i ω)
  have hle : hittingAfter u (Set.Ici c) 1 ω ≤ ((i + m : ℕ) : WithTop ℕ) :=
    hittingAfter_le_of_mem (i := i + m) (by omega) hc
  have : ((i + m : ℕ) : WithTop ℕ) ≤ ((j + m : ℕ) : WithTop ℕ) := by
    exact_mod_cast (by omega : i + m ≤ j + m)
  exact absurd (hj.trans_le (hle.trans this)) (lt_irrefl _)

/-- If Page's statistic vanishes at time `m` before the alarm, CUSUM restarted at time `m`
raises its alarm no later than CUSUM does. The two alarms coincide, by `lt_cusumTime_shift`; only
this inequality is needed. -/
private theorem lt_cusumTime_of_shift (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (c : ℝ) {m : ℕ} {ω : ℕ → X}
    (h0 : pageCusum P₀ P₁ h₁₀ h₀₁ m ω = 0) (hm : (m : WithTop ℕ) < cusumTime P₀ P₁ h₁₀ h₀₁ c ω)
    (j : ℕ) (hj : (j : WithTop ℕ) < cusumTime P₀ P₁ h₁₀ h₀₁ c (fun i => ω (i + m))) :
    ((j + m : ℕ) : WithTop ℕ) < cusumTime P₀ P₁ h₁₀ h₀₁ c ω := by
  set u := pageCusum P₀ P₁ h₁₀ h₀₁
  change (j : WithTop ℕ) < hittingAfter u (Set.Ici c) 1 (fun i => ω (i + m)) at hj
  change (m : WithTop ℕ) < hittingAfter u (Set.Ici c) 1 ω at hm
  change ((j + m : ℕ) : WithTop ℕ) < hittingAfter u (Set.Ici c) 1 ω
  by_contra hcon
  obtain ⟨i, hi, hiu⟩ := hittingAfter_le_iff.1 (not_lt.1 hcon)
  simp only [Set.mem_Icc, Nat.cast_id] at hi
  have hmi : m < i := by
    by_contra hmi
    have hle : hittingAfter u (Set.Ici c) 1 ω ≤ (i : WithTop ℕ) :=
      hittingAfter_le_of_mem (i := i) hi.1 hiu
    have : (i : WithTop ℕ) ≤ (m : WithTop ℕ) := by exact_mod_cast (not_lt.1 hmi)
    exact absurd (hm.trans_le (hle.trans this)) (lt_irrefl _)
  have hc : c ≤ u (i - m) (fun i => ω (i + m)) := by
    have h := pageCusum_shift_eq P₀ P₁ h₁₀ h₀₁ h0 (i - m)
    rw [Nat.sub_add_cancel hmi.le] at h
    change c ≤ pageCusum P₀ P₁ h₁₀ h₀₁ (i - m) (fun i => ω (i + m))
    rw [h]
    exact hiu
  have hle : hittingAfter u (Set.Ici c) 1 (fun i => ω (i + m)) ≤ ((i - m : ℕ) : WithTop ℕ) :=
    hittingAfter_le_of_mem (i := i - m) (by omega) hc
  have : ((i - m : ℕ) : WithTop ℕ) ≤ (j : WithTop ℕ) := by
    exact_mod_cast (by omega : i - m ≤ j)
  exact absurd (hj.trans_le (hle.trans this)) (lt_irrefl _)

/-- The expected delay `D = E₁[N_c]` of CUSUM when every observation has law `P₁`. -/
private noncomputable def cusDelay (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((show ℕ∞ from cusumTime P₀ P₁ h₁₀ h₀₁ c ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₁)

/-- Under the change-point law with change at `m + 1`, a function of the first `m`
observations is independent of CUSUM restarted at time `m`, whose mean is `D`. -/
private theorem lintegral_mul_cusumTime_shift (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (c : ℝ) (m : ℕ)
    {φ : (ℕ → X) → ℝ≥0∞} (hφ : Measurable[observationFiltration X m] φ) :
    ∫⁻ ω, φ ω * ((show ℕ∞ from cusumTime P₀ P₁ h₁₀ h₀₁ c (fun i => ω (i + m))) : ℝ≥0∞)
      ∂changePointLaw P₀ P₁ (m + 1) =
      (∫⁻ ω, φ ω ∂changePointLaw P₀ P₁ (m + 1)) * cusDelay P₀ P₁ h₁₀ h₀₁ c := by
  unfold changePointLaw
  rw [lintegral_mul_comp_shift _ m hφ (measurable_enat (isStoppingTime_cusumTime P₀ P₁ h₁₀ h₀₁ c))]
  unfold cusDelay
  congr 2
  congr 1
  funext i
  exact ite_eq_right (by omega)

/-- **The delay of CUSUM.** Lorden's criterion of the CUSUM alarm is at most `D = E₁[N_c]`. -/
private theorem lordenDelay_cusumTime_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (c : ℝ) :
    lordenDelay P₀ P₁ (cusumTime P₀ P₁ h₁₀ h₀₁ c) ≤ cusDelay P₀ P₁ h₁₀ h₀₁ c := by
  refine iSup₂_le fun ν hν => iSup₂_le fun F hF => iSup_le fun hF0 => ?_
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  have hF' : MeasurableSet[observationFiltration X m] F := by simpa using hF
  have hFm : MeasurableSet F := (observationFiltration X).le m F hF'
  rw [ENNReal.div_le_iff hF0.ne' (measure_ne_top _ _)]
  set N := cusumTime P₀ P₁ h₁₀ h₀₁ c
  calc ∫⁻ ω in F, (((show ℕ∞ from N ω) + 1 - ((m + 1 : ℕ) : ℕ∞) : ℕ∞) : ℝ≥0∞)
        ∂changePointLaw P₀ P₁ (m + 1)
      = ∫⁻ ω in F, (((show ℕ∞ from N ω) - m : ℕ∞) : ℝ≥0∞) ∂changePointLaw P₀ P₁ (m + 1) :=
        lintegral_congr fun ω => congrArg (fun t : ℕ∞ => (t : ℝ≥0∞)) (enat_add_one_sub (N ω) m)
    _ ≤ ∫⁻ ω in F, ((show ℕ∞ from N (fun i => ω (i + m))) : ℝ≥0∞)
        ∂changePointLaw P₀ P₁ (m + 1) :=
        lintegral_mono fun ω => toENNReal_sub_le (lt_cusumTime_shift P₀ P₁ h₁₀ h₀₁ c m ω)
    _ = ∫⁻ ω, F.indicator 1 ω * ((show ℕ∞ from N (fun i => ω (i + m))) : ℝ≥0∞)
        ∂changePointLaw P₀ P₁ (m + 1) := by
        rw [← lintegral_indicator hFm]
        refine lintegral_congr fun ω => ?_
        by_cases hω : ω ∈ F <;> simp [hω]
    _ = cusDelay P₀ P₁ h₁₀ h₀₁ c * changePointLaw P₀ P₁ (m + 1) F := by
        rw [lintegral_mul_cusumTime_shift P₀ P₁ h₁₀ h₀₁ c m (φ := F.indicator 1)
          (Measurable.indicator (by exact measurable_const) hF'), lintegral_indicator_one hFm,
          mul_comm]

/-- **One half of the CUSUM identity.** `E_∞[∑_{k<N} max(U_k, 1)] ≥ D E_∞[∑_{k<N} (1 - U_k)⁺]`:
at every change point where `U < 1`, CUSUM restarted there raises its alarm no later than CUSUM,
and its delay has mean `D`. -/
private theorem mul_cusSum_le_cusSum_max (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (c : ℝ) :
    cusDelay P₀ P₁ h₁₀ h₀₁ c * cusSum P₀ P₁ (fun u => 1 - u) (cusumTime P₀ P₁ h₁₀ h₀₁ c) ≤
      cusSum P₀ P₁ (fun u => max u 1) (cusumTime P₀ P₁ h₁₀ h₀₁ c) := by
  set N := cusumTime P₀ P₁ h₁₀ h₀₁ c
  have hN := isStoppingTime_cusumTime P₀ P₁ h₁₀ h₀₁ c
  rw [cusSum_max_eq P₀ P₁ h₁₀ h₀₁ hN, cusSum, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun m => ?_
  set φ : (ℕ → X) → ℝ≥0∞ :=
    {ω | (m : WithTop ℕ) < N ω}.indicator fun ω => 1 - cusU P₀ P₁ m ω with hφ
  have hφm : Measurable[observationFiltration X m] φ :=
    (measurable_const.sub (measurable_cusU P₀ P₁ m)).indicator (measurableSet_natCast_lt hN m)
  have hpt : ∀ ω, φ ω * ((show ℕ∞ from N (fun i => ω (i + m))) : ℝ≥0∞) ≤
      (1 - cusU P₀ P₁ m ω) * (((show ℕ∞ from N ω) - m : ℕ∞) : ℝ≥0∞) := by
    intro ω
    by_cases hω : (m : WithTop ℕ) < N ω
    · rw [hφ, Set.indicator_of_mem (by exact hω)]
      by_cases hU : 1 ≤ cusU P₀ P₁ m ω
      · simp [tsub_eq_zero_of_le hU]
      · have h0 : pageCusum P₀ P₁ h₁₀ h₀₁ m ω = 0 := by
          have hmax := max_cusU_one P₀ P₁ h₁₀ h₀₁ m ω
          rw [max_eq_right (not_le.1 hU).le, eq_comm, ENNReal.ofReal_eq_one,
            Real.exp_eq_one_iff] at hmax
          exact hmax
        gcongr
        exact le_toENNReal_sub (lt_cusumTime_of_shift P₀ P₁ h₁₀ h₀₁ c h0 hω)
    · rw [hφ, Set.indicator_of_notMem (by exact hω), zero_mul]
      exact zero_le
  calc cusDelay P₀ P₁ h₁₀ h₀₁ c * ∫⁻ ω in {ω | (m : WithTop ℕ) < N ω}, 1 - cusU P₀ P₁ m ω
        ∂Measure.infinitePi (fun _ : ℕ => P₀)
      = (∫⁻ ω, φ ω ∂changePointLaw P₀ P₁ (m + 1)) * cusDelay P₀ P₁ h₁₀ h₀₁ c := by
        rw [lintegral_changePointLaw_eq_of_lt P₀ P₁ h₁₀ h₀₁ (Nat.lt_succ_self m) hφm, hφ,
          lintegral_indicator ((observationFiltration X).le m _
            (measurableSet_natCast_lt hN m)), mul_comm]
    _ = ∫⁻ ω, φ ω * ((show ℕ∞ from N (fun i => ω (i + m))) : ℝ≥0∞)
        ∂changePointLaw P₀ P₁ (m + 1) :=
        (lintegral_mul_cusumTime_shift P₀ P₁ h₁₀ h₀₁ c m hφm).symm
    _ ≤ _ := lintegral_mono hpt

/-! ### The running cost of the discounted problems -/

/-- Running cost `r(u) = max(u, 1) + D min(u, 1)` of the discounted problems. -/
private noncomputable def cusCost (D u : ℝ≥0∞) : ℝ≥0∞ :=
  max u 1 + D * min u 1

private theorem monotone_cusCost (D : ℝ≥0∞) : Monotone (cusCost D) := fun _ _ h => by
  unfold cusCost
  gcongr

private theorem measurable_cusCost (D : ℝ≥0∞) : Measurable (cusCost D) :=
  (monotone_cusCost D).measurable

private theorem cusSum_cusCost (P₀ P₁ : Measure X) (D : ℝ≥0∞) (T : (ℕ → X) → WithTop ℕ) :
    cusSum P₀ P₁ (cusCost D) T =
      cusSum P₀ P₁ (fun u => max u 1) T + D * cusSum P₀ P₁ (fun u => min u 1) T := by
  rw [← cusSum_const_mul P₀ P₁ (f := fun u => min u 1) (measurable_id.min measurable_const),
    ← cusSum_add P₀ P₁ (f := fun u => max u 1) (g := fun u => D * min u 1)
      (measurable_id.max measurable_const)]
  rfl

private theorem cusSum_one_eq (P₀ P₁ : Measure X) (T : (ℕ → X) → WithTop ℕ) :
    cusSum P₀ P₁ (fun _ => 1) T =
      cusSum P₀ P₁ (fun u => min u 1) T + cusSum P₀ P₁ (fun u => 1 - u) T := by
  rw [← cusSum_add P₀ P₁ (f := fun u => min u 1) (g := fun u => 1 - u)
    (measurable_id.min measurable_const)]
  congr 1
  funext u
  rcases le_total u 1 with h | h
  · rw [min_eq_left h, add_tsub_cancel_of_le h]
  · rw [min_eq_right h, tsub_eq_zero_of_le h, add_zero]

/-- For CUSUM, `E_∞[∑_{k<N} r(U_k)] ≥ D E_∞[N]`. -/
private theorem mul_lintegral_le_cusSum_cusCost (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (c : ℝ) :
    cusDelay P₀ P₁ h₁₀ h₀₁ c * cusSum P₀ P₁ (fun _ => 1) (cusumTime P₀ P₁ h₁₀ h₀₁ c) ≤
      cusSum P₀ P₁ (cusCost (cusDelay P₀ P₁ h₁₀ h₀₁ c)) (cusumTime P₀ P₁ h₁₀ h₀₁ c) := by
  rw [cusSum_cusCost, cusSum_one_eq, mul_add, add_comm]
  exact add_le_add_left (mul_cusSum_le_cusSum_max P₀ P₁ h₁₀ h₀₁ c) _

/-- From `E_∞[∑_{k<T} r(U_k)] ≥ D E_∞[T]` to `E_∞[∑_{k<T} max(U_k, 1)] ≥ D E_∞[∑_{k<T} (1 - U_k)⁺]`,
when `D` and `E_∞[T]` are finite. -/
private theorem mul_cusSum_le_of_cusCost (P₀ P₁ : Measure X) {D : ℝ≥0∞} (hD : D ≠ ∞)
    {T : (ℕ → X) → WithTop ℕ} (hET : cusSum P₀ P₁ (fun _ => 1) T ≠ ∞)
    (h : D * cusSum P₀ P₁ (fun _ => 1) T ≤ cusSum P₀ P₁ (cusCost D) T) :
    D * cusSum P₀ P₁ (fun u => 1 - u) T ≤ cusSum P₀ P₁ (fun u => max u 1) T := by
  rw [cusSum_cusCost, cusSum_one_eq, mul_add, add_comm (cusSum P₀ P₁ (fun u => max u 1) T)] at h
  have hM : D * cusSum P₀ P₁ (fun u => min u 1) T ≠ ∞ := by
    refine ENNReal.mul_ne_top hD (ne_top_of_le_ne_top hET ?_)
    rw [cusSum_one_eq]
    exact le_self_add
  exact (ENNReal.add_le_add_iff_left hM).1 h

/-! ### Finiteness of the mean times -/

/-- If `P₀ ≠ P₁`, the log-likelihood ratio is at least some `δ > 0` with positive
`P₀`-probability. -/
private theorem exists_measure_le_llr_pos (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (hne : P₀ ≠ P₁) :
    ∃ δ : ℝ, 0 < δ ∧ 0 < P₀ {x | δ ≤ llr P₁ P₀ x} := by
  have hpos : P₀ {x | 1 < P₁.rnDeriv P₀ x} ≠ 0 := by
    intro h0
    have hle : ∀ᵐ x ∂P₀, P₁.rnDeriv P₀ x ≤ 1 := by
      rw [ae_iff]
      simpa only [not_le] using h0
    have hA : ∀ A, MeasurableSet A → P₁ A ≤ P₀ A := by
      intro A hA
      rw [← Measure.withDensity_rnDeriv_eq P₁ P₀ h₁₀, withDensity_apply _ hA]
      calc ∫⁻ x in A, P₁.rnDeriv P₀ x ∂P₀ ≤ ∫⁻ _ in A, 1 ∂P₀ :=
            lintegral_mono_ae (ae_restrict_of_ae hle)
        _ = P₀ A := by simp
    refine hne (Measure.ext fun A hA' => le_antisymm ?_ (hA A hA'))
    have hc := hA Aᶜ hA'.compl
    rw [prob_compl_eq_one_sub hA', prob_compl_eq_one_sub hA'] at hc
    exact (ENNReal.sub_le_sub_iff_left prob_le_one ENNReal.one_ne_top).1 hc
  by_contra hcon
  push Not at hcon
  refine hpos (measure_mono_null (t := (⋃ k : ℕ, {x | 1 / ((k : ℝ) + 1) ≤ llr P₁ P₀ x}) ∪
    {x | P₁.rnDeriv P₀ x = ∞}) ?_ ?_)
  · intro x (hx : 1 < P₁.rnDeriv P₀ x)
    by_cases htop : P₁.rnDeriv P₀ x = ∞
    · exact Or.inr htop
    refine Or.inl (Set.mem_iUnion.2 ?_)
    have h1 : 1 < (P₁.rnDeriv P₀ x).toReal := by
      rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top htop).2 hx
    have hlog : 0 < llr P₁ P₀ x := Real.log_pos h1
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hlog
    exact ⟨k, hk.le⟩
  · refine measure_union_null (measure_iUnion_null fun k => ?_) ?_
    · exact le_antisymm (hcon _ (by positivity)) zero_le
    · have := Measure.rnDeriv_lt_top P₁ P₀
      rw [ae_iff] at this
      simpa only [not_lt, top_le_iff] using this

/-- On `{δ ≤ log L}` with `δ > 0`, the likelihood ratio is at least `1`. -/
private theorem one_le_rnDeriv_of_le_llr (P₀ P₁ : Measure X) {δ : ℝ} (hδ : 0 < δ) {x : X}
    (hx : δ ≤ llr P₁ P₀ x) : 1 ≤ P₁.rnDeriv P₀ x := by
  have hlog : 0 < Real.log (P₁.rnDeriv P₀ x).toReal := hδ.trans_le hx
  have h1 : 1 < (P₁.rnDeriv P₀ x).toReal := (Real.log_pos_iff ENNReal.toReal_nonneg).1 hlog
  have htop : P₁.rnDeriv P₀ x ≠ ∞ := fun h => by
    rw [h, ENNReal.toReal_top] at h1
    linarith
  rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal h1.le

private theorem measure_le_llr_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) {δ : ℝ} (hδ : 0 < δ) :
    P₀ {x | δ ≤ llr P₁ P₀ x} ≤ P₁ {x | δ ≤ llr P₁ P₀ x} := by
  have hG : MeasurableSet {x | δ ≤ llr P₁ P₀ x} := measurableSet_le measurable_const
    (measurable_llr _ _)
  calc P₀ {x | δ ≤ llr P₁ P₀ x} = ∫⁻ _ in {x | δ ≤ llr P₁ P₀ x}, 1 ∂P₀ := by simp
    _ ≤ ∫⁻ x in {x | δ ≤ llr P₁ P₀ x}, P₁.rnDeriv P₀ x ∂P₀ :=
        setLIntegral_mono (Measure.measurable_rnDeriv _ _) fun x hx =>
          one_le_rnDeriv_of_le_llr P₀ P₁ hδ hx
    _ = P₁ {x | δ ≤ llr P₁ P₀ x} := by
        rw [← withDensity_apply _ hG, Measure.withDensity_rnDeriv_eq P₁ P₀ h₁₀]

/-- A run of `j` observations with log-likelihood ratio at least `δ` raises Page's statistic to
at least `j δ`. -/
private theorem mul_le_pageCusum (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {δ : ℝ} (n : ℕ) (ω : ℕ → X) :
    ∀ j : ℕ, (∀ i < j, δ ≤ llr P₁ P₀ (ω (n + i))) → j * δ ≤ pageCusum P₀ P₁ h₁₀ h₀₁ (n + j) ω
  | 0, _ => by simpa using pageCusum_nonneg P₀ P₁ h₁₀ h₀₁ n ω
  | j + 1, h => by
    have ih := mul_le_pageCusum P₀ P₁ h₁₀ h₀₁ n ω j fun i hi => h i (by omega)
    have hj := h j (by omega)
    rw [show n + (j + 1) = (n + j) + 1 by omega]
    simp only [pageCusum]
    push_cast
    exact le_max_of_le_left (by linarith)

/-- **Finite mean time to alarm (blocks argument).** If a single observation has
log-likelihood ratio at least `δ > 0` with positive `Q`-probability, CUSUM has finite mean
under `Q^ℕ`. -/
private theorem lintegral_cusumTime_lt_top (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (c : ℝ) (Q : Measure X)
    [IsProbabilityMeasure Q] {δ : ℝ} (hδ : 0 < δ) (hQ : 0 < Q {x | δ ≤ llr P₁ P₀ x}) :
    ∫⁻ ω, ((show ℕ∞ from cusumTime P₀ P₁ h₁₀ h₀₁ c ω) : ℝ≥0∞)
      ∂Measure.infinitePi (fun _ : ℕ => Q) < ∞ := by
  set N := cusumTime P₀ P₁ h₁₀ h₀₁ c
  set μ := Measure.infinitePi (fun _ : ℕ => Q)
  have hN := isStoppingTime_cusumTime P₀ P₁ h₁₀ h₀₁ c
  set G := {x | δ ≤ llr P₁ P₀ x}
  have hG : MeasurableSet G := measurableSet_le measurable_const (measurable_llr _ _)
  set m := ⌈c / δ⌉₊ + 1 with hm
  have hm0 : m ≠ 0 := by omega
  have : NeZero m := ⟨hm0⟩
  have hmδ : c ≤ m * δ := by
    have := Nat.le_ceil (c / δ)
    rw [div_le_iff₀ hδ] at this
    have : (⌈c / δ⌉₊ : ℝ) * δ ≤ m * δ := by
      gcongr
      rw [hm]
      linarith
    linarith
  set q := Q G ^ m
  have hq0 : q ≠ 0 := pow_ne_zero _ hQ.ne'
  have hq1 : q ≤ 1 := pow_le_one₀ zero_le prob_le_one
  set B : Set (ℕ → X) := {ω | ∀ j < m, ω j ∈ G}
  have hB : MeasurableSet B := by
    have : B = ⋂ j ∈ range m, (fun ω : ℕ → X => ω j) ⁻¹' G := by
      ext ω
      simp [B]
    rw [this]
    exact Finset.measurableSet_biInter _ fun j _ => measurable_pi_apply j hG
  have hμB : μ B = q := by
    have : B = Set.pi (range m : Set ℕ) fun _ => G := by
      ext ω
      simp [B]
    rw [this, Measure.infinitePi_pi _ fun _ _ => hG, prod_const, card_range]
  have hS : ∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < N ω} := fun n =>
    (observationFiltration X).le n _ (measurableSet_natCast_lt hN n)
  -- geometric decay over blocks
  have hblock : ∀ k : ℕ, μ {ω | ((k * m : ℕ) : WithTop ℕ) < N ω} ≤ (1 - q) ^ k := by
    intro k
    induction k with
    | zero => simpa using prob_le_one
    | succ k ih =>
      have hsub : {ω | (((k + 1) * m : ℕ) : WithTop ℕ) < N ω} ⊆
          {ω | ((k * m : ℕ) : WithTop ℕ) < N ω} ∩ (fun ω i => ω (i + k * m)) ⁻¹' Bᶜ := by
        intro ω hω
        have hkm : ((k * m : ℕ) : WithTop ℕ) ≤ (((k + 1) * m : ℕ) : WithTop ℕ) := by
          exact_mod_cast Nat.mul_le_mul_right m (Nat.le_succ k)
        refine ⟨hkm.trans_lt hω, ?_⟩
        intro hBω
        have hc : c ≤ pageCusum P₀ P₁ h₁₀ h₀₁ (k * m + m) ω := by
          refine hmδ.trans (mul_le_pageCusum P₀ P₁ h₁₀ h₀₁ (k * m) ω m fun i hi => ?_)
          have h' : ω (i + k * m) ∈ G := hBω i hi
          rwa [add_comm] at h'
        have hle : N ω ≤ (((k + 1) * m : ℕ) : WithTop ℕ) :=
          hittingAfter_le_of_mem (i := (k + 1) * m) (by nlinarith [Nat.pos_of_ne_zero hm0])
            (by rw [show (k + 1) * m = k * m + m by ring]; exact hc)
        exact absurd (hω.trans_le hle) (lt_irrefl _)
      have hind : μ ({ω | ((k * m : ℕ) : WithTop ℕ) < N ω} ∩
          (fun ω i => ω (i + k * m)) ⁻¹' Bᶜ) =
          μ {ω | ((k * m : ℕ) : WithTop ℕ) < N ω} * (1 - q) := by
        have h := lintegral_mul_comp_shift (fun _ : ℕ => Q) (k * m)
          (φ := {ω | ((k * m : ℕ) : WithTop ℕ) < N ω}.indicator 1)
          (Measurable.indicator (by exact measurable_const) (measurableSet_natCast_lt hN _))
          (g := Bᶜ.indicator 1) (measurable_one.indicator hB.compl)
        rw [lintegral_indicator_one (hS _), lintegral_indicator_one hB.compl,
          prob_compl_eq_one_sub hB, hμB] at h
        rw [← h, ← lintegral_indicator_one ((hS _).inter (hB.compl.preimage
          (measurable_pi_iff.2 fun j => measurable_pi_apply (j + k * m))))]
        refine lintegral_congr fun ω => ?_
        simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, Pi.one_apply]
        split_ifs <;> simp_all
      calc μ {ω | (((k + 1) * m : ℕ) : WithTop ℕ) < N ω}
          ≤ μ ({ω | ((k * m : ℕ) : WithTop ℕ) < N ω} ∩ (fun ω i => ω (i + k * m)) ⁻¹' Bᶜ) :=
            measure_mono hsub
        _ = μ {ω | ((k * m : ℕ) : WithTop ℕ) < N ω} * (1 - q) := hind
        _ ≤ (1 - q) ^ k * (1 - q) := by gcongr
        _ = (1 - q) ^ (k + 1) := (pow_succ _ _).symm
  have hterm : ∀ n : ℕ, μ {ω | (n : WithTop ℕ) < N ω} ≤ (1 - q) ^ (n / m) := by
    intro n
    refine (measure_mono (s := {ω | (n : WithTop ℕ) < N ω})
      (t := {ω | ((n / m * m : ℕ) : WithTop ℕ) < N ω}) fun ω hω => ?_).trans (hblock (n / m))
    have hle : ((n / m * m : ℕ) : WithTop ℕ) ≤ (n : WithTop ℕ) := by
      exact_mod_cast Nat.div_mul_le_self n m
    exact hle.trans_lt hω
  rw [lintegral_enat_eq_tsum μ hS]
  calc ∑' n : ℕ, μ {ω | (n : WithTop ℕ) < N ω} ≤ ∑' n : ℕ, (1 - q) ^ (n / m) :=
        tsum_le_tsum hterm
    _ = ∑' p : ℕ × Fin m, (1 - q) ^ p.1 := by
        rw [← (Nat.divModEquiv m).symm.tsum_eq]
        refine tsum_congr fun p => ?_
        congr 1
        simp only [Nat.divModEquiv_symm_apply]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero hm0),
          Nat.div_eq_of_lt p.2.is_lt, Nat.zero_add]
    _ = m * q⁻¹ := by
        rw [tsum_prod (f := fun (a : ℕ) (_ : Fin m) => (1 - q) ^ a)]
        simp only [tsum_fintype, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.sub_sub_cancel ENNReal.one_ne_top hq1]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top m)
        (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hq0))

/-! ### The discounted problems -/

/-- Backward induction with horizon `n` for the discounted problem in the CUSUM chain:
stopping costs `1`, observing once more costs `θ r(u)` and discounts the future by `β`, and the
next observation is drawn from `P₀`. -/
private noncomputable def cusIter (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) : ℕ → ℝ≥0∞ → ℝ≥0∞
  | 0 => fun _ => 1
  | n + 1 => fun u => min 1 (θ * cusCost D u +
      β * ∫⁻ x, cusIter P₀ P₁ β D θ n (cusStep P₀ P₁ u x) ∂P₀)

private theorem cusIter_le_one (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) (n : ℕ) (u : ℝ≥0∞) :
    cusIter P₀ P₁ β D θ n u ≤ 1 := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_left _ _

private theorem cusIter_mono (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) (n : ℕ) :
    Monotone (cusIter P₀ P₁ β D θ n) := by
  induction n with
  | zero => exact fun _ _ _ => le_rfl
  | succ n ih =>
    intro u u' h
    refine min_le_min_left _ (add_le_add ?_ ?_)
    · gcongr
      exact monotone_cusCost D h
    · gcongr with x
      exact ih (cusStep_mono P₀ P₁ h x)

private theorem measurable_cusIter_comp (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) (n : ℕ)
    (u : ℝ≥0∞) : Measurable fun x => cusIter P₀ P₁ β D θ n (cusStep P₀ P₁ u x) :=
  (cusIter_mono P₀ P₁ β D θ n).measurable.comp (measurable_cusStep_right P₀ P₁ u)

private theorem cusIter_succ_le (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) (n : ℕ) (u : ℝ≥0∞) :
    cusIter P₀ P₁ β D θ (n + 1) u ≤ cusIter P₀ P₁ β D θ n u := by
  induction n generalizing u with
  | zero => exact min_le_left _ _
  | succ n ih =>
    refine min_le_min_left _ (add_le_add le_rfl ?_)
    gcongr with x
    exact ih _

private theorem antitone_cusIter (P₀ P₁ : Measure X) (β D θ u : ℝ≥0∞) :
    Antitone fun n => cusIter P₀ P₁ β D θ n u :=
  antitone_nat_of_succ_le fun n => cusIter_succ_le P₀ P₁ β D θ n u

private theorem cusIter_mono_cost (P₀ P₁ : Measure X) (β D : ℝ≥0∞) {θ θ' : ℝ≥0∞}
    (h : θ ≤ θ') (n : ℕ) (u : ℝ≥0∞) : cusIter P₀ P₁ β D θ n u ≤ cusIter P₀ P₁ β D θ' n u := by
  induction n generalizing u with
  | zero => exact le_rfl
  | succ n ih =>
    refine min_le_min_left _ (add_le_add (by gcongr) ?_)
    gcongr with x
    exact ih _

private theorem cusIter_cost_mul_le (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) (n : ℕ) {t : ℝ≥0∞}
    (ht : 1 ≤ t) (u : ℝ≥0∞) :
    cusIter P₀ P₁ β D (t * θ) n u ≤ t * cusIter P₀ P₁ β D θ n u := by
  induction n generalizing u with
  | zero => exact le_mul_of_one_le_left' ht
  | succ n ih =>
    simp only [cusIter]
    rw [mul_min, mul_one]
    refine min_le_min ht ?_
    rw [mul_add]
    refine add_le_add (le_of_eq (by ring)) ?_
    calc β * ∫⁻ x, cusIter P₀ P₁ β D (t * θ) n (cusStep P₀ P₁ u x) ∂P₀
        ≤ β * ∫⁻ x, t * cusIter P₀ P₁ β D θ n (cusStep P₀ P₁ u x) ∂P₀ := by
          gcongr with x
          exact ih _
      _ = t * (β * ∫⁻ x, cusIter P₀ P₁ β D θ n (cusStep P₀ P₁ u x) ∂P₀) := by
          rw [lintegral_const_mul _ (measurable_cusIter_comp P₀ P₁ β D θ n u)]
          ring

/-- The value function of the discounted problem with unbounded horizon. -/
private noncomputable def cusValue (P₀ P₁ : Measure X) (β D θ u : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ n, cusIter P₀ P₁ β D θ n u

/-- The expected cost of observing once more and then acting optimally. -/
private noncomputable def cusCont (P₀ P₁ : Measure X) (β D θ u : ℝ≥0∞) : ℝ≥0∞ :=
  θ * cusCost D u + β * ∫⁻ x, cusValue P₀ P₁ β D θ (cusStep P₀ P₁ u x) ∂P₀

private theorem cusValue_le_one (P₀ P₁ : Measure X) (β D θ u : ℝ≥0∞) :
    cusValue P₀ P₁ β D θ u ≤ 1 :=
  (iInf_le _ 0).trans (cusIter_le_one P₀ P₁ β D θ 0 u)

private theorem cusValue_mono (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) :
    Monotone (cusValue P₀ P₁ β D θ) :=
  fun _ _ h => iInf_mono fun n => cusIter_mono P₀ P₁ β D θ n h

private theorem measurable_cusValue (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) :
    Measurable (cusValue P₀ P₁ β D θ) :=
  (cusValue_mono P₀ P₁ β D θ).measurable

private theorem measurable_cusValue_comp (P₀ P₁ : Measure X) (β D θ u : ℝ≥0∞) :
    Measurable fun x => cusValue P₀ P₁ β D θ (cusStep P₀ P₁ u x) :=
  (measurable_cusValue P₀ P₁ β D θ).comp (measurable_cusStep_right P₀ P₁ u)

private theorem cusValue_mono_cost (P₀ P₁ : Measure X) (β D : ℝ≥0∞) {θ θ' : ℝ≥0∞}
    (h : θ ≤ θ') (u : ℝ≥0∞) : cusValue P₀ P₁ β D θ u ≤ cusValue P₀ P₁ β D θ' u :=
  iInf_mono fun n => cusIter_mono_cost P₀ P₁ β D h n u

private theorem cusValue_cost_mul_le (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) {t : ℝ≥0∞}
    (ht : 1 ≤ t) (ht' : t ≠ ∞) (u : ℝ≥0∞) :
    cusValue P₀ P₁ β D (t * θ) u ≤ t * cusValue P₀ P₁ β D θ u := by
  rw [cusValue, cusValue, ENNReal.mul_iInf_of_ne (one_pos.trans_le ht).ne' ht']
  exact iInf_mono fun n => cusIter_cost_mul_le P₀ P₁ β D θ n ht u

/-- **Bellman equation** for the value function. -/
private theorem cusValue_eq (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {β : ℝ≥0∞} (hβ0 : β ≠ 0)
    (hβ : β ≠ ∞) (D θ u : ℝ≥0∞) :
    cusValue P₀ P₁ β D θ u = min 1 (cusCont P₀ P₁ β D θ u) := by
  have hshift : cusValue P₀ P₁ β D θ u = ⨅ n, cusIter P₀ P₁ β D θ (n + 1) u :=
    le_antisymm (le_iInf fun n => iInf_le _ (n + 1))
      (iInf_mono fun n => cusIter_succ_le P₀ P₁ β D θ n u)
  rw [hshift]
  simp only [cusIter, cusCont]
  rw [← inf_iInf, ← ENNReal.add_iInf, ← ENNReal.mul_iInf_of_ne hβ0 hβ]
  congr 3
  simp only [cusValue]
  rw [lintegral_iInf]
  · intro n
    exact measurable_cusIter_comp P₀ P₁ β D θ n u
  · intro n m hnm x
    exact antitone_cusIter P₀ P₁ β D θ _ hnm
  · refine ne_top_of_le_ne_top (measure_ne_top P₀ Set.univ) ?_
    rw [← one_mul (P₀ Set.univ), ← lintegral_const]
    exact lintegral_mono fun x => cusIter_le_one P₀ P₁ β D θ 0 _

private theorem cusValue_le_cont (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {β : ℝ≥0∞}
    (hβ0 : β ≠ 0) (hβ : β ≠ ∞) (D θ u : ℝ≥0∞) :
    cusValue P₀ P₁ β D θ u ≤ cusCont P₀ P₁ β D θ u := by
  rw [cusValue_eq P₀ P₁ hβ0 hβ]
  exact min_le_right _ _

private theorem cusCont_mono (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) :
    Monotone (cusCont P₀ P₁ β D θ) := fun u u' h => by
  unfold cusCont
  refine add_le_add (by gcongr; exact monotone_cusCost D h) ?_
  gcongr with x
  exact cusValue_mono P₀ P₁ β D θ (cusStep_mono P₀ P₁ h x)

private theorem cusCont_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] (β D θ u : ℝ≥0∞) :
    cusCont P₀ P₁ β D θ u ≤ θ * cusCost D u + β := by
  unfold cusCont
  gcongr
  calc β * ∫⁻ x, cusValue P₀ P₁ β D θ (cusStep P₀ P₁ u x) ∂P₀ ≤ β * ∫⁻ _, 1 ∂P₀ := by
        gcongr with x
        exact cusValue_le_one P₀ P₁ β D θ _
    _ = β := by simp

private theorem le_cusCont (P₀ P₁ : Measure X) (β D θ u : ℝ≥0∞) :
    θ * cusCost D u ≤ cusCont P₀ P₁ β D θ u :=
  le_self_add

private theorem cusCont_mono_cost (P₀ P₁ : Measure X) (β D : ℝ≥0∞) {θ θ' : ℝ≥0∞}
    (h : θ ≤ θ') (u : ℝ≥0∞) : cusCont P₀ P₁ β D θ u ≤ cusCont P₀ P₁ β D θ' u := by
  unfold cusCont
  gcongr with x
  exact cusValue_mono_cost P₀ P₁ β D h _

private theorem cusCont_le_mul_of_le (P₀ P₁ : Measure X) (β D : ℝ≥0∞) {θ θ' t : ℝ≥0∞}
    (ht : 1 ≤ t) (ht' : t ≠ ∞) (h : θ' ≤ t * θ) (u : ℝ≥0∞) :
    cusCont P₀ P₁ β D θ' u ≤ t * cusCont P₀ P₁ β D θ u := by
  rw [cusCont, cusCont, mul_add t,
    ← lintegral_const_mul _ (measurable_cusValue_comp P₀ P₁ β D θ u)]
  refine add_le_add ?_ ?_
  · calc θ' * cusCost D u ≤ t * θ * cusCost D u := by gcongr
      _ = t * (θ * cusCost D u) := mul_assoc _ _ _
  · rw [← lintegral_const_mul _ (measurable_cusValue_comp P₀ P₁ β D θ' u),
      ← lintegral_const_mul _ ((measurable_cusValue_comp P₀ P₁ β D θ u).const_mul β)]
    refine lintegral_mono fun x => ?_
    calc β * cusValue P₀ P₁ β D θ' (cusStep P₀ P₁ u x)
        ≤ β * (t * cusValue P₀ P₁ β D θ (cusStep P₀ P₁ u x)) := by
          gcongr
          exact (cusValue_mono_cost P₀ P₁ β D h _).trans
            (cusValue_cost_mul_le P₀ P₁ β D θ ht ht' _)
      _ = t * (β * cusValue P₀ P₁ β D θ (cusStep P₀ P₁ u x)) := by ring

private theorem cusCont_ne_top (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {β D θ u : ℝ≥0∞}
    (hβ : β ≠ ∞) (hD : D ≠ ∞) (hθ : θ ≠ ∞) (hu : u ≠ ∞) : cusCont P₀ P₁ β D θ u ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (cusCont_le P₀ P₁ β D θ u)
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hθ ?_, hβ⟩
  exact ENNReal.add_ne_top.2 ⟨max_ne_top hu ENNReal.one_ne_top,
    ENNReal.mul_ne_top hD (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))⟩

/-! ### Choice of the cost: the CUSUM threshold is optimal for some discounted problem -/

/-- Continuity of the continuation cost at a finite state `h` in the cost parameter `θ > 0`. -/
private theorem continuousAt_cusCont (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    {β D h : ℝ≥0∞} (hβ : β ≠ ∞) (hD : D ≠ ∞) (hh : h ≠ ∞) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) :
    ContinuousAt (fun θ : ℝ => (cusCont P₀ P₁ β D (ENNReal.ofReal θ) h).toReal) θ₀ := by
  set F : ℝ → ℝ := fun θ => (cusCont P₀ P₁ β D (ENNReal.ofReal θ) h).toReal with hF
  have hfin : ∀ θ : ℝ, cusCont P₀ P₁ β D (ENNReal.ofReal θ) h ≠ ∞ := fun θ =>
    cusCont_ne_top P₀ P₁ hβ hD ENNReal.ofReal_ne_top hh
  -- two-sided comparison with the value at `θ₀`
  have hcmp : ∀ θ θ' : ℝ, 0 < θ → 0 < θ' → F θ' ≤ max 1 (θ' / θ) * F θ := by
    intro θ θ' hθ hθ'
    have ht1 : 1 ≤ ENNReal.ofReal (max 1 (θ' / θ)) := ENNReal.one_le_ofReal.2 (le_max_left _ _)
    have hle : ENNReal.ofReal θ' ≤ ENNReal.ofReal (max 1 (θ' / θ)) * ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_mul (le_max_of_le_left zero_le_one)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc θ' = θ' / θ * θ := (div_mul_cancel₀ θ' hθ.ne').symm
        _ ≤ max 1 (θ' / θ) * θ := mul_le_mul_of_nonneg_right (le_max_right _ _) hθ.le
    have h1 := cusCont_le_mul_of_le P₀ P₁ β D ht1 ENNReal.ofReal_ne_top hle h
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin θ)) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_max_of_le_left zero_le_one)] at h2
  have hup : ∀ᶠ θ in 𝓝 θ₀, F θ ≤ max 1 (θ / θ₀) * F θ₀ := by
    filter_upwards [eventually_gt_nhds hθ₀] with θ hθ
    exact hcmp θ₀ θ hθ₀ hθ
  have hlow : ∀ᶠ θ in 𝓝 θ₀, F θ₀ / max 1 (θ₀ / θ) ≤ F θ := by
    filter_upwards [eventually_gt_nhds hθ₀] with θ hθ
    rw [div_le_iff₀ (lt_max_of_lt_left one_pos), mul_comm]
    exact hcmp θ θ₀ hθ hθ₀
  have hT1 : Tendsto (fun θ => max 1 (θ / θ₀) * F θ₀) (𝓝 θ₀) (𝓝 (F θ₀)) := by
    have : ContinuousAt (fun θ => max 1 (θ / θ₀) * F θ₀) θ₀ :=
      (continuousAt_const.max (continuousAt_id.div_const θ₀)).mul continuousAt_const
    simpa [div_self hθ₀.ne'] using this.tendsto
  have hT2 : Tendsto (fun θ => F θ₀ / max 1 (θ₀ / θ)) (𝓝 θ₀) (𝓝 (F θ₀)) := by
    have : ContinuousAt (fun θ => F θ₀ / max 1 (θ₀ / θ)) θ₀ :=
      continuousAt_const.div (continuousAt_const.max
        (continuousAt_const.div continuousAt_id hθ₀.ne')) (lt_max_of_lt_left one_pos).ne'
    simpa [div_self hθ₀.ne'] using this.tendsto
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hT2 hT1 hlow hup

/-- **Choice of the cost.** For every discount `0 < β < 1` and every finite threshold `h`,
some cost `θ > 0` makes observing and stopping equally good at `h`. -/
private theorem exists_cusCont_eq_one (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    {β D h : ℝ≥0∞} (hβ1 : β < 1) (hD : D ≠ ∞) (hh : h ≠ ∞) :
    ∃ θ : ℝ, 0 < θ ∧ (1 - β.toReal) / (cusCost D h).toReal ≤ θ ∧
      cusCont P₀ P₁ β D (ENNReal.ofReal θ) h = 1 := by
  have hβ : β ≠ ∞ := (hβ1.trans ENNReal.one_lt_top).ne
  set K := cusCost D h with hK
  have hK1 : 1 ≤ K := le_self_add.trans' (le_max_right _ _)
  have hKtop : K ≠ ∞ := ENNReal.add_ne_top.2 ⟨max_ne_top hh ENNReal.one_ne_top,
    ENNReal.mul_ne_top hD (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))⟩
  have hKr : 1 ≤ K.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hKtop hK1
  have hb1 : β.toReal < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hβ1
  set θ₁ := (1 - β.toReal) / K.toReal
  set θ₂ := 1 / K.toReal
  have hθ₁ : 0 < θ₁ := div_pos (by linarith) (by linarith)
  have hθ₁₂ : θ₁ ≤ θ₂ := div_le_div_of_nonneg_right (by linarith [ENNReal.toReal_nonneg (a := β)])
    (by linarith)
  set F : ℝ → ℝ := fun θ => (cusCont P₀ P₁ β D (ENNReal.ofReal θ) h).toReal
  have hfin : ∀ θ : ℝ, cusCont P₀ P₁ β D (ENNReal.ofReal θ) h ≠ ∞ := fun θ =>
    cusCont_ne_top P₀ P₁ hβ hD ENNReal.ofReal_ne_top hh
  have hF₁ : F θ₁ ≤ 1 := by
    have h1 := cusCont_le P₀ P₁ β D (ENNReal.ofReal θ₁) h
    have h2 : ENNReal.ofReal θ₁ * K + β = 1 := by
      rw [← ENNReal.ofReal_toReal hKtop, ← ENNReal.ofReal_mul hθ₁.le, ← ENNReal.ofReal_toReal hβ,
        ← ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg, div_mul_cancel₀ _ (by linarith),
        sub_add_cancel, ENNReal.ofReal_one]
    rw [h2] at h1
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
  have hF₂ : 1 ≤ F θ₂ := by
    have h1 := le_cusCont P₀ P₁ β D (ENNReal.ofReal θ₂) h
    have h2 : ENNReal.ofReal θ₂ * K = 1 := by
      rw [← ENNReal.ofReal_toReal hKtop, ← ENNReal.ofReal_mul (by positivity),
        div_mul_cancel₀ _ (by linarith), ENNReal.ofReal_one]
    rw [h2] at h1
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (hfin θ₂) h1
  have hcont : ContinuousOn F (Set.Icc θ₁ θ₂) := fun θ hθ =>
    (continuousAt_cusCont P₀ P₁ hβ hD hh (hθ₁.trans_le hθ.1)).continuousWithinAt
  obtain ⟨θ, hθ, hFθ⟩ := intermediate_value_Icc hθ₁₂ hcont ⟨hF₁, hF₂⟩
  refine ⟨θ, hθ₁.trans_le hθ.1, hθ.1, ?_⟩
  rw [← ENNReal.ofReal_toReal (hfin θ)]
  change ENNReal.ofReal (F θ) = 1
  rw [hFθ, ENNReal.ofReal_one]

/-! ### Verification for the discounted problems -/

/-- `E_∞[∑_{k<T} βᵏ f(U_k)]`, the discounted expected sum of `f` along the CUSUM chain before
`T`. -/
private noncomputable def cusDisc (P₀ P₁ : Measure X) (β : ℝ≥0∞) (f : ℝ≥0∞ → ℝ≥0∞)
    (T : (ℕ → X) → WithTop ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, β ^ k * ∫⁻ ω in {ω | (k : WithTop ℕ) < T ω}, f (cusU P₀ P₁ k ω)
    ∂Measure.infinitePi (fun _ : ℕ => P₀)

/-- Expected discounted running cost `θ βᵏ r(U_k)` that a stopping time `T` pays at step `k`
when it continues, on `{k < T}`. -/
private noncomputable def cusStepCost (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞)
    (T : (ℕ → X) → WithTop ℕ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | (k : WithTop ℕ) < T ω}, θ * (β ^ k * cusCost D (cusU P₀ P₁ k ω))
    ∂Measure.infinitePi (fun _ : ℕ => P₀)

/-- Discounted value of the state at which `T` stops, on the event `{T = k}`. -/
private noncomputable def cusStopValue (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞)
    (T : (ℕ → X) → WithTop ℕ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | T ω = k}, β ^ k * cusValue P₀ P₁ β D θ (cusU P₀ P₁ k ω)
    ∂Measure.infinitePi (fun _ : ℕ => P₀)

/-- Discounted value of the state at time `n` on the event that `T` has not stopped before
`n`. -/
private noncomputable def cusRemValue (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞)
    (T : (ℕ → X) → WithTop ℕ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | (n : WithTop ℕ) ≤ T ω}, β ^ n * cusValue P₀ P₁ β D θ (cusU P₀ P₁ n ω)
    ∂Measure.infinitePi (fun _ : ℕ => P₀)

private theorem cusRemValue_eq (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) (n : ℕ) :
    cusRemValue P₀ P₁ β D θ T n = cusStopValue P₀ P₁ β D θ T n +
      ∫⁻ ω in {ω | (n : WithTop ℕ) < T ω}, β ^ n * cusValue P₀ P₁ β D θ (cusU P₀ P₁ n ω)
        ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  have hset : {ω | (n : WithTop ℕ) ≤ T ω} = {ω | T ω = n} ∪ {ω | (n : WithTop ℕ) < T ω} := by
    ext ω; simp only [Set.mem_union, Set.mem_ofPred_eq, le_iff_eq_or_lt, eq_comm]
  rw [cusRemValue, cusStopValue, hset, lintegral_union
    ((observationFiltration X).le n _ (measurableSet_natCast_lt hT n))]
  refine Set.disjoint_left.2 fun ω h1 h2 => ?_
  simp only [Set.mem_ofPred_eq] at h1 h2
  rw [h1] at h2
  exact lt_irrefl _ h2

private theorem setLIntegral_cusCont_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    (β D θ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ} (hT : IsStoppingTime (observationFiltration X) T)
    (n : ℕ) :
    ∫⁻ ω in {ω | (n : WithTop ℕ) < T ω}, β ^ n * cusCont P₀ P₁ β D θ (cusU P₀ P₁ n ω)
        ∂Measure.infinitePi (fun _ : ℕ => P₀) =
      cusStepCost P₀ P₁ β D θ T n + cusRemValue P₀ P₁ β D θ T (n + 1) := by
  have hY := measurable_cusU P₀ P₁ n
  have hYm := measurable_cusU' P₀ P₁ n
  have hh : Measurable (Function.uncurry fun u x =>
      β ^ (n + 1) * cusValue P₀ P₁ β D θ (cusStep P₀ P₁ u x)) :=
    measurable_const.mul ((measurable_cusValue P₀ P₁ β D θ).comp (measurable_cusStep P₀ P₁))
  have hpt : ∀ ω, β ^ n * cusCont P₀ P₁ β D θ (cusU P₀ P₁ n ω) =
      θ * (β ^ n * cusCost D (cusU P₀ P₁ n ω)) + ∫⁻ x,
        β ^ (n + 1) * cusValue P₀ P₁ β D θ (cusStep P₀ P₁ (cusU P₀ P₁ n ω) x) ∂P₀ := by
    intro ω
    rw [cusCont, lintegral_const_mul _ (measurable_cusValue_comp P₀ P₁ β D θ _)]
    ring
  simp only [hpt]
  rw [lintegral_add_left (f := fun ω => θ * (β ^ n * cusCost D (cusU P₀ P₁ n ω)))
    (measurable_const.mul (measurable_const.mul ((measurable_cusCost D).comp hYm))),
    cusStepCost, cusRemValue, setOfPred_natCast_add_one_le_eq,
    ← setLIntegral_infinitePi_coord P₀ n (measurableSet_natCast_lt hT n) hY hh]
  rfl

private theorem cusRemValue_zero (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] (β D θ : ℝ≥0∞)
    (T : (ℕ → X) → WithTop ℕ) : cusRemValue P₀ P₁ β D θ T 0 = cusValue P₀ P₁ β D θ 0 := by
  simp [cusRemValue, cusU]

/-- For any stopping time `T` and horizon `n`, the value at the initial state `0` is at most the
expected running cost of `T` before `min T n`, plus the discounted value at the states where `T`
stops before `n`, plus the discounted value at time `n` on `{n ≤ T}`. -/
private theorem cusValue_le_sum_add_remValue (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    {β : ℝ≥0∞} (hβ0 : β ≠ 0) (hβ : β ≠ ∞) (D θ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) (n : ℕ) :
    cusValue P₀ P₁ β D θ 0 ≤ ∑ k ∈ range n,
      (cusStepCost P₀ P₁ β D θ T k + cusStopValue P₀ P₁ β D θ T k) +
        cusRemValue P₀ P₁ β D θ T n := by
  induction n with
  | zero => simp [cusRemValue_zero]
  | succ n ih =>
    refine ih.trans ?_
    rw [sum_range_succ, add_assoc]
    refine add_le_add le_rfl ?_
    rw [cusRemValue_eq P₀ P₁ β D θ hT, add_comm (cusStepCost _ _ _ _ _ _ _), add_assoc,
      ← setLIntegral_cusCont_eq P₀ P₁ β D θ hT]
    refine add_le_add le_rfl (lintegral_mono fun ω => ?_)
    gcongr
    exact cusValue_le_cont P₀ P₁ hβ0 hβ D θ _

/-- If observing is optimal at the state of every time at which `T` continues, the bound of
`cusValue_le_sum_add_remValue` is reversed: the expected running cost of `T` before `min T n`,
plus the discounted value at the states where `T` stops before `n`, plus the discounted value at
time `n` on `{n ≤ T}`, is at most the value at the initial state `0`. This is the expected cost
of `T` only if, moreover, stopping is optimal where `T` stops (`risk_le_cusValue`). -/
private theorem sum_add_remValue_le_cusValue (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    (β D θ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ} (hT : IsStoppingTime (observationFiltration X) T)
    (hcont : ∀ n : ℕ, ∀ ω, (n : WithTop ℕ) < T ω →
      cusCont P₀ P₁ β D θ (cusU P₀ P₁ n ω) ≤ cusValue P₀ P₁ β D θ (cusU P₀ P₁ n ω))
    (n : ℕ) :
    ∑ k ∈ range n, (cusStepCost P₀ P₁ β D θ T k + cusStopValue P₀ P₁ β D θ T k) +
      cusRemValue P₀ P₁ β D θ T n ≤ cusValue P₀ P₁ β D θ 0 := by
  induction n with
  | zero => simp [cusRemValue_zero]
  | succ n ih =>
    refine le_trans ?_ ih
    rw [sum_range_succ, add_assoc]
    refine add_le_add le_rfl ?_
    rw [cusRemValue_eq P₀ P₁ β D θ hT n, add_comm (cusStepCost _ _ _ _ _ _ _), add_assoc,
      ← setLIntegral_cusCont_eq P₀ P₁ β D θ hT]
    refine add_le_add le_rfl (setLIntegral_mono' ((observationFiltration X).le n _
      (measurableSet_natCast_lt hT n)) fun ω hω => ?_)
    gcongr
    exact hcont n ω hω

private theorem tsum_cusStepCost (P₀ P₁ : Measure X) (β D θ : ℝ≥0∞)
    (T : (ℕ → X) → WithTop ℕ) :
    ∑' k, cusStepCost P₀ P₁ β D θ T k = θ * cusDisc P₀ P₁ β (cusCost D) T := by
  rw [cusDisc, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hm : Measurable fun ω => cusCost D (cusU P₀ P₁ k ω) :=
    (measurable_cusCost D).comp (measurable_cusU' P₀ P₁ k)
  rw [cusStepCost, lintegral_const_mul _ (hm.const_mul _), lintegral_const_mul _ hm]

/-- **Lower bound for the discounted cost of any stopping time.** -/
private theorem cusValue_le_risk (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    {β : ℝ≥0∞} (hβ0 : β ≠ 0) (hβ1 : β < 1) (D θ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) :
    cusValue P₀ P₁ β D θ 0 ≤ θ * cusDisc P₀ P₁ β (cusCost D) T +
      ∑' k : ℕ, β ^ k * Measure.infinitePi (fun _ : ℕ => P₀) {ω | T ω = k} := by
  have hβ : β ≠ ∞ := (hβ1.trans ENNReal.one_lt_top).ne
  set S := ∑' k, (cusStepCost P₀ P₁ β D θ T k + cusStopValue P₀ P₁ β D θ T k) with hS
  have hbound : ∀ n : ℕ, cusValue P₀ P₁ β D θ 0 ≤ S + β ^ n := by
    intro n
    refine (cusValue_le_sum_add_remValue P₀ P₁ hβ0 hβ D θ hT n).trans
      (add_le_add (sum_le_tsum _) ?_)
    calc cusRemValue P₀ P₁ β D θ T n ≤ ∫⁻ _ in {ω | (n : WithTop ℕ) ≤ T ω}, β ^ n
          ∂Measure.infinitePi (fun _ : ℕ => P₀) :=
          lintegral_mono fun ω => mul_le_of_le_one_right' (cusValue_le_one P₀ P₁ β D θ _)
      _ = β ^ n * Measure.infinitePi (fun _ : ℕ => P₀) {ω | (n : WithTop ℕ) ≤ T ω} :=
          setLIntegral_const _ _
      _ ≤ β ^ n * 1 := by gcongr; exact prob_le_one
      _ = β ^ n := mul_one _
  have htend : Tendsto (fun n : ℕ => S + β ^ n) atTop (𝓝 S) := by
    simpa using tendsto_const_nhds.add (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hβ1)
  refine (ge_of_tendsto' htend hbound).trans ?_
  rw [hS, tsum_add, tsum_cusStepCost]
  refine add_le_add le_rfl (tsum_le_tsum fun k => ?_)
  rw [cusStopValue, ← setLIntegral_const]
  exact lintegral_mono fun ω => mul_le_of_le_one_right' (cusValue_le_one P₀ P₁ β D θ _)

/-- **A rule that observes only where observing is optimal and stops where the value is `1`
attains the discounted value.** -/
private theorem risk_le_cusValue (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    (β D θ : ℝ≥0∞) {T : (ℕ → X) → WithTop ℕ} (hT : IsStoppingTime (observationFiltration X) T)
    (hcont : ∀ n : ℕ, ∀ ω, (n : WithTop ℕ) < T ω →
      cusCont P₀ P₁ β D θ (cusU P₀ P₁ n ω) ≤ cusValue P₀ P₁ β D θ (cusU P₀ P₁ n ω))
    (hstop : ∀ (n : ℕ) ω, T ω = n → cusValue P₀ P₁ β D θ (cusU P₀ P₁ n ω) = 1) :
    θ * cusDisc P₀ P₁ β (cusCost D) T +
      ∑' k : ℕ, β ^ k * Measure.infinitePi (fun _ : ℕ => P₀) {ω | T ω = k} ≤
      cusValue P₀ P₁ β D θ 0 := by
  have hsum : ∑' k, (cusStepCost P₀ P₁ β D θ T k + cusStopValue P₀ P₁ β D θ T k) ≤
      cusValue P₀ P₁ β D θ 0 :=
    ENNReal.tsum_le_of_sum_range_le fun n => le_self_add.trans
      (sum_add_remValue_le_cusValue P₀ P₁ β D θ hT hcont n)
  rw [tsum_add, tsum_cusStepCost] at hsum
  refine le_trans (le_of_eq ?_) hsum
  congr 1
  refine tsum_congr fun k => ?_
  rw [cusStopValue, ← setLIntegral_const]
  refine (setLIntegral_congr_fun ((observationFiltration X).le k _ (hT.measurableSet_eq k))
    fun ω hω => ?_).symm
  rw [hstop k ω hω, mul_one]

/-- `(1 - β) ∑_{k<n} βᵏ = 1 - βⁿ`. -/
private theorem one_sub_mul_sum_pow {β : ℝ≥0∞} (hβ1 : β ≤ 1) (n : ℕ) :
    (1 - β) * ∑ k ∈ range n, β ^ k = 1 - β ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hβtop : β ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
    rw [sum_range_succ, mul_add, ih, ENNReal.sub_mul fun _ _ => ENNReal.pow_ne_top hβtop, one_mul,
      ← pow_succ']
    exact tsub_add_tsub_cancel (pow_le_one₀ zero_le hβ1)
      (pow_le_pow_of_le_one zero_le hβ1 (Nat.le_succ n))

/-- `∑ₖ βᵏ 1{t = k} + (1 - β) ∑ₖ βᵏ 1{k < t} = 1` for every `t : WithTop ℕ`. -/
private theorem tsum_pow_ite_add {β : ℝ≥0∞} (hβ1 : β < 1) (t : WithTop ℕ) :
    ∑' k : ℕ, β ^ k * (if t = k then 1 else 0) +
      (1 - β) * ∑' k : ℕ, β ^ k * (if (k : WithTop ℕ) < t then 1 else 0) = 1 := by
  by_cases ht : t = ⊤
  · subst ht
    have h1 : ∑' k : ℕ, β ^ k * (if (⊤ : WithTop ℕ) = k then 1 else 0) = 0 :=
      tsum_eq_zero_iff.2 fun k => by simp
    have h2 : ∑' k : ℕ, β ^ k * (if (k : WithTop ℕ) < ⊤ then 1 else 0) = ∑' k : ℕ, β ^ k :=
      tsum_congr fun k => by simp
    rw [h1, h2, zero_add, ENNReal.tsum_geometric, ENNReal.mul_inv_cancel
      (tsub_pos_of_lt hβ1).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 ht
  have hn' : t = (n : WithTop ℕ) := hn.symm
  subst hn'
  have h1 : ∑' k : ℕ, β ^ k * (if (n : WithTop ℕ) = k then 1 else 0) = β ^ n := by
    rw [tsum_eq_single n fun k hk => by simp [Ne.symm hk]]
    simp
  have h2 : ∑' k : ℕ, β ^ k * (if (k : WithTop ℕ) < n then 1 else 0) =
      ∑ k ∈ range n, β ^ k := by
    rw [← tsum_ite_lt_eq]
    exact tsum_congr fun k => by
      by_cases hk : k < n
      · rw [ite_eq_left (by exact_mod_cast hk), ite_eq_left hk, mul_one]
      · rw [ite_eq_right (by exact_mod_cast hk), ite_eq_right hk, mul_zero]
  rw [h1, h2, one_sub_mul_sum_pow hβ1.le, add_tsub_cancel_of_le (pow_le_one₀ zero_le hβ1.le)]

/-- `G_β(T) + (1 - β) E_∞[∑_{k<T} βᵏ] = 1`, with `G_β(T) = E_∞[β^T; T < ∞]`. -/
private theorem tsum_pow_measure_eq_add (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    {β : ℝ≥0∞} (hβ1 : β < 1) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) :
    ∑' k : ℕ, β ^ k * Measure.infinitePi (fun _ : ℕ => P₀) {ω | T ω = k} +
      (1 - β) * cusDisc P₀ P₁ β (fun _ => 1) T = 1 := by
  set μ := Measure.infinitePi (fun _ : ℕ => P₀)
  have hE : ∀ k : ℕ, MeasurableSet {ω | T ω = k} := fun k =>
    (observationFiltration X).le k _ (hT.measurableSet_eq k)
  have hL : ∀ k : ℕ, MeasurableSet {ω | (k : WithTop ℕ) < T ω} := fun k =>
    (observationFiltration X).le k _ (measurableSet_natCast_lt hT k)
  have hA : ∑' k : ℕ, β ^ k * μ {ω | T ω = k} =
      ∫⁻ ω, ∑' k : ℕ, β ^ k * (if T ω = k then 1 else 0) ∂μ := by
    rw [lintegral_tsum (f := fun (k : ℕ) ω => β ^ k * (if T ω = k then 1 else 0))
      fun k => by exact ((Measurable.ite (hE k) measurable_const measurable_const).const_mul
        _).aemeasurable]
    refine tsum_congr fun k => ?_
    rw [lintegral_const_mul _ (Measurable.ite (hE k) measurable_const measurable_const)]
    congr 1
    rw [← lintegral_indicator_one (hE k)]
    exact lintegral_congr fun ω => by simp [Set.indicator_apply]
  have hB : cusDisc P₀ P₁ β (fun _ => 1) T =
      ∫⁻ ω, ∑' k : ℕ, β ^ k * (if (k : WithTop ℕ) < T ω then 1 else 0) ∂μ := by
    rw [lintegral_tsum (f := fun (k : ℕ) ω => β ^ k * (if (k : WithTop ℕ) < T ω then 1 else 0))
      fun k => by exact ((Measurable.ite (hL k) measurable_const measurable_const).const_mul
        _).aemeasurable, cusDisc]
    refine tsum_congr fun k => ?_
    rw [lintegral_const_mul _ (Measurable.ite (hL k) measurable_const measurable_const),
      setLIntegral_const, one_mul, ← lintegral_indicator_one (hL k)]
    exact congrArg _ (lintegral_congr fun ω => by simp [Set.indicator_apply])
  have hmB : Measurable fun ω => ∑' k : ℕ, β ^ k * (if (k : WithTop ℕ) < T ω then 1 else 0) :=
    Measurable.tsum fun k => measurable_const.mul
      (Measurable.ite (hL k) measurable_const measurable_const)
  rw [hA, hB, ← lintegral_const_mul _ hmB, ← lintegral_add_right _ (hmB.const_mul _)]
  simp only [tsum_pow_ite_add hβ1, lintegral_const, measure_univ, one_mul]

/-- **CUSUM solves a discounted problem.** For every discount `0 < β < 1` there is a multiplier
`0 ≤ s ≤ r(e^c)` such that, for every stopping time `T`,
`E_∞[∑_{k<N} βᵏ r(U_k)] + s E_∞[∑_{k<T} βᵏ] ≤ E_∞[∑_{k<T} βᵏ r(U_k)] + s E_∞[∑_{k<N} βᵏ]`. -/
private theorem exists_cusDisc_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {c : ℝ} (hc : 0 < c)
    {D : ℝ≥0∞} (hD : D ≠ ∞) {β : ℝ≥0∞} (hβ0 : β ≠ 0) (hβ1 : β < 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ (cusCost D (ENNReal.ofReal (Real.exp c))).toReal ∧
      ∀ T : (ℕ → X) → WithTop ℕ, IsStoppingTime (observationFiltration X) T →
        cusDisc P₀ P₁ β (cusCost D) (cusumTime P₀ P₁ h₁₀ h₀₁ c) +
            ENNReal.ofReal s * cusDisc P₀ P₁ β (fun _ => 1) T ≤
          cusDisc P₀ P₁ β (cusCost D) T +
            ENNReal.ofReal s * cusDisc P₀ P₁ β (fun _ => 1) (cusumTime P₀ P₁ h₁₀ h₀₁ c) := by
  have hβ : β ≠ ∞ := (hβ1.trans ENNReal.one_lt_top).ne
  set h := ENNReal.ofReal (Real.exp c) with hhdef
  have hh : h ≠ ∞ := ENNReal.ofReal_ne_top
  obtain ⟨θ, hθ0, hθ1, hC⟩ := exists_cusCont_eq_one P₀ P₁ hβ1 hD hh
  set K := cusCost D h with hK
  have hK1 : 1 ≤ K := le_self_add.trans' (le_max_right _ _)
  have hKtop : K ≠ ∞ := ENNReal.add_ne_top.2 ⟨max_ne_top hh ENNReal.one_ne_top,
    ENNReal.mul_ne_top hD (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))⟩
  have hKpos : 0 < K.toReal := by
    have : (1 : ℝ) ≤ K.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono hKtop hK1
    linarith
  have hb1 : β.toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top hβ1.le
  set ϑ := ENNReal.ofReal θ with hϑ
  have hϑ0 : ϑ ≠ 0 := (ENNReal.ofReal_pos.2 hθ0).ne'
  have hϑtop : ϑ ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨(1 - β.toReal) / θ, div_nonneg (by linarith) hθ0.le, ?_, fun T hT => ?_⟩
  · rw [div_le_iff₀ hθ0]
    rw [div_le_iff₀ hKpos] at hθ1
    linarith
  set N := cusumTime P₀ P₁ h₁₀ h₀₁ c
  have hN := isStoppingTime_cusumTime P₀ P₁ h₁₀ h₀₁ c
  -- the CUSUM rule observes while the chain is below `h` and stops at or above it
  have hcont : ∀ n : ℕ, ∀ ω, (n : WithTop ℕ) < N ω →
      cusCont P₀ P₁ β D ϑ (cusU P₀ P₁ n ω) ≤ cusValue P₀ P₁ β D ϑ (cusU P₀ P₁ n ω) := by
    intro n ω hn
    have hW : ¬ c ≤ pageCusum P₀ P₁ h₁₀ h₀₁ n ω := by
      rcases Nat.eq_zero_or_pos n with rfl | hn1
      · simpa [pageCusum] using hc
      · exact notMem_of_lt_hittingAfter (u := pageCusum P₀ P₁ h₁₀ h₀₁) (s := Set.Ici c)
          (n := 1) hn hn1
    have hU : cusU P₀ P₁ n ω ≤ h := (not_le.1 ((le_pageCusum_iff P₀ P₁ h₁₀ h₀₁ hc n ω).not.1
      hW)).le
    have hle : cusCont P₀ P₁ β D ϑ (cusU P₀ P₁ n ω) ≤ 1 := hC ▸ cusCont_mono P₀ P₁ β D ϑ hU
    rw [cusValue_eq P₀ P₁ hβ0 hβ, min_eq_right hle]
  have hstop : ∀ (n : ℕ) ω, N ω = n → cusValue P₀ P₁ β D ϑ (cusU P₀ P₁ n ω) = 1 := by
    intro n ω hn
    have hne : hittingAfter (pageCusum P₀ P₁ h₁₀ h₀₁) (Set.Ici c) 1 ω ≠ ⊤ := by
      change N ω ≠ ⊤
      rw [hn]
      exact WithTop.coe_ne_top
    have hmem := hittingAfter_mem_set_of_ne_top hne
    change c ≤ pageCusum P₀ P₁ h₁₀ h₀₁ (N ω).untopA ω at hmem
    rw [hn] at hmem
    have hU : h ≤ cusU P₀ P₁ n ω := (le_pageCusum_iff P₀ P₁ h₁₀ h₀₁ hc n ω).1 hmem
    have hle : 1 ≤ cusCont P₀ P₁ β D ϑ (cusU P₀ P₁ n ω) := hC ▸ cusCont_mono P₀ P₁ β D ϑ hU
    rw [cusValue_eq P₀ P₁ hβ0 hβ, min_eq_left hle]
  have h1 := risk_le_cusValue P₀ P₁ β D ϑ hN hcont hstop
  have h2 := cusValue_le_risk P₀ P₁ hβ0 hβ1 D ϑ hT
  have hGN := tsum_pow_measure_eq_add P₀ P₁ hβ1 hN
  have hGT := tsum_pow_measure_eq_add P₀ P₁ hβ1 hT
  set gN := ∑' k : ℕ, β ^ k * Measure.infinitePi (fun _ : ℕ => P₀) {ω | N ω = k}
  set gT := ∑' k : ℕ, β ^ k * Measure.infinitePi (fun _ : ℕ => P₀) {ω | T ω = k}
  set eN := (1 - β) * cusDisc P₀ P₁ β (fun _ => 1) N
  set eT := (1 - β) * cusDisc P₀ P₁ β (fun _ => 1) T
  set a := cusDisc P₀ P₁ β (cusCost D) N
  set b := cusDisc P₀ P₁ β (cusCost D) T
  have h3 : ϑ * a + eT ≤ ϑ * b + eN := by
    refine ENNReal.le_of_add_le_add_right ENNReal.one_ne_top ?_
    calc ϑ * a + eT + 1 = (ϑ * a + gN) + (eT + eN) := by rw [← hGN]; ring
      _ ≤ (ϑ * b + gT) + (eT + eN) := add_le_add (h1.trans h2) le_rfl
      _ = ϑ * b + eN + 1 := by rw [← hGT]; ring
  have hs : ENNReal.ofReal ((1 - β.toReal) / θ) = ϑ⁻¹ * (1 - β) := by
    rw [ENNReal.ofReal_div_of_pos hθ0, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_toReal hβ, div_eq_mul_inv, mul_comm]
  have h4 : ϑ⁻¹ * (ϑ * a + eT) ≤ ϑ⁻¹ * (ϑ * b + eN) := by gcongr
  have e1 : ∀ x : ℝ≥0∞, ϑ⁻¹ * (ϑ * x) = x := fun x => by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hϑ0 hϑtop, one_mul]
  rw [mul_add, mul_add, e1, e1] at h4
  rw [hs, mul_assoc, mul_assoc]
  exact h4

/-! ### The limit of vanishing discount -/

private theorem cusDisc_le_cusSum (P₀ P₁ : Measure X) {β : ℝ≥0∞} (hβ1 : β ≤ 1)
    (f : ℝ≥0∞ → ℝ≥0∞) (T : (ℕ → X) → WithTop ℕ) :
    cusDisc P₀ P₁ β f T ≤ cusSum P₀ P₁ f T :=
  tsum_le_tsum fun _ => mul_le_of_le_one_left' (pow_le_one₀ zero_le hβ1)

/-- Monotone convergence for discounted sums as the discount increases to `1`. -/
private theorem tendsto_tsum_pow_mul {b : ℕ → ℝ≥0∞} (hb : Monotone b)
    (hb1 : Tendsto b atTop (𝓝 1)) (a : ℕ → ℝ≥0∞) :
    Tendsto (fun j => ∑' k, b j ^ k * a k) atTop (𝓝 (∑' k, a k)) := by
  have hmono : ∀ k, Monotone fun j => b j ^ k * a k := fun k i j hij => by
    change b i ^ k * a k ≤ b j ^ k * a k
    gcongr
    exact hb hij
  have hsup : ∀ k, ⨆ j, b j ^ k * a k = a k := by
    intro k
    rw [← ENNReal.iSup_mul]
    have htend : Tendsto (fun j => b j ^ k) atTop (𝓝 1) := by
      have := ((ENNReal.continuous_pow k).tendsto 1).comp hb1
      rw [one_pow] at this
      exact this
    rw [iSup_eq_of_tendsto (fun i j hij => by gcongr; exact hb hij) htend, one_mul]
  have hkey : ⨆ j, ∑' k, b j ^ k * a k = ∑' k, a k := by
    simp_rw [← lintegral_count]
    rw [← lintegral_iSup (fun j => measurable_of_countable _) fun i j hij k => hmono k hij]
    exact lintegral_congr fun k => hsup k
  rw [← hkey]
  exact tendsto_atTop_iSup fun i j hij => tsum_le_tsum fun k => hmono k hij

/-- The discounts `βⱼ = 1 - 1/(j + 2)`, increasing to `1`. -/
private noncomputable def discSeq (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - 1 / ((j : ℝ) + 2))

private theorem discSeq_ne_zero (j : ℕ) : discSeq j ≠ 0 := by
  refine (ENNReal.ofReal_pos.2 ?_).ne'
  have : 1 / ((j : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  linarith

private theorem discSeq_lt_one (j : ℕ) : discSeq j < 1 := by
  rw [discSeq, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff one_pos]
  have : 0 < 1 / ((j : ℝ) + 2) := by positivity
  linarith

private theorem monotone_discSeq : Monotone discSeq := fun i j hij => by
  refine ENNReal.ofReal_le_ofReal (sub_le_sub_left ?_ _)
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

private theorem tendsto_discSeq : Tendsto discSeq atTop (𝓝 1) := by
  have h : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h' : Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 2)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    rwa [sub_zero] at this
  have := (ENNReal.continuous_ofReal.tendsto 1).comp h'
  rw [ENNReal.ofReal_one] at this
  exact this

/-- **Lagrangian inequality for CUSUM.** There is a multiplier `s < ∞` such that every stopping
time `T` with `E_∞[T] < ∞` satisfies
`E_∞[∑_{k<N} r(U_k)] + s E_∞[T] ≤ E_∞[∑_{k<T} r(U_k)] + s E_∞[N]`. -/
private theorem exists_lagrange (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {c : ℝ} (hc : 0 < c)
    {D : ℝ≥0∞} (hD : D ≠ ∞)
    (hEN : cusSum P₀ P₁ (fun _ => 1) (cusumTime P₀ P₁ h₁₀ h₀₁ c) ≠ ∞) :
    ∃ S : ℝ≥0∞, S ≠ ∞ ∧ ∀ T : (ℕ → X) → WithTop ℕ,
      IsStoppingTime (observationFiltration X) T → cusSum P₀ P₁ (fun _ => 1) T ≠ ∞ →
        cusSum P₀ P₁ (cusCost D) (cusumTime P₀ P₁ h₁₀ h₀₁ c) +
            S * cusSum P₀ P₁ (fun _ => 1) T ≤
          cusSum P₀ P₁ (cusCost D) T +
            S * cusSum P₀ P₁ (fun _ => 1) (cusumTime P₀ P₁ h₁₀ h₀₁ c) := by
  set N := cusumTime P₀ P₁ h₁₀ h₀₁ c
  set K := (cusCost D (ENNReal.ofReal (Real.exp c))).toReal
  choose s hs0 hsK hineq using fun j =>
    exists_cusDisc_le P₀ P₁ h₁₀ h₀₁ hc hD (discSeq_ne_zero j) (discSeq_lt_one j)
  obtain ⟨s', hs', φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (x := s) (Metric.isBounded_Icc 0 K)
    fun j => ⟨hs0 j, hsK j⟩
  rw [isClosed_Icc.closure_eq] at hs'
  refine ⟨ENNReal.ofReal s', ENNReal.ofReal_ne_top, fun T hT hET => ?_⟩
  have hb : Monotone (discSeq ∘ φ) := monotone_discSeq.comp hφ.monotone
  have hb1 : Tendsto (discSeq ∘ φ) atTop (𝓝 1) := tendsto_discSeq.comp hφ.tendsto_atTop
  have hS : Tendsto (fun j => ENNReal.ofReal (s (φ j))) atTop (𝓝 (ENNReal.ofReal s')) :=
    (ENNReal.continuous_ofReal.tendsto s').comp hlim
  have hL : Tendsto (fun j => cusDisc P₀ P₁ (discSeq (φ j)) (cusCost D) N +
      ENNReal.ofReal (s (φ j)) * cusDisc P₀ P₁ (discSeq (φ j)) (fun _ => 1) T) atTop
      (𝓝 (cusSum P₀ P₁ (cusCost D) N + ENNReal.ofReal s' * cusSum P₀ P₁ (fun _ => 1) T)) :=
    (tendsto_tsum_pow_mul hb hb1 _).add (ENNReal.Tendsto.mul hS (Or.inr hET)
      (tendsto_tsum_pow_mul hb hb1 _) (Or.inr ENNReal.ofReal_ne_top))
  have hR : Tendsto (fun j => cusSum P₀ P₁ (cusCost D) T +
      ENNReal.ofReal (s (φ j)) * cusSum P₀ P₁ (fun _ => 1) N) atTop
      (𝓝 (cusSum P₀ P₁ (cusCost D) T + ENNReal.ofReal s' * cusSum P₀ P₁ (fun _ => 1) N)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.mul_const hS (Or.inr hEN))
  refine le_of_tendsto_of_tendsto' hL hR fun j => (hineq (φ j) T hT).trans ?_
  gcongr
  · exact cusDisc_le_cusSum P₀ P₁ (discSeq_lt_one _).le _ _
  · exact cusDisc_le_cusSum P₀ P₁ (discSeq_lt_one _).le _ _

/-! ### Moustakides' theorem -/

private theorem lordenDelay_mono (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] {T T' : (ℕ → X) → WithTop ℕ} (h : ∀ ω, T ω ≤ T' ω) :
    lordenDelay P₀ P₁ T ≤ lordenDelay P₀ P₁ T' := by
  refine iSup₂_mono fun ν _ => iSup₂_mono fun F _ => iSup_mono fun _ => ?_
  refine ENNReal.div_le_div_right (lintegral_mono fun ω => ?_) _
  exact ENat.toENNReal_mono (tsub_le_tsub_right (add_le_add (h ω) le_rfl) _)

private theorem cusSum_zero_time (P₀ P₁ : Measure X) (f : ℝ≥0∞ → ℝ≥0∞) :
    cusSum P₀ P₁ f (fun _ => ((0 : ℕ) : WithTop ℕ)) = 0 := by
  unfold cusSum
  refine tsum_eq_zero_iff.2 fun k => ?_
  have : {ω : ℕ → X | (k : WithTop ℕ) < ((0 : ℕ) : WithTop ℕ)} = ∅ := by
    ext ω
    simp
  rw [this, Measure.restrict_empty, lintegral_zero_measure]

private theorem cusSum_one_le_measure (P₀ P₁ : Measure X) {T : (ℕ → X) → WithTop ℕ}
    (k : ℕ) : Measure.infinitePi (fun _ : ℕ => P₀) {ω | (k : WithTop ℕ) < T ω} ≤
      cusSum P₀ P₁ (fun _ => 1) T := by
  refine le_trans (le_of_eq ?_) (le_tsum _ k)
  simp

/-- **Main case: stopping times with finite mean.** -/
private theorem cusDelay_le_lordenDelay (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {c : ℝ} (hc : 0 < c)
    (hD : cusDelay P₀ P₁ h₁₀ h₀₁ c ≠ ∞)
    (hEN : cusSum P₀ P₁ (fun _ => 1) (cusumTime P₀ P₁ h₁₀ h₀₁ c) ≠ ∞)
    {T : (ℕ → X) → WithTop ℕ} (hT : IsStoppingTime (observationFiltration X) T)
    (hET : cusSum P₀ P₁ (fun _ => 1) T ≠ ∞)
    (hγ : cusSum P₀ P₁ (fun _ => 1) (cusumTime P₀ P₁ h₁₀ h₀₁ c) ≤ cusSum P₀ P₁ (fun _ => 1) T) :
    cusDelay P₀ P₁ h₁₀ h₀₁ c ≤ lordenDelay P₀ P₁ T := by
  set N := cusumTime P₀ P₁ h₁₀ h₀₁ c
  set D := cusDelay P₀ P₁ h₁₀ h₀₁ c
  set μ := Measure.infinitePi (fun _ : ℕ => P₀)
  set E : ((ℕ → X) → WithTop ℕ) → ℝ≥0∞ := fun T => cusSum P₀ P₁ (fun _ => 1) T with hEdef
  set R : ((ℕ → X) → WithTop ℕ) → ℝ≥0∞ := fun T => cusSum P₀ P₁ (cusCost D) T with hRdef
  -- `E_∞[N] ≥ 1`
  have hEN0 : E N ≠ 0 := by
    refine (lt_of_lt_of_le ?_ (cusSum_one_le_measure P₀ P₁ 0)).ne'
    have : {ω | ((0 : ℕ) : WithTop ℕ) < N ω} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le (by exact_mod_cast zero_lt_one)
        (le_hittingAfter (u := pageCusum P₀ P₁ h₁₀ h₀₁) (s := Set.Ici c) (n := 1) ω)
    rw [this, measure_univ]
    exact one_pos
  obtain ⟨S, hS, hlag⟩ := exists_lagrange P₀ P₁ h₁₀ h₀₁ hc hD hEN
  -- the multiplier is at least `D`
  have hRN : D * E N ≤ R N := mul_lintegral_le_cusSum_cusCost P₀ P₁ h₁₀ h₀₁ c
  have hSD : D ≤ S := by
    have h0 := hlag (fun _ => ((0 : ℕ) : WithTop ℕ)) (isStoppingTime_const _ 0)
      (by rw [cusSum_zero_time]; exact ENNReal.zero_ne_top)
    rw [cusSum_zero_time, cusSum_zero_time, mul_zero, add_zero, zero_add] at h0
    exact (ENNReal.mul_le_mul_iff_left hEN0 hEN).1 (hRN.trans h0)
  -- `D E_∞[T] ≤ E_∞[∑_{k<T} r(U_k)]`
  have hRT : D * E T ≤ R T := by
    have hlagT := hlag T hT hET
    set δ := E T - E N
    have hETeq : E T = E N + δ := (add_tsub_cancel_of_le hγ).symm
    have hSN : S * E N ≠ ∞ := ENNReal.mul_ne_top hS hEN
    have h1 : R N + S * δ ≤ R T := by
      refine (ENNReal.add_le_add_iff_right hSN).1 ?_
      calc R N + S * δ + S * E N = R N + S * E T := by rw [hETeq, mul_add]; ring
        _ ≤ R T + S * E N := hlagT
    calc D * E T = D * E N + D * δ := by rw [hETeq, mul_add]
      _ ≤ R N + S * δ := add_le_add hRN (by gcongr)
      _ ≤ R T := h1
  have hBA := mul_cusSum_le_of_cusCost P₀ P₁ hD hET hRT
  have hAJ := cusSum_max_le P₀ P₁ h₁₀ h₀₁ hT
  -- `0 < E_∞[∑_{k<T} (1 - U_k)⁺] < ∞`
  have hB0 : cusSum P₀ P₁ (fun u => 1 - u) T ≠ 0 := by
    intro hB
    have h0 : μ {ω | ((0 : ℕ) : WithTop ℕ) < T ω} = 0 := by
      have := (le_tsum _ 0).trans_eq hB
      simpa [cusU] using this
    have hE0 : E T = 0 := by
      refine tsum_eq_zero_iff.2 fun k => ?_
      simp only [setLIntegral_const, one_mul]
      refine measure_mono_null (fun ω (hω : (k : WithTop ℕ) < T ω) => ?_) h0
      exact lt_of_le_of_lt (by exact_mod_cast Nat.zero_le k) hω
    exact hEN0 (le_antisymm (hγ.trans_eq hE0) zero_le)
  have hBtop : cusSum P₀ P₁ (fun u => 1 - u) T ≠ ∞ :=
    ne_top_of_le_ne_top hET (cusSum_mono P₀ P₁ (fun _ => tsub_le_self) T)
  exact (ENNReal.mul_le_mul_iff_left hB0 hBtop).1 (hBA.trans hAJ)

/-- **Moustakides' theorem: optimality of CUSUM under Lorden's criterion.** Let `P₀ ≠ P₁` be
mutually absolutely continuous, let `c > 0`, and let `γ` be the mean time to false alarm
`E_∞[N_c]` of the CUSUM alarm `N_c = inf {n ≥ 1 : W_n ≥ c}`. Then `N_c` minimises Lorden's
worst-case delay `sup_ν ess sup E_ν[(T - ν + 1)⁺ | X₁, …, X_{ν-1}]` among all stopping times `T`
with `E_∞[T] ≥ γ` (Moustakides 1986, as stated in Lai 2001, §3, p. 316; Lorden 1971 had proved
asymptotic optimality as `γ → ∞`). Lai writes CUSUM with the statistic
`max_{1 ≤ k ≤ n} ∑_{i=k}^{n} log L(Xᵢ)`; for `c > 0` it crosses `c` at the same time as Page's
statistic `W_n` used here (Veeravalli–Banerjee, remark after equation (48)). -/
theorem cusumTime_lordenDelay_le {P₀ P₁ : Measure X} [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (hne : P₀ ≠ P₁) {c : ℝ}
    (hc : 0 < c) {γ : ℝ≥0∞}
    (hγ : ∫⁻ ω, ((show ℕ∞ from cusumTime P₀ P₁ h₁₀ h₀₁ c ω) : ℝ≥0∞)
      ∂Measure.infinitePi (fun _ : ℕ => P₀) = γ)
    {T : (ℕ → X) → WithTop ℕ} (hT : IsStoppingTime (observationFiltration X) T)
    (hTγ : γ ≤ ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀)) :
    lordenDelay P₀ P₁ (cusumTime P₀ P₁ h₁₀ h₀₁ c) ≤ lordenDelay P₀ P₁ T := by
  set N := cusumTime P₀ P₁ h₁₀ h₀₁ c
  have hN := isStoppingTime_cusumTime P₀ P₁ h₁₀ h₀₁ c
  obtain ⟨δ, hδ, hpos⟩ := exists_measure_le_llr_pos P₀ P₁ h₁₀ hne
  have hD : cusDelay P₀ P₁ h₁₀ h₀₁ c ≠ ∞ :=
    (lintegral_cusumTime_lt_top P₀ P₁ h₁₀ h₀₁ c P₁ hδ
      (hpos.trans_le (measure_le_llr_le P₀ P₁ h₁₀ hδ))).ne
  have hEN : cusSum P₀ P₁ (fun _ => 1) N ≠ ∞ := by
    rw [cusSum_one P₀ P₁ hN]
    exact (lintegral_cusumTime_lt_top P₀ P₁ h₁₀ h₀₁ c P₀ hδ hpos).ne
  have hγ' : cusSum P₀ P₁ (fun _ => 1) N = γ := by rw [cusSum_one P₀ P₁ hN, hγ]
  refine (lordenDelay_cusumTime_le P₀ P₁ h₁₀ h₀₁ c).trans ?_
  by_cases hET : cusSum P₀ P₁ (fun _ => 1) T = ∞
  · -- truncate `T` at a large time
    set μ := Measure.infinitePi (fun _ : ℕ => P₀)
    have htend := ENNReal.tendsto_nat_tsum fun k => μ {ω | (k : WithTop ℕ) < T ω}
    have hET' : ∑' k : ℕ, μ {ω | (k : WithTop ℕ) < T ω} = ∞ := by
      rw [← hET]
      unfold cusSum
      simp only [setLIntegral_const, one_mul]
      rfl
    rw [hET'] at htend
    obtain ⟨n, hn⟩ := (htend.eventually (lt_mem_nhds
      (lt_top_iff_ne_top.2 hEN))).exists
    have hTn : IsStoppingTime (observationFiltration X) fun ω => min (T ω) (n : WithTop ℕ) :=
      hT.min_const n
    have hEn : cusSum P₀ P₁ (fun _ => 1) (fun ω => min (T ω) n) =
        ∑ k ∈ range n, μ {ω | (k : WithTop ℕ) < T ω} := by
      unfold cusSum
      rw [← tsum_ite_lt_eq]
      refine tsum_congr fun k => ?_
      simp only [setLIntegral_const, one_mul, lt_min_iff]
      by_cases hk : k < n
      · rw [ite_eq_left hk]
        congr 1
        ext ω
        simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
        exact fun _ => by exact_mod_cast hk
      · rw [ite_eq_right hk]
        have : {ω | (k : WithTop ℕ) < T ω ∧ (k : WithTop ℕ) < (n : WithTop ℕ)} = ∅ := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
          exact fun _ h => hk (by exact_mod_cast h)
        rw [this, measure_empty]
    have hEnfin : cusSum P₀ P₁ (fun _ => 1) (fun ω => min (T ω) n) ≠ ∞ := by
      rw [hEn]
      exact ENNReal.sum_ne_top.2 fun k _ => measure_ne_top _ _
    refine (cusDelay_le_lordenDelay P₀ P₁ h₁₀ h₀₁ hc hD hEN hTn hEnfin
      (by rw [hEn]; exact hn.le)).trans ?_
    exact lordenDelay_mono P₀ P₁ fun ω => min_le_left _ _
  · refine cusDelay_le_lordenDelay P₀ P₁ h₁₀ h₀₁ hc hD hEN hT hET ?_
    rw [hγ', cusSum_one P₀ P₁ hT]
    exact hTγ

end MeasureTheory
