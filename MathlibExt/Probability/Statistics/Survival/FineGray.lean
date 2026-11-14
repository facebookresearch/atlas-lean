/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MathlibExt.Probability.Statistics.Survival.CoxPartialLikelihood
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The Fine–Gray subdistribution hazard model

A subject has a failure time `T` and a failure cause `J`. The **cumulative incidence function**
of cause `c` is `F_c(t) = P(T ≤ t, J = c)`. Fine and Gray (1999) define the **subdistribution
hazard** of cause `c` by keeping the subjects that failed from a competing cause in the risk
event,

  `λ*_c(t) = lim_{h → 0+} P(t ≤ T < t + h, J = c | T ≥ t or (T < t and J ≠ c)) / h`,

and model it by proportional subdistribution hazards `λ*_c(t; x) = λ₀(t) exp ⟪β, x⟫`.

## Main definitions

* `cif`, `cifBefore`: `F_c(t)` and its left limit `F_c(t-) = P(T < t, J = c)`.
* `subdistRiskSet`, `subdistHazardQuotient`, `HasSubdistHazardAt`, `subdistHazard`: the risk
  event `{T ≥ t} ∪ {T < t, J ≠ c}`, the conditional difference quotient (with Mathlib's
  conditional measure `P[|·]`), the statement that it converges as `h → 0+`, and its limit.
* `cumSubdistHazard`: `Λ*_c(t) = ∫₀ᵗ λ*_c`.
* `IsPropSubdistHazards`: the proportional subdistribution hazards model.
* `fgRiskSet`, `fgPartialLikelihood`, `fgLogPartialLikelihood`: the Fine–Gray risk set (subjects
  under observation plus earlier competing-event subjects) and partial likelihood.
* `fgWeight`, `fgWeightedPartialLikelihood`: the inverse-probability-of-censoring weights and the
  weighted partial likelihood used under censoring.

## Main results

* `hasSubdistHazardAt_of_hasDerivWithinAt_cifBefore`: `λ*_c(t) = f / (1 - F_c(t-))` when `F_c(·-)`
  has right derivative `f` at `t`; `hasSubdistHazardAt_of_hasDerivWithinAt`: the same with
  `F_c(t)` for a continuous `F_c`.
* `one_sub_cif_eq`, `cif_eq_one_sub_exp`: **the link to the cumulative incidence function**,
  `F_c(t) = 1 - exp (-Λ*_c(t))` for `T > 0`, `F_c` continuous on `[0, t]`, differentiable on
  `(0, t)` with integrable derivative, and `F_c(t) < 1`.
* `IsPropSubdistHazards.cif_eq`, `IsPropSubdistHazards.cif_eq_rpow`: **CIF regression**,
  `F_c(t; x) = 1 - exp (-exp ⟪β, x⟫ Λ₀(t)) = 1 - (1 - F_c(t; 0)) ^ exp ⟪β, x⟫`.
* `mem_fgRiskSet_of_competing`, `notMem_fgRiskSet_of_censored`, `notMem_fgRiskSet_of_cause`:
  competing-event subjects stay at risk; censored and cause-`c` subjects leave it.
* `fgPartialLikelihood_eq_partialLikelihood`: the Fine–Gray partial likelihood is Cox's partial
  likelihood after moving competing-event times past every observed time; hence
  `log_fgPartialLikelihood` and `concaveOn_fgLogPartialLikelihood` (concavity in `β`).
* `fgPartialLikelihood_eq_of_noCompeting`: without competing events it is Cox's partial
  likelihood; `fgWeightedPartialLikelihood_one`: with censoring survival `G ≡ 1` the weighted
  partial likelihood is the risk-set one.

## Scope

The CIF link assumes `F_c` continuous on `[0, t]` and differentiable on `(0, t)`; the hazard
is a right limit (`h → 0+`).
The large-sample theory of the Fine–Gray estimator (consistency and asymptotic normality of the
weighted partial-likelihood estimator, the variance estimator), the score and information of
the weighted partial likelihood, and the Kaplan–Meier estimation of the censoring survival `G`
are not formalized here.

## References

* J. P. Fine and R. J. Gray, *A proportional hazards model for the subdistribution of a
  competing risk*, J. Amer. Statist. Assoc. 94 (1999), 496–509.
* D. R. Cox, *Regression models and life-tables*, J. Roy. Statist. Soc. Ser. B 34 (1972),
  187–220.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.FineGray

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- `t ↦ t + h` maps right neighbourhoods of `0` to right neighbourhoods of `t`. -/
private lemma tendsto_add_nhdsGT (t : ℝ) : Tendsto (fun h : ℝ => t + h) (𝓝[>] 0) (𝓝[>] t) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun h hh => ?_⟩
  · have : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · simpa using hh

section Population

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- The cumulative incidence function `F_c(t) = P(T ≤ t, J = c)` of cause `c`. -/
noncomputable def cif (P : Measure Ω) (T : Ω → ℝ) (J : Ω → ι) (c : ι) (t : ℝ) : ℝ :=
  P.real {ω | T ω ≤ t ∧ J ω = c}

/-- The left limit `F_c(t-) = P(T < t, J = c)` of the cumulative incidence function. -/
noncomputable def cifBefore (P : Measure Ω) (T : Ω → ℝ) (J : Ω → ι) (c : ι) (t : ℝ) : ℝ :=
  P.real {ω | T ω < t ∧ J ω = c}

/-- The Fine–Gray risk event at time `t` for cause `c`: the subject has not failed before `t`,
or has failed before `t` from a cause other than `c`, `{T ≥ t} ∪ {T < t, J ≠ c}`. -/
def subdistRiskSet (T : Ω → ℝ) (J : Ω → ι) (c : ι) (t : ℝ) : Set Ω :=
  {ω | t ≤ T ω} ∪ {ω | T ω < t ∧ J ω ≠ c}

/-- The event `{t ≤ T < t + h, J = c}` of a cause-`c` failure in `[t, t + h)`. -/
def causeEventIn (T : Ω → ℝ) (J : Ω → ι) (c : ι) (t h : ℝ) : Set Ω :=
  {ω | t ≤ T ω ∧ T ω < t + h ∧ J ω = c}

/-- The difference quotient `P(t ≤ T < t + h, J = c | T ≥ t or (T < t and J ≠ c)) / h` whose
limit as `h → 0+` is the subdistribution hazard. -/
noncomputable def subdistHazardQuotient (P : Measure Ω) (T : Ω → ℝ) (J : Ω → ι) (c : ι)
    (t h : ℝ) : ℝ :=
  (P[|subdistRiskSet T J c t]).real (causeEventIn T J c t h) / h

/-- `HasSubdistHazardAt P T J c t l`: the subdistribution hazard of cause `c` at time `t` exists
and equals `l`,
`λ*_c(t) = lim_{h → 0+} P(t ≤ T < t + h, J = c | T ≥ t or (T < t and J ≠ c)) / h = l`. -/
def HasSubdistHazardAt (P : Measure Ω) (T : Ω → ℝ) (J : Ω → ι) (c : ι) (t l : ℝ) : Prop :=
  Tendsto (subdistHazardQuotient P T J c t) (𝓝[>] 0) (𝓝 l)

/-- The **Fine–Gray subdistribution hazard** of cause `c` at time `t`,
`λ*_c(t) = lim_{h → 0+} P(t ≤ T < t + h, J = c | T ≥ t or (T < t and J ≠ c)) / h`
(junk value when the limit does not exist). -/
noncomputable def subdistHazard (P : Measure Ω) (T : Ω → ℝ) (J : Ω → ι) (c : ι) (t : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (subdistHazardQuotient P T J c t)

/-- The cumulative subdistribution hazard `Λ*_c(t) = ∫₀ᵗ λ*_c(s) ds`. -/
noncomputable def cumSubdistHazard (P : Measure Ω) (T : Ω → ℝ) (J : Ω → ι) (c : ι) (t : ℝ) :
    ℝ :=
  ∫ s in (0 : ℝ)..t, subdistHazard P T J c s

variable {P : Measure Ω} {T : Ω → ℝ} {J : Ω → ι} {c : ι}

/-- An existing subdistribution hazard is the value of `subdistHazard`. -/
theorem HasSubdistHazardAt.subdistHazard_eq {t l : ℝ} (h : HasSubdistHazardAt P T J c t l) :
    subdistHazard P T J c t = l :=
  h.limUnder_eq

omit [MeasurableSpace Ω] in
/-- The complement of the risk event is `{T < t, J = c}`. -/
theorem compl_subdistRiskSet (t : ℝ) :
    (subdistRiskSet T J c t)ᶜ = {ω | T ω < t ∧ J ω = c} := by
  ext ω
  simp only [subdistRiskSet, mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_and, not_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, not_not.1 (h2 h1)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun _ h => h h2⟩

omit [MeasurableSpace Ω] in
/-- A cause-`c` failure in `[t, t + h)` lies in the risk event at `t`. -/
theorem causeEventIn_subset (t h : ℝ) : causeEventIn T J c t h ⊆ subdistRiskSet T J c t :=
  fun _ hω => Or.inl hω.1

variable (hT : Measurable T) (hJ : MeasurableSet {ω | J ω = c})
include hT hJ

/-- The event `{T < t, J = c}` is measurable. -/
theorem measurableSet_cifBeforeSet (t : ℝ) : MeasurableSet {ω | T ω < t ∧ J ω = c} :=
  (measurableSet_lt hT measurable_const).inter hJ

/-- The risk event is measurable. -/
theorem measurableSet_subdistRiskSet (t : ℝ) : MeasurableSet (subdistRiskSet T J c t) := by
  rw [← compl_compl (subdistRiskSet T J c t), compl_subdistRiskSet]
  exact (measurableSet_cifBeforeSet hT hJ t).compl

/-- The risk event has probability `1 - F_c(t-)`. -/
theorem measureReal_subdistRiskSet [IsProbabilityMeasure P] (t : ℝ) :
    P.real (subdistRiskSet T J c t) = 1 - cifBefore P T J c t := by
  rw [← compl_compl (subdistRiskSet T J c t), probReal_compl_eq_one_sub
    (measurableSet_subdistRiskSet hT hJ t).compl, compl_subdistRiskSet, cifBefore]

/-- `P(t ≤ T < t + h, J = c) = F_c((t + h)-) - F_c(t-)` for `h ≥ 0`. -/
theorem measureReal_causeEventIn [IsFiniteMeasure P] {t h : ℝ} (hh : 0 ≤ h) :
    P.real (causeEventIn T J c t h) = cifBefore P T J c (t + h) - cifBefore P T J c t := by
  have hsub : {ω | T ω < t ∧ J ω = c} ⊆ {ω | T ω < t + h ∧ J ω = c} :=
    fun ω hω => ⟨by linarith [hω.1], hω.2⟩
  have heq : causeEventIn T J c t h = {ω | T ω < t + h ∧ J ω = c} \ {ω | T ω < t ∧ J ω = c} := by
    ext ω
    simp only [causeEventIn, Set.mem_sdiff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h2, h3⟩, fun h => absurd h.1 (not_lt.2 h1)⟩
    · rintro ⟨⟨h2, h3⟩, h1⟩
      exact ⟨le_of_not_gt fun h => h1 ⟨h, h3⟩, h2, h3⟩
  rw [heq, measureReal_sdiff hsub (measurableSet_cifBeforeSet hT hJ t), cifBefore, cifBefore]

/-- The subdistribution-hazard difference quotient in terms of `F_c(·-)`. -/
theorem subdistHazardQuotient_eq [IsProbabilityMeasure P] {t h : ℝ} (hh : 0 ≤ h) :
    subdistHazardQuotient P T J c t h =
      (cifBefore P T J c (t + h) - cifBefore P T J c t) / h / (1 - cifBefore P T J c t) := by
  rw [subdistHazardQuotient, measureReal_def, cond_apply (measurableSet_subdistRiskSet hT hJ t),
    ENNReal.toReal_mul, ENNReal.toReal_inv, inter_eq_right.2 (causeEventIn_subset t h),
    ← measureReal_def, ← measureReal_def, measureReal_subdistRiskSet hT hJ,
    measureReal_causeEventIn hT hJ hh]
  ring

/-- **The subdistribution hazard, general form** (Fine and Gray 1999): if `F_c(·-)` has right
derivative `f` at `t`, then `λ*_c(t) = f / (1 - F_c(t-))`. (When `F_c(t-) = 1` the risk event is
null and both sides are `0` by the conventions `P[·|∅] = 0` and `x / 0 = 0`.) -/
theorem hasSubdistHazardAt_of_hasDerivWithinAt_cifBefore [IsProbabilityMeasure P] {t f : ℝ}
    (hd : HasDerivWithinAt (cifBefore P T J c) f (Ici t) t) :
    HasSubdistHazardAt P T J c t (f / (1 - cifBefore P T J c t)) := by
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).1 hd.Ioi_of_Ici
  refine ((hs.comp (tendsto_add_nhdsGT t)).div_const _).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left,
    subdistHazardQuotient_eq hT hJ hh.le]

omit hT hJ in
/-- At a continuity point of the cumulative incidence function, `F_c(t-) = F_c(t)`. -/
theorem cifBefore_eq_cif_of_continuousAt [IsFiniteMeasure P] {t : ℝ}
    (hc : ContinuousAt (cif P T J c) t) : cifBefore P T J c t = cif P T J c t := by
  set A : ℕ → Set Ω := fun n => {ω | T ω ≤ t - 1 / ((n : ℝ) + 1) ∧ J ω = c}
  have hmono : Monotone A := fun n m hnm ω hω =>
    ⟨hω.1.trans (by linarith [Nat.one_div_le_one_div (α := ℝ) hnm]), hω.2⟩
  have hU : (⋃ n, A n) = {ω | T ω < t ∧ J ω = c} := by
    ext ω
    simp only [A, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨n, h1, h2⟩
      exact ⟨h1.trans_lt (by have := Nat.one_div_pos_of_nat (α := ℝ) (n := n); linarith), h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h1)
      exact ⟨n, by linarith, h2⟩
  have h1 : Tendsto (fun n => P.real (A n)) atTop (𝓝 (cifBefore P T J c t)) := by
    have := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp (tendsto_measure_iUnion_atTop
      (μ := P) hmono)
    rw [hU] at this
    exact this
  have hu : Tendsto (fun n : ℕ => t - 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_nhds_unique h1 (hc.tendsto.comp hu)

/-- **The subdistribution hazard of a continuous cumulative incidence function**: if `F_c` is
continuous on a right neighbourhood of `t` and has right derivative `f` at `t`, then
`λ*_c(t) = f / (1 - F_c(t))`. -/
theorem hasSubdistHazardAt_of_hasDerivWithinAt [IsProbabilityMeasure P] {t f : ℝ}
    (hc : ∀ᶠ s in 𝓝[≥] t, ContinuousAt (cif P T J c) s)
    (hd : HasDerivWithinAt (cif P T J c) f (Ici t) t) :
    HasSubdistHazardAt P T J c t
      (f / (1 - cif P T J c t)) := by
  have hEq : cifBefore P T J c =ᶠ[𝓝[≥] t] cif P T J c :=
    hc.mono fun s hs => cifBefore_eq_cif_of_continuousAt hs
  have ht : cifBefore P T J c t = cif P T J c t := hEq.self_of_nhdsWithin self_mem_Ici
  rw [← ht]
  exact hasSubdistHazardAt_of_hasDerivWithinAt_cifBefore hT hJ (hd.congr_of_eventuallyEq hEq ht)

omit hT hJ in
/-- The cumulative incidence function is non-decreasing. -/
theorem cif_mono [IsFiniteMeasure P] : Monotone (cif P T J c) :=
  fun _ _ hst => measureReal_mono fun _ hω => ⟨hω.1.trans hst, hω.2⟩

/-- **Link between the subdistribution hazard and the cumulative incidence function**
(Fine and Gray 1999, Section 2): if `F_c` is continuous on `[0, t]` and differentiable on
`(0, t)` with integrable derivative, and `F_c(t) < 1`, then
`1 - F_c(t) = (1 - F_c(0)) exp (-Λ*_c(t))`, where
`Λ*_c(t) = ∫₀ᵗ λ*_c` is the integral of the subdistribution hazard defined by the limit. -/
theorem one_sub_cif_eq [IsProbabilityMeasure P] {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hc : ContinuousOn (cif P T J c) (Icc 0 t))
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt (cif P T J c) (f s) s)
    (hf : IntervalIntegrable f volume 0 t) (hlt : cif P T J c t < 1) :
    1 - cif P T J c t = (1 - cif P T J c 0) * Real.exp (-cumSubdistHazard P T J c t) := by
  set F := cif P T J c with hFdef
  have hmono : Monotone F := cif_mono
  have hpos : ∀ s ∈ Icc 0 t, 0 < 1 - F s := fun s hs => by linarith [hmono hs.2]
  -- the subdistribution hazard is `f / (1 - F)` on `(0, t)`
  have hhaz : ∀ s ∈ Ioo 0 t, subdistHazard P T J c s = f s / (1 - F s) := fun s hs => by
    have hds := (hd s hs).hasDerivWithinAt (s := Ici s)
    refine (hasSubdistHazardAt_of_hasDerivWithinAt hT hJ ?_ hds).subdistHazard_eq
    filter_upwards [Ico_mem_nhdsGE hs.2] with u hu
    exact (hd u ⟨hs.1.trans_le hu.1, hu.2⟩).continuousAt
  -- `-log (1 - F)` is an antiderivative of `f / (1 - F)`
  have hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun u => -Real.log (1 - F u)) (f s / (1 - F s)) s :=
    fun s hs => by
      have h := ((hasDerivAt_const s (1 : ℝ)).sub (hd s hs)).log
        (hpos s (Ioo_subset_Icc_self hs)).ne'
      exact h.neg.congr_deriv (by simp only [Pi.sub_apply]; ring)
  have hcont : ContinuousOn (fun u => -Real.log (1 - F u)) (Icc 0 t) :=
    ((continuousOn_const.sub hc).log fun s hs => (hpos s hs).ne').neg
  have hint : IntervalIntegrable (fun s => f s / (1 - F s)) volume 0 t := by
    simp only [div_eq_mul_inv]
    refine hf.mul_continuousOn ?_
    rw [uIcc_of_le ht]
    exact (continuousOn_const.sub hc).inv₀ fun s hs => (hpos s hs).ne'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
  have hΛ : cumSubdistHazard P T J c t = -Real.log (1 - F t) + Real.log (1 - F 0) := by
    rw [cumSubdistHazard, ← sub_neg_eq_add, ← hFTC]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(countable_singleton t).ae_notMem volume] with s hst hs
    rw [uIoc_of_le ht] at hs
    exact hhaz s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
  rw [hΛ, neg_add, neg_neg, ← sub_eq_add_neg, Real.exp_sub, Real.exp_log (hpos t ⟨ht, le_rfl⟩),
    Real.exp_log (hpos 0 ⟨le_rfl, ht⟩)]
  field_simp [(hpos 0 ⟨le_rfl, ht⟩).ne']

omit hT hJ in
/-- If `T > 0` almost surely then `F_c(0) = 0`. -/
theorem cif_zero_of_ae_pos [IsFiniteMeasure P] (hpos : ∀ᵐ ω ∂P, 0 < T ω) : cif P T J c 0 = 0 := by
  have h0 : P {ω | T ω ≤ 0 ∧ J ω = c} = 0 :=
    measure_mono_null (fun ω hω => not_lt.2 hω.1) (ae_iff.1 hpos)
  simp [cif, measureReal_def, h0]

/-- **Cumulative incidence from the subdistribution hazard** (Fine and Gray 1999, Section 2):
for a failure time `T > 0` with `F_c` continuous on `[0, t]`, differentiable on `(0, t)` with
integrable derivative, and `F_c(t) < 1`, `F_c(t) = 1 - exp (-Λ*_c(t))`. -/
theorem cif_eq_one_sub_exp [IsProbabilityMeasure P] (hpos : ∀ᵐ ω ∂P, 0 < T ω) {t : ℝ}
    (ht : 0 ≤ t) {f : ℝ → ℝ} (hc : ContinuousOn (cif P T J c) (Icc 0 t))
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt (cif P T J c) (f s) s)
    (hf : IntervalIntegrable f volume 0 t) (hlt : cif P T J c t < 1) :
    cif P T J c t = 1 - Real.exp (-cumSubdistHazard P T J c t) := by
  have h := one_sub_cif_eq hT hJ ht hc hd hf hlt
  rw [cif_zero_of_ae_pos hpos, sub_zero, one_mul] at h
  linarith

end Population

section PSH

variable {Ω ι : Type*} [MeasurableSpace Ω] {p : ℕ}

/-- The **proportional subdistribution hazards model** (Fine and Gray 1999, Section 2): for every
covariate vector `x`, the law `P x` of `(T, J)` given covariate `x` has subdistribution hazard
`λ*_c(t; x) = λ₀(t) exp ⟪β, x⟫` for cause `c` at every time `t ≥ 0`. -/
def IsPropSubdistHazards (P : (Fin p → ℝ) → Measure Ω) (T : Ω → ℝ) (J : Ω → ι) (c : ι)
    (hazard₀ : ℝ → ℝ) (β : Fin p → ℝ) : Prop :=
  ∀ x t, 0 ≤ t → HasSubdistHazardAt (P x) T J c t (hazard₀ t * Real.exp (β ⬝ᵥ x))

variable {P : (Fin p → ℝ) → Measure Ω} {T : Ω → ℝ} {J : Ω → ι} {c : ι} {hazard₀ : ℝ → ℝ}
  {β : Fin p → ℝ}

/-- Under proportional subdistribution hazards the cumulative subdistribution hazard factors as
`Λ*_c(t; x) = exp ⟪β, x⟫ ∫₀ᵗ λ₀`. -/
theorem IsPropSubdistHazards.cumSubdistHazard_eq (h : IsPropSubdistHazards P T J c hazard₀ β)
    (x : Fin p → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cumSubdistHazard (P x) T J c t = Real.exp (β ⬝ᵥ x) * ∫ s in (0 : ℝ)..t, hazard₀ s := by
  rw [cumSubdistHazard, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  rw [(h x s hs.1).subdistHazard_eq, mul_comm]

variable (hT : Measurable T) (hJ : MeasurableSet {ω | J ω = c})
include hT hJ

/-- **Fine–Gray CIF regression** (Fine and Gray 1999, Section 2): under proportional
subdistribution hazards, `F_c(t; x) = 1 - exp (-exp ⟪β, x⟫ Λ₀(t))` with `Λ₀(t) = ∫₀ᵗ λ₀`,
provided `T > 0` almost surely, `F_c(·; x)` is continuous on `[0, t]` and differentiable on
`(0, t)` with integrable derivative, and `F_c(t; x) < 1`. -/
theorem IsPropSubdistHazards.cif_eq (h : IsPropSubdistHazards P T J c hazard₀ β)
    (x : Fin p → ℝ) [IsProbabilityMeasure (P x)] (hpos : ∀ᵐ ω ∂P x, 0 < T ω) {t : ℝ}
    (ht : 0 ≤ t) {f : ℝ → ℝ} (hc : ContinuousOn (cif (P x) T J c) (Icc 0 t))
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt (cif (P x) T J c) (f s) s)
    (hf : IntervalIntegrable f volume 0 t) (hlt : cif (P x) T J c t < 1) :
    cif (P x) T J c t = 1 - Real.exp (-(Real.exp (β ⬝ᵥ x) * ∫ s in (0 : ℝ)..t, hazard₀ s)) := by
  rw [cif_eq_one_sub_exp hT hJ hpos ht hc hd hf hlt, h.cumSubdistHazard_eq x ht]

/-- **Fine–Gray CIF regression, baseline form**: under proportional subdistribution hazards,
`F_c(t; x) = 1 - (1 - F_c(t; 0)) ^ exp ⟪β, x⟫`. -/
theorem IsPropSubdistHazards.cif_eq_rpow (h : IsPropSubdistHazards P T J c hazard₀ β)
    (x : Fin p → ℝ) [IsProbabilityMeasure (P x)] [IsProbabilityMeasure (P 0)]
    (hpos : ∀ᵐ ω ∂P x, 0 < T ω) (hpos₀ : ∀ᵐ ω ∂P 0, 0 < T ω) {t : ℝ} (ht : 0 ≤ t)
    {f f₀ : ℝ → ℝ} (hc : ContinuousOn (cif (P x) T J c) (Icc 0 t))
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt (cif (P x) T J c) (f s) s)
    (hf : IntervalIntegrable f volume 0 t) (hlt : cif (P x) T J c t < 1)
    (hc₀ : ContinuousOn (cif (P 0) T J c) (Icc 0 t))
    (hd₀ : ∀ s ∈ Ioo 0 t, HasDerivAt (cif (P 0) T J c) (f₀ s) s)
    (hf₀ : IntervalIntegrable f₀ volume 0 t) (hlt₀ : cif (P 0) T J c t < 1) :
    cif (P x) T J c t = 1 - (1 - cif (P 0) T J c t) ^ Real.exp (β ⬝ᵥ x) := by
  have h₀ := h.cif_eq hT hJ 0 hpos₀ ht hc₀ hd₀ hf₀ hlt₀
  rw [dotProduct_zero, Real.exp_zero, one_mul] at h₀
  rw [h.cif_eq hT hJ x hpos ht hc hd hf hlt, h₀, sub_sub_cancel, ← Real.exp_mul]
  congr 2
  ring

end PSH

section PartialLikelihood

open Finset Real MathlibExt.Probability.Statistics.CoxPartialLikelihood

variable {ι : Type*} [DecidableEq ι] {n p : ℕ}

/-- The **Fine–Gray risk set** at the observed time of subject `i`, for cause `c`
(Fine and Gray 1999, Section 3, without censoring of competing-event subjects): the subjects
still under observation, `X_l ≥ X_i`, together with those observed to fail from a cause other
than `c` before `X_i`. The status `ε l` is `none` for a censored subject and `some c'` for a
failure from cause `c'`. -/
noncomputable def fgRiskSet (X : Fin n → ℝ) (ε : Fin n → Option ι) (c : ι) (i : Fin n) :
    Finset (Fin n) :=
  {l | X i ≤ X l ∨ (X l < X i ∧ ε l ≠ none ∧ ε l ≠ some c)}

/-- The **Fine–Gray partial likelihood** for cause `c`,
`∏_{i : εᵢ = c} exp ⟪β, xᵢ⟫ / ∑_{l ∈ R*(Xᵢ)} exp ⟪β, x_l⟫`, where `R*` is the Fine–Gray risk set
that keeps competing-event subjects at risk. -/
noncomputable def fgPartialLikelihood (X : Fin n → ℝ) (ε : Fin n → Option ι) (c : ι)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) : ℝ :=
  ∏ i with ε i = some c, exp (β ⬝ᵥ x i) / ∑ l ∈ fgRiskSet X ε c i, exp (β ⬝ᵥ x l)

/-- The Fine–Gray log partial likelihood
`∑_{i : εᵢ = c} (⟪β, xᵢ⟫ - log ∑_{l ∈ R*(Xᵢ)} exp ⟪β, x_l⟫)`. -/
noncomputable def fgLogPartialLikelihood (X : Fin n → ℝ) (ε : Fin n → Option ι) (c : ι)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) : ℝ :=
  ∑ i with ε i = some c, (β ⬝ᵥ x i - log (∑ l ∈ fgRiskSet X ε c i, exp (β ⬝ᵥ x l)))

/-- The Fine–Gray weight of subject `l` at the observed time `X_i` of a cause-`c` failure, given a
censoring survival function `G` (Fine and Gray 1999, Section 3): the product of the weight
`r_l(X_i) G(X_i) / G(min(X_l, X_i))` and the indicator that `l` has no cause-`c` failure before
`X_i`, that is, `1` while `l` is under
observation, `G(X_i) / G(X_l)` if `l` failed from a competing cause before `X_i`, and `0`
otherwise. -/
noncomputable def fgWeight (X : Fin n → ℝ) (ε : Fin n → Option ι) (c : ι) (G : ℝ → ℝ)
    (l i : Fin n) : ℝ :=
  if X i ≤ X l then 1 else if ε l ≠ none ∧ ε l ≠ some c then G (X i) / G (X l) else 0

/-- The **inverse-probability-of-censoring weighted Fine–Gray partial likelihood**
`∏_{i : εᵢ = c} exp ⟪β, xᵢ⟫ / ∑_l w_l(X_i) exp ⟪β, x_l⟫` (Fine and Gray 1999, Section 3), with
`w` the weight `fgWeight`; in practice `G` is the Kaplan–Meier estimate of the censoring
survival function. -/
noncomputable def fgWeightedPartialLikelihood (X : Fin n → ℝ) (ε : Fin n → Option ι) (c : ι)
    (G : ℝ → ℝ) (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) : ℝ :=
  ∏ i with ε i = some c, exp (β ⬝ᵥ x i) / ∑ l, fgWeight X ε c G l i * exp (β ⬝ᵥ x l)

variable (X : Fin n → ℝ) (ε : Fin n → Option ι) (c : ι)

/-- Membership in the Fine–Gray risk set. -/
theorem mem_fgRiskSet {i l : Fin n} :
    l ∈ fgRiskSet X ε c i ↔ X i ≤ X l ∨ (X l < X i ∧ ε l ≠ none ∧ ε l ≠ some c) := by
  simp [fgRiskSet]

/-- The Cox risk set is contained in the Fine–Gray risk set. -/
theorem riskSet_subset_fgRiskSet (i : Fin n) : riskSet X i ⊆ fgRiskSet X ε c i := fun l hl =>
  (mem_fgRiskSet X ε c).2 (Or.inl (by simpa [riskSet] using hl))

/-- **Competing-event subjects stay at risk**: a subject observed to fail from a cause other
than `c` belongs to every Fine–Gray risk set. -/
theorem mem_fgRiskSet_of_competing {l : Fin n} (hl : ε l ≠ none ∧ ε l ≠ some c) (i : Fin n) :
    l ∈ fgRiskSet X ε c i := by
  rw [mem_fgRiskSet]
  rcases le_or_gt (X i) (X l) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hl⟩

/-- A subject censored before `X_i` is not in the Fine–Gray risk set at `X_i`. -/
theorem notMem_fgRiskSet_of_censored {i l : Fin n} (hl : ε l = none) (hlt : X l < X i) :
    l ∉ fgRiskSet X ε c i := by
  rw [mem_fgRiskSet]
  rintro (h | ⟨-, h, -⟩)
  · exact absurd h (not_le.2 hlt)
  · exact h hl

/-- A subject that failed from cause `c` before `X_i` is not in the Fine–Gray risk set at
`X_i`. -/
theorem notMem_fgRiskSet_of_cause {i l : Fin n} (hl : ε l = some c) (hlt : X l < X i) :
    l ∉ fgRiskSet X ε c i := by
  rw [mem_fgRiskSet]
  rintro (h | ⟨-, -, h⟩)
  · exact absurd h (not_le.2 hlt)
  · exact h hl

/-- Without censoring (`G ≡ 1`) the Fine–Gray weight is the indicator of the Fine–Gray risk
set. -/
theorem fgWeight_one (l i : Fin n) :
    fgWeight X ε c (fun _ => 1) l i = if l ∈ fgRiskSet X ε c i then 1 else 0 := by
  unfold fgWeight
  have hm := mem_fgRiskSet X ε c (i := i) (l := l)
  by_cases h1 : X i ≤ X l
  · rw [ite_eq_left h1, ite_eq_left (hm.2 (Or.inl h1))]
  · by_cases h3 : ε l ≠ none ∧ ε l ≠ some c
    · rw [ite_eq_right h1, ite_eq_left h3, ite_eq_left (hm.2 (Or.inr ⟨not_le.1 h1, h3⟩)),
        div_one]
    · rw [ite_eq_right h1, ite_eq_right h3,
        ite_eq_right fun h => (hm.1 h).elim h1 fun h => h3 h.2]

/-- With `G ≡ 1` the weighted Fine–Gray partial likelihood is the risk-set Fine–Gray partial
likelihood. -/
theorem fgWeightedPartialLikelihood_one (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    fgWeightedPartialLikelihood X ε c (fun _ => 1) x β = fgPartialLikelihood X ε c x β := by
  refine prod_congr rfl fun i _ => ?_
  simp only [fgWeight_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

/-- Competing-event times moved past every observed time: `X_l` for a subject without a
competing event, and `∑_m |X_m|` for a subject that failed from a cause other than `c`. -/
noncomputable def fgTime (l : Fin n) : ℝ :=
  if ε l ≠ none ∧ ε l ≠ some c then ∑ m, |X m| else X l

/-- For a cause-`c` failure `i`, the Fine–Gray risk set is the Cox risk set of the data with the
competing-event times moved to `∑_m |X_m|`. -/
theorem fgRiskSet_eq_riskSet_fgTime {i : Fin n} (hi : ε i = some c) :
    fgRiskSet X ε c i = riskSet (fgTime X ε c) i := by
  have hti : fgTime X ε c i = X i := by simp [fgTime, hi]
  ext l
  simp only [mem_fgRiskSet, riskSet, Finset.mem_filter, Finset.mem_univ, true_and, hti]
  by_cases hl : ε l ≠ none ∧ ε l ≠ some c
  · have hle : X i ≤ ∑ m, |X m| :=
      (le_abs_self _).trans (single_le_sum (f := fun m => |X m|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i))
    simp only [fgTime, ite_eq_left hl, hle, iff_true]
    rcases le_or_gt (X i) (X l) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hl⟩
  · simp only [fgTime, ite_eq_right hl]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact h
      · exact absurd h hl
    · exact Or.inl

/-- The cause-`c` event indicator `δᵢ = (εᵢ = c)`. -/
def causeIndicator (i : Fin n) : Bool := decide (ε i = some c)

/-- The cause-`c` events selected by `causeIndicator` are the indices with `εᵢ = c`. -/
lemma filter_causeIndicator :
    Finset.univ.filter (fun i : Fin n => causeIndicator ε c i = true) =
      Finset.univ.filter (fun i => ε i = some c) := by
  ext i
  simp [causeIndicator]

/-- **The Fine–Gray partial likelihood is a Cox partial likelihood** for the data with the
competing-event times moved past every observed time and cause-`c` failures as the events. -/
theorem fgPartialLikelihood_eq_partialLikelihood (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    fgPartialLikelihood X ε c x β =
      partialLikelihood (fgTime X ε c) (causeIndicator ε c) x β := by
  rw [fgPartialLikelihood, partialLikelihood, filter_causeIndicator]
  refine prod_congr rfl fun i hi => ?_
  rw [fgRiskSet_eq_riskSet_fgTime X ε c (by simpa using hi)]

/-- The Fine–Gray log partial likelihood is the corresponding Cox log partial likelihood. -/
theorem fgLogPartialLikelihood_eq_logPartialLikelihood (x : Fin n → Fin p → ℝ)
    (β : Fin p → ℝ) :
    fgLogPartialLikelihood X ε c x β =
      logPartialLikelihood (fgTime X ε c) (causeIndicator ε c) x β := by
  rw [fgLogPartialLikelihood, logPartialLikelihood, filter_causeIndicator]
  refine sum_congr rfl fun i hi => ?_
  rw [fgRiskSet_eq_riskSet_fgTime X ε c (by simpa using hi)]

/-- The logarithm of the Fine–Gray partial likelihood is the Fine–Gray log partial
likelihood. -/
theorem log_fgPartialLikelihood (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    log (fgPartialLikelihood X ε c x β) = fgLogPartialLikelihood X ε c x β := by
  rw [fgPartialLikelihood_eq_partialLikelihood, log_partialLikelihood,
    fgLogPartialLikelihood_eq_logPartialLikelihood]

/-- **Concavity of the Fine–Gray log partial likelihood** on `ℝᵖ`. -/
theorem concaveOn_fgLogPartialLikelihood (x : Fin n → Fin p → ℝ) :
    ConcaveOn ℝ Set.univ (fgLogPartialLikelihood X ε c x) := by
  have h : fgLogPartialLikelihood X ε c x =
      logPartialLikelihood (fgTime X ε c) (causeIndicator ε c) x :=
    funext (fgLogPartialLikelihood_eq_logPartialLikelihood X ε c x)
  rw [h]
  exact concaveOn_logPartialLikelihood _ _ _

/-- **No competing events**: if every subject is censored or fails from cause `c`, the
Fine–Gray risk set is the Cox risk set. -/
theorem fgRiskSet_eq_riskSet (hε : ∀ l, ε l = none ∨ ε l = some c) (i : Fin n) :
    fgRiskSet X ε c i = riskSet X i := by
  ext l
  simp only [mem_fgRiskSet, riskSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨-, h1, h2⟩)
    · exact h
    · exact (hε l).elim (fun h => absurd h h1) fun h => absurd h h2
  · exact Or.inl

/-- **No competing events**: the Fine–Gray partial likelihood is Cox's partial likelihood. -/
theorem fgPartialLikelihood_eq_of_noCompeting (hε : ∀ l, ε l = none ∨ ε l = some c)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    fgPartialLikelihood X ε c x β = partialLikelihood X (causeIndicator ε c) x β := by
  rw [fgPartialLikelihood, partialLikelihood, filter_causeIndicator]
  simp only [fgRiskSet_eq_riskSet X ε c hε]

end PartialLikelihood

end MathlibExt.Probability.Statistics.FineGray
