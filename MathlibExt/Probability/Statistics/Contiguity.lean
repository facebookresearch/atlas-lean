/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Contiguity and Le Cam's first and third lemmas under local asymptotic normality

Let `P` be a probability measure and `Qₙ = exp(Λₙ) · P` probability measures with densities
`exp Λₙ` with respect to `P`, where `Λₙ` is the log-likelihood ratio. The sequence is *locally
asymptotically normal* (LAN) with central sequence `Sₙ` and local parameter `h` if
`Sₙ → N(0, v)` in distribution under `P` and `Λₙ - h Sₙ → -h² v / 2` in `P`-probability, so that
`Λₙ → N(-h² v / 2, h² v)` under `P`.

## Main results

* `gaussianReal_withDensity_exp`: exponential tilting of a centered Gaussian,
  `exp(h x - h² v / 2) · N(0, v) = N(h v, v)`.
* `isContiguous_withDensity_exp` (Le Cam's first lemma): under LAN, `Qₙ` is contiguous with
  respect to `P`: `P(Aₙ) → 0` implies `Qₙ(Aₙ) → 0`.
* `tendstoInDistribution_withDensity_exp` (Le Cam's third lemma, LAN case): under LAN,
  `Sₙ → N(h v, v)` in distribution under `Qₙ`.
* `IsContiguous.tendsto_measure_abs_sub_ge`: contiguity transfers convergence in probability.

All measures live on one measurable space; the case of varying sample spaces reduces to this
one by transporting the measures along a common map (as in
`LikelihoodRatioLocalPower`).

## References

* L. Le Cam, "Locally asymptotically normal families of distributions", Univ. California
  Publ. Statist. 3 (1960) 37–98.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), ch. 6 (Definition 6.3, Lemma 6.4,
  Example 6.5, Theorem 6.6).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MathlibExt.Probability.Statistics.Contiguity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The sequence of measures `Q n` is **contiguous** with respect to `P n` (`Q ◁ P`): every
sequence of measurable sets whose `P n`-measure tends to `0` has `Q n`-measure tending to `0`.

Source: van der Vaart (1998), Definition 6.3. -/
def IsContiguous (Q P : ℕ → Measure Ω) : Prop :=
  ∀ A : ℕ → Set Ω, (∀ n, MeasurableSet (A n)) →
    Tendsto (fun n => P n (A n)) atTop (𝓝 0) → Tendsto (fun n => Q n (A n)) atTop (𝓝 0)

/-- **Exponential tilting of a centered Gaussian.** The law `N(0, v)` reweighted by the density
`exp(h x - h² v / 2)` is `N(h v, v)`. For `v = 0` both sides are the Dirac mass at `0`. -/
theorem gaussianReal_withDensity_exp (h : ℝ) (v : ℝ≥0) :
    (gaussianReal 0 v).withDensity
        (fun x => ENNReal.ofReal (Real.exp (h * x - h ^ 2 * v / 2))) =
      gaussianReal (h * v) v := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, NNReal.coe_zero, mul_zero, gaussianReal_zero_var,
      dirac_withDensity]
    simp
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.coe_nonneg (by exact_mod_cast Ne.symm hv)
  simp only [Pi.mul_apply, gaussianPDF_def, gaussianPDFReal_def]
  rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
  congr 3
  field_simp
  ring

/-- The tilting density `exp(h x - h² v / 2)` has total mass one under `N(0, v)`. -/
private theorem lintegral_exp_tilt (h : ℝ) (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (h * x - h ^ 2 * v / 2)) ∂gaussianReal 0 v = 1 := by
  have := congrArg (fun m : Measure ℝ => m Set.univ) (gaussianReal_withDensity_exp h v)
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, measure_univ]
    using this

/-- Integrability and unit mean of the tilting density. -/
private theorem integrable_exp_tilt (h : ℝ) (v : ℝ≥0) :
    Integrable (fun x => Real.exp (h * x - h ^ 2 * v / 2)) (gaussianReal 0 v) ∧
      ∫ x, Real.exp (h * x - h ^ 2 * v / 2) ∂gaussianReal 0 v = 1 := by
  have hm : Measurable fun x : ℝ => Real.exp (h * x - h ^ 2 * v / 2) := by fun_prop
  have hfin : HasFiniteIntegral (fun x => Real.exp (h * x - h ^ 2 * v / 2)) (gaussianReal 0 v) := by
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le),
      lintegral_exp_tilt]
    exact ENNReal.one_lt_top
  refine ⟨⟨hm.aestronglyMeasurable, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (Real.exp_pos _).le)
    hm.aestronglyMeasurable, lintegral_exp_tilt, ENNReal.toReal_one]

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The facts shared by Le Cam's first and third lemmas: the likelihood ratios `exp Λₙ` have
`P`-mean one, and `(Sₙ, Λₙ - h Sₙ)` converges jointly in distribution to `(G, -h² v / 2)`,
`G ~ N(0, v)` (Slutsky). -/
private theorem leCam_core {Λ S : ℕ → Ω → ℝ} {h : ℝ} {v : ℝ≥0}
    (hΛ : ∀ n, Measurable (Λ n))
    [∀ n, IsProbabilityMeasure (P.withDensity fun ω => ENNReal.ofReal (Real.exp (Λ n ω)))]
    (hS : TendstoInDistribution S atTop id (fun _ => P) (gaussianReal 0 v))
    (hLAN : TendstoInMeasure P (fun n ω => Λ n ω - h * S n ω) atTop
      (fun _ => -(h ^ 2 * v / 2))) :
    (∀ n, Integrable (fun ω => Real.exp (Λ n ω)) P ∧ ∫ ω, Real.exp (Λ n ω) ∂P = 1) ∧
    (∀ g : ℝ × ℝ →ᵇ ℝ, Tendsto (fun n => ∫ ω, g (S n ω, Λ n ω - h * S n ω) ∂P) atTop
      (𝓝 (∫ x, g (x, -(h ^ 2 * v / 2)) ∂gaussianReal 0 v))) := by
  refine ⟨fun n => ?_, fun g => ?_⟩
  · have hm : Measurable fun ω => Real.exp (Λ n ω) := Real.measurable_exp.comp (hΛ n)
    have h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (Λ n ω)) ∂P = 1 := by
      have := measure_univ (μ := P.withDensity fun ω => ENNReal.ofReal (Real.exp (Λ n ω)))
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    have hfin : HasFiniteIntegral (fun ω => Real.exp (Λ n ω)) P := by
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le), h1]
      exact ENNReal.one_lt_top
    refine ⟨⟨hm.aestronglyMeasurable, hfin⟩, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (Real.exp_pos _).le)
      hm.aestronglyMeasurable, h1, ENNReal.toReal_one]
  · have hD : ∀ n, AEMeasurable (fun ω => Λ n ω - h * S n ω) P := fun n =>
      (hΛ n).aemeasurable.sub ((hS.forall_aemeasurable n).const_mul h)
    have hpair := hS.prodMk_of_tendstoInMeasure_const S _ id hLAN hD
    have := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hpair.forall_aemeasurable hpair.aemeasurable_limit).1 hpair g
    simpa only [id] using this


omit [IsProbabilityMeasure P] in
/-- Truncation bound: for `Y ≥ 0` integrable and `|φ| ≤ C`,
`|∫ Y φ - ∫ φ min(Y, K)| ≤ C (∫ Y - ∫ min(Y, K))`. -/
private theorem abs_integral_sub_min_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Y φ : α → ℝ} {K C : ℝ} (hK : 0 ≤ K) (hYm : Measurable Y) (hY : Integrable Y μ)
    (hY0 : ∀ x, 0 ≤ Y x) (hφm : AEStronglyMeasurable φ μ) (hφ : ∀ x, |φ x| ≤ C) :
    |∫ x, Y x * φ x ∂μ - ∫ x, φ x * min (Y x) K ∂μ| ≤
      C * (∫ x, Y x ∂μ - ∫ x, min (Y x) K ∂μ) := by
  have hmin : Integrable (fun x => min (Y x) K) μ :=
    hY.mono' (hYm.min measurable_const).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hY0 x) hK)]; exact min_le_left _ _)
  have hφb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C := Eventually.of_forall fun x => hφ x
  have h1 : Integrable (fun x => Y x * φ x) μ := hY.mul_bdd hφm hφb
  have h2 : Integrable (fun x => φ x * min (Y x) K) μ := hmin.bdd_mul hφm hφb
  have hd : Integrable (fun x => Y x - min (Y x) K) μ := hY.sub hmin
  rw [← integral_sub h1 h2, ← integral_sub hY hmin, ← integral_const_mul]
  have := norm_integral_le_of_norm_le (hd.const_mul C)
    (f := fun x => Y x * φ x - φ x * min (Y x) K) (Eventually.of_forall fun x => by
      have e : Y x * φ x - φ x * min (Y x) K = (Y x - min (Y x) K) * φ x := by ring
      rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.2 (min_le_left _ _)),
        mul_comm]
      exact mul_le_mul_of_nonneg_right (hφ x) (sub_nonneg.2 (min_le_left _ _)))
  simpa only [Real.norm_eq_abs] using this

/-- The truncated means `∫ min(exp Λₙ, K) dP` converge to `∫ min(exp(h x - h² v / 2), K) dN(0, v)`,
and the latter tend to `1` as `K → ∞`. -/
private theorem leCam_trunc {Λ S : ℕ → Ω → ℝ} {h : ℝ} {v : ℝ≥0}
    (hΛ : ∀ n, Measurable (Λ n))
    [∀ n, IsProbabilityMeasure (P.withDensity fun ω => ENNReal.ofReal (Real.exp (Λ n ω)))]
    (hS : TendstoInDistribution S atTop id (fun _ => P) (gaussianReal 0 v))
    (hLAN : TendstoInMeasure P (fun n ω => Λ n ω - h * S n ω) atTop
      (fun _ => -(h ^ 2 * v / 2))) :
    (∀ K : ℝ, 0 ≤ K → Tendsto (fun n => ∫ ω, min (Real.exp (Λ n ω)) K ∂P) atTop
      (𝓝 (∫ x, min (Real.exp (h * x - h ^ 2 * v / 2)) K ∂gaussianReal 0 v))) ∧
    Tendsto (fun k : ℕ => ∫ x, min (Real.exp (h * x - h ^ 2 * v / 2)) (k : ℝ) ∂gaussianReal 0 v)
      atTop (𝓝 1) := by
  refine ⟨fun K hK => ?_, ?_⟩
  · set g : ℝ × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z : ℝ × ℝ => min (Real.exp (h * z.1 + z.2)) K) (by fun_prop) K (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.exp_pos _).le hK)]
        exact min_le_right _ _)
    have := (leCam_core hΛ hS hLAN).2 g
    simpa only [g, BoundedContinuousFunction.coe_ofNormedAddCommGroup, add_sub_cancel,
      ← sub_eq_add_neg] using this
  · obtain ⟨he, he1⟩ := integrable_exp_tilt h v
    rw [← he1]
    refine tendsto_integral_of_dominated_convergence _ (fun k => by fun_prop) he
      (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.exp_pos _).le k.cast_nonneg)]
      exact min_le_left _ _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈Real.exp (h * x - h ^ 2 * v / 2)⌉₊] with k hk
      exact (min_eq_left ((Nat.le_ceil _).trans (by exact_mod_cast hk))).symm

/-- **Le Cam's first lemma** (LAN case). Let `Qₙ = exp(Λₙ) · P` be probability measures. If
`Sₙ → N(0, v)` in distribution under `P` and `Λₙ - h Sₙ → -h² v / 2` in `P`-probability, then
`Qₙ` is contiguous with respect to `P`. This is the case of Le Cam's first lemma in which
`Λₙ → N(-σ²/2, σ²)` under `P`, `σ² = h² v`; the general form (any limit `L` of `dQₙ/dP` with
`E L = 1`) is not stated here.

Source: Le Cam (1960); van der Vaart (1998), Lemma 6.4 and Example 6.5. -/
theorem isContiguous_withDensity_exp {Λ S : ℕ → Ω → ℝ} {h : ℝ} {v : ℝ≥0}
    (hΛ : ∀ n, Measurable (Λ n))
    [∀ n, IsProbabilityMeasure (P.withDensity fun ω => ENNReal.ofReal (Real.exp (Λ n ω)))]
    (hS : TendstoInDistribution S atTop id (fun _ => P) (gaussianReal 0 v))
    (hLAN : TendstoInMeasure P (fun n ω => Λ n ω - h * S n ω) atTop
      (fun _ => -(h ^ 2 * v / 2))) :
    IsContiguous (fun n => P.withDensity fun ω => ENNReal.ofReal (Real.exp (Λ n ω)))
      (fun _ => P) := by
  intro A hA hPA
  have hL := (leCam_core hΛ hS hLAN).1
  obtain ⟨htr, hm⟩ := leCam_trunc hΛ hS hLAN
  set q : ℕ → ℝ := fun n => ∫ ω in A n, Real.exp (Λ n ω) ∂P with hq_def
  have hQ : ∀ n, P.withDensity (fun ω => ENNReal.ofReal (Real.exp (Λ n ω))) (A n) =
      ENNReal.ofReal (q n) := fun n => by
    rw [withDensity_apply _ (hA n), ofReal_integral_eq_lintegral_ofReal (hL n).1.integrableOn
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  simp only [hQ]
  rw [← ENNReal.ofReal_zero]
  refine ENNReal.tendsto_ofReal ?_
  have hq0 : ∀ n, 0 ≤ q n := fun n => setIntegral_nonneg (hA n) fun _ _ => (Real.exp_pos _).le
  have hbound : ∀ n (K : ℝ), 0 ≤ K →
      q n ≤ K * P.real (A n) + (1 - ∫ ω, min (Real.exp (Λ n ω)) K ∂P) := by
    intro n K hK
    have hLi := (hL n).1
    have hmin : Integrable (fun ω => min (Real.exp (Λ n ω)) K) P :=
      hLi.mono' ((Real.measurable_exp.comp (hΛ n)).min measurable_const).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.exp_pos _).le hK)]
          exact min_le_left _ _)
    have hdiff : Integrable (fun ω => Real.exp (Λ n ω) - min (Real.exp (Λ n ω)) K) P :=
      hLi.sub hmin
    calc q n = ∫ ω in A n, min (Real.exp (Λ n ω)) K ∂P +
          ∫ ω in A n, (Real.exp (Λ n ω) - min (Real.exp (Λ n ω)) K) ∂P := by
          rw [← integral_add hmin.integrableOn hdiff.integrableOn]
          simp only [hq_def, add_sub_cancel]
      _ ≤ ∫ ω in A n, K ∂P + ∫ ω, (Real.exp (Λ n ω) - min (Real.exp (Λ n ω)) K) ∂P :=
          add_le_add (setIntegral_mono_on hmin.integrableOn (integrableOn_const) (hA n)
            fun ω _ => min_le_right _ _)
            (setIntegral_le_integral hdiff (Eventually.of_forall fun ω =>
              sub_nonneg.2 (min_le_left _ _)))
      _ = K * P.real (A n) + (1 - ∫ ω, min (Real.exp (Λ n ω)) K ∂P) := by
          rw [setIntegral_const, integral_sub hLi hmin, (hL n).2, smul_eq_mul, mul_comm]
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hq0 n),
    fun ε hε => ?_⟩
  obtain ⟨k, hk⟩ := (hm.eventually (lt_mem_nhds (by linarith : 1 - ε / 2 < 1))).exists
  have hPA' : Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hPA
    simpa only [Function.comp_def, ENNReal.toReal_zero, measureReal_def] using this
  have h1 := (hPA'.const_mul (k : ℝ)).add ((htr k k.cast_nonneg).const_sub 1)
  have hlt : (k : ℝ) * 0 + (1 - ∫ x, min (Real.exp (h * x - h ^ 2 * v / 2)) (k : ℝ)
      ∂gaussianReal 0 v) < ε := by linarith
  filter_upwards [h1.eventually (gt_mem_nhds hlt)] with n hn
  exact (hbound n k k.cast_nonneg).trans_lt hn

/-- **Le Cam's third lemma** (LAN case). Let `Qₙ = exp(Λₙ) · P` be probability measures. If
`Sₙ → N(0, v)` in distribution under `P` and `Λₙ - h Sₙ → -h² v / 2` in `P`-probability, then
`Sₙ → N(h v, v)` in distribution under `Qₙ`. This is the case of Le Cam's third lemma for the
central sequence itself (covariance `h v` with `Λₙ`); the general form, for an arbitrary
statistic jointly asymptotically normal with `Λₙ`, is not stated here.

Source: Le Cam (1960); van der Vaart (1998), Theorem 6.6. -/
theorem tendstoInDistribution_withDensity_exp {Λ S : ℕ → Ω → ℝ} {h : ℝ} {v : ℝ≥0}
    (hΛ : ∀ n, Measurable (Λ n))
    [∀ n, IsProbabilityMeasure (P.withDensity fun ω => ENNReal.ofReal (Real.exp (Λ n ω)))]
    (hS : TendstoInDistribution S atTop id (fun _ => P) (gaussianReal 0 v))
    (hLAN : TendstoInMeasure P (fun n ω => Λ n ω - h * S n ω) atTop
      (fun _ => -(h ^ 2 * v / 2))) :
    TendstoInDistribution S atTop id
      (fun n => P.withDensity fun ω => ENNReal.ofReal (Real.exp (Λ n ω)))
      (gaussianReal (h * v) v) := by
  have hL := (leCam_core hΛ hS hLAN).1
  have hpair := (leCam_core hΛ hS hLAN).2
  obtain ⟨htr, hm⟩ := leCam_trunc hΛ hS hLAN
  obtain ⟨he, he1⟩ := integrable_exp_tilt h v
  have hSm := hS.forall_aemeasurable
  refine (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun n => (hSm n).mono_ac (withDensity_absolutelyContinuous _ _)) aemeasurable_id).2
    fun f => ?_
  have hQint : ∀ n, ∫ ω, f (S n ω) ∂(P.withDensity fun ω => ENNReal.ofReal (Real.exp (Λ n ω))) =
      ∫ ω, Real.exp (Λ n ω) * f (S n ω) ∂P := fun n => by
    rw [integral_withDensity_eq_integral_toReal_smul ((hΛ n).exp.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext ω
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have hlim : ∫ x, f (id x) ∂gaussianReal (h * v) v =
      ∫ x, Real.exp (h * x - h ^ 2 * v / 2) * f x ∂gaussianReal 0 v := by
    rw [← gaussianReal_withDensity_exp, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext x
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, id]
  rw [hlim]
  refine Tendsto.congr (fun n => (hQint n).symm) ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e : ℝ → ℝ := fun x => Real.exp (h * x - h ^ 2 * v / 2) with he_def
  set C : ℝ := ‖f‖ + 1 with hC_def
  have hC : 0 < C := by positivity
  have hfC : ∀ x, |f x| ≤ C := fun x =>
    (Real.norm_eq_abs (f x) ▸ f.norm_coe_le_norm x).trans (by linarith)
  have hε4 : 0 < ε / (4 * C) := by positivity
  obtain ⟨k, hk⟩ := (hm.eventually (lt_mem_nhds (by linarith : 1 - ε / (4 * C) < 1))).exists
  set K : ℝ := (k : ℝ) with hK_def
  have hK : 0 ≤ K := k.cast_nonneg
  set g : ℝ × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z : ℝ × ℝ => f z.1 * min (Real.exp (h * z.1 + z.2)) K) (by fun_prop) (C * K)
    (fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_min (Real.exp_pos _).le hK)]
      exact mul_le_mul (hfC _) (min_le_right _ _) (le_min (Real.exp_pos _).le hK) hC.le)
  have hp := hpair g
  simp only [g, BoundedContinuousFunction.coe_ofNormedAddCommGroup, add_sub_cancel,
    ← sub_eq_add_neg] at hp
  have ht := htr K hK
  have hmk : ∫ x, min (e x) K ∂gaussianReal 0 v ≤ 1 := by
    rw [← he1]
    exact integral_mono (he.mono' (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.exp_pos _).le hK)]
      exact min_le_left _ _)) he fun x => min_le_left _ _
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hp (ε / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 ht (ε / (4 * C)) hε4
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  rw [Real.dist_eq] at h1 h2 ⊢
  have hA := abs_integral_sub_min_le (μ := P) (Y := fun ω => Real.exp (Λ n ω)) hK
    (Real.measurable_exp.comp (hΛ n)) (hL n).1
    (fun _ => (Real.exp_pos _).le) (f.continuous.comp_aestronglyMeasurable
      (hSm n).aestronglyMeasurable) (fun ω => hfC (S n ω))
  have hB := abs_integral_sub_min_le (μ := gaussianReal 0 v) hK (by fun_prop : Measurable e) he
    (fun _ => (Real.exp_pos _).le) f.continuous.aestronglyMeasurable hfC
  rw [(hL n).2] at hA
  rw [he1] at hB
  have hk' : C * (1 - ∫ x, min (e x) K ∂gaussianReal 0 v) < ε / 4 := by
    have : 1 - ∫ x, min (e x) K ∂gaussianReal 0 v < ε / (4 * C) := by linarith
    calc C * (1 - ∫ x, min (e x) K ∂gaussianReal 0 v) < C * (ε / (4 * C)) :=
          mul_lt_mul_of_pos_left this hC
      _ = ε / 4 := by field_simp
  have hA' : C * (1 - ∫ ω, min (Real.exp (Λ n ω)) K ∂P) <
      C * (1 - ∫ x, min (e x) K ∂gaussianReal 0 v) + ε / 4 := by
    have : 1 - ∫ ω, min (Real.exp (Λ n ω)) K ∂P <
        1 - ∫ x, min (e x) K ∂gaussianReal 0 v + ε / (4 * C) := by
      have := (abs_lt.1 h2).1; linarith
    calc C * (1 - ∫ ω, min (Real.exp (Λ n ω)) K ∂P) <
        C * (1 - ∫ x, min (e x) K ∂gaussianReal 0 v + ε / (4 * C)) :=
          mul_lt_mul_of_pos_left this hC
      _ = C * (1 - ∫ x, min (e x) K ∂gaussianReal 0 v) + ε / 4 := by field_simp
  have htri := abs_sub_le (∫ ω, Real.exp (Λ n ω) * f (S n ω) ∂P)
    (∫ ω, f (S n ω) * min (Real.exp (Λ n ω)) K ∂P) (∫ x, e x * f x ∂gaussianReal 0 v)
  have htri2 := abs_sub_le (∫ ω, f (S n ω) * min (Real.exp (Λ n ω)) K ∂P)
    (∫ x, f x * min (e x) K ∂gaussianReal 0 v) (∫ x, e x * f x ∂gaussianReal 0 v)
  rw [abs_sub_comm (∫ x, f x * min (e x) K ∂gaussianReal 0 v)] at htri2
  linarith

omit [IsProbabilityMeasure P] in
/-- **Contiguity transfers convergence in probability.** If `Q ◁ P` (a fixed `P`) and the
measurable functions `T n` converge to `c` in `P`-probability, then
`Q n {ω | ε ≤ |T n ω - c|} → 0` for every `ε > 0`.

Source: van der Vaart (1998), ch. 6. -/
theorem IsContiguous.tendsto_measure_abs_sub_ge {Q : ℕ → Measure Ω}
    (hQP : IsContiguous Q (fun _ => P)) {T : ℕ → Ω → ℝ} (hT : ∀ n, Measurable (T n)) {c : ℝ}
    (h : TendstoInMeasure P T atTop (fun _ => c)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => Q n {ω | ε ≤ |T n ω - c|}) atTop (𝓝 0) := by
  refine hQP _ (fun n => measurableSet_le measurable_const
    (continuous_abs.measurable.comp ((hT n).sub_const c))) ?_
  simpa only [Real.dist_eq] using (tendstoInMeasure_iff_dist.1 h) ε hε

end MathlibExt.Probability.Statistics.Contiguity
