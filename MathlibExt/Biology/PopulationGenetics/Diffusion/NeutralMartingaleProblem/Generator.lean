/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
public import MathlibExt.Biology.PopulationGenetics.Diffusion.SemigroupMoments
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Markov processes with the neutral Wright–Fisher semigroup solve the martingale problem

`MathlibExt.Biology.PopulationGenetics.Diffusion.Semigroup` constructs the neutral
Wright–Fisher semigroup `wfSemigroup` on `C([0, 1], ℝ)` and identifies its generator
`L p = x (1 - x) / 2 · p''` on polynomials only, and
`MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess` states the martingale
problem `IsWrightFisherSolution σ ℱ μ X` for **all** `C²` test functions. This file connects the
two: a continuous `[0, 1]`-valued process that is adapted to a filtration `ℱ` and Markov with
respect to `ℱ` with transition semigroup `wfSemigroup` solves `IsWrightFisherSolution 0`.

The process and filtration are hypothesis variables: the Markov property is assumed in its
conditional-expectation form
`μ[g (X t) | ℱ s] = (wfSemigroup (t - s) g) (X s)` a.s. for `s ≤ t` and continuous `g` on
`[0, 1]` (states are read in `[0, 1]` through `Set.projIcc`). No particular realization of the
process is used.

## Main results

* `wfSemigroup_sub_eq_integral`: `P_T p - p = ∫₀ᵀ P_u (L p) du` in `C([0, 1], ℝ)` for every
  polynomial `p`.
* `exists_polynomial_near_contDiff_two`: a `C²` function is approximated uniformly on `[0, 1]`
  by polynomials together with its first and second derivatives.
* `isWrightFisherSolution_zero_of_markov`: the Markov property with the neutral semigroup implies
  the neutral martingale problem for `C²` test functions.

## Method

For a polynomial `p`, `s ≤ t` and `A ∈ ℱ s`, the Markov property turns
`∫_A p (X t) - ∫_A p (X s)` into `Λ (P_{t-s} p - p)` for the bounded functional
`Λ g = ∫_A g (X s)`, and, after Fubini, `∫_A ∫ₛᵗ (L p) (X r) dr` into `∫ₛᵗ Λ (P_{r-s} L p) dr`; the
semigroup identity equates the two. The time integral `ω ↦ ∫₀ᵗ g (X r ω) dr` is
`ℱ t`-measurable because `(r, ω) ↦ g (X (min r t) ω)` is continuous in `r` and
`ℱ t`-measurable in `ω`, hence jointly measurable. For a `C²` test function `f`, a polynomial with
`|p - f| ≤ ε` and `|p'' - f''| ≤ ε` on `[0, 1]` changes every term of the martingale identity by
at most a constant times `ε`, uniformly on the sample space, because `X` stays in `[0, 1]`;
letting `ε → 0` gives the identity for `f`, and hence the martingale property.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), ch. 1 (semigroups and generators), ch. 4, Prop. 1.7 (Markov processes solve the
  martingale problem for their generator), and ch. 10 (Wright–Fisher diffusion).
-/

@[expose] public section

open MeasureTheory Filter Topology Set Polynomial
open scoped NNReal ENNReal unitInterval

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem

open MathlibExt.Biology.PopulationGenetics.Diffusion (generator)
open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup

/-! ### The semigroup identity on polynomials -/

private theorem continuousOn_wfSemigroup_poly (q : ℝ[X]) :
    ContinuousOn (fun u : ℝ => wfSemigroup u (q.toContinuousMapOn I)) (Ici 0) := by
  intro u hu
  rcases (mem_Ici.1 hu).eq_or_lt with rfl | hu
  · have h := tendsto_wfSemigroup_nhdsGE_zero (q.toContinuousMapOn I)
    simpa [ContinuousWithinAt, wfSemigroup_zero] using h
  · exact (hasDerivAt_wfSemigroup_toContinuousMapOn q hu).continuousAt.continuousWithinAt

/-- **Semigroup identity on polynomials.** For a polynomial `p` and `T ≥ 0`, the neutral
Wright–Fisher semigroup satisfies `P_T p - p = ∫₀ᵀ P_u (L p) du` in `C([0, 1], ℝ)`, where
`L = polyGenerator` is the neutral generator `x (1 - x) / 2 · p''`.

Source: Ethier & Kurtz (1986), ch. 1, Prop. 1.5 (b), specialised to the polynomial core
derivative `hasDerivAt_wfSemigroup_toContinuousMapOn`. -/
theorem wfSemigroup_sub_eq_integral (p : ℝ[X]) {T : ℝ} (hT : 0 ≤ T) :
    wfSemigroup T (p.toContinuousMapOn I) - p.toContinuousMapOn I =
      ∫ u in (0 : ℝ)..T, wfSemigroup u ((polyGenerator p).toContinuousMapOn I) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT
    ((continuousOn_wfSemigroup_poly p).mono Icc_subset_Ici_self)
    (fun u hu => (hasDerivAt_wfSemigroup_toContinuousMapOn p hu.1).hasDerivWithinAt)
    (((continuousOn_wfSemigroup_poly _).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hT)]
  simp [wfSemigroup_zero]

/-! ### Measurability and boundedness of the time integrals -/

/-- A parametric interval integral of a Carathéodory integrand is strongly measurable. -/
private theorem stronglyMeasurable_intervalIntegral {α : Type*} [MeasurableSpace α]
    {u : ℝ → α → ℝ} (hc : ∀ a, Continuous fun r => u r a) (hm : ∀ r, StronglyMeasurable (u r))
    (a b : ℝ) : StronglyMeasurable fun x => ∫ r in a..b, u r x := by
  have H : StronglyMeasurable (Function.uncurry fun (x : α) (r : ℝ) => u r x) :=
    (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc hm).comp_measurable
      measurable_swap
  unfold intervalIntegral
  exact (H.integral_prod_right (ν := volume.restrict (Ioc a b))).sub
    (H.integral_prod_right (ν := volume.restrict (Ioc b a)))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

/-- The time integral `∫₀ᵗ g (X s) ds` of a continuous function along a continuous adapted
process is `ℱ t`-strongly measurable. -/
private theorem stronglyMeasurable_integral_comp (hcont : ∀ ω, Continuous fun t => X t ω)
    (hadapt : StronglyAdapted ℱ X) {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ≥0) :
    StronglyMeasurable[ℱ t] fun ω => ∫ s in (0 : ℝ)..(t : ℝ), g (X (Real.toNNReal s) ω) := by
  let u : ℝ → Ω → ℝ := fun r ω => g (X (Real.toNNReal (min r t)) ω)
  have hc : ∀ ω, Continuous fun r => u r ω := fun ω =>
    hg.comp ((hcont ω).comp (continuous_real_toNNReal.comp (continuous_id.min continuous_const)))
  have hm : ∀ r, StronglyMeasurable[ℱ t] (u r) := fun r =>
    hg.comp_stronglyMeasurable ((hadapt _).mono (ℱ.mono (Real.toNNReal_le_iff_le_coe.2
      (min_le_right _ _))))
  have H := @stronglyMeasurable_intervalIntegral Ω (ℱ t) u hc hm 0 t
  convert H using 1
  funext _
  refine intervalIntegral.integral_congr fun r hr => ?_
  have hr' : r ≤ t := by
    rw [uIcc_of_le (NNReal.coe_nonneg t)] at hr
    exact hr.2
  simp [u, min_eq_left hr']

/-- A bound for a continuous function on `[0, 1]`. -/
private theorem exists_bound_Icc {g : ℝ → ℝ} (hg : Continuous g) :
    ∃ B, ∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ B :=
  isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn

/-- The time integral `∫₀ᵗ g (X s) ds` of a continuous function along a `[0, 1]`-valued
process is bounded by `t` times a bound of `g` on `[0, 1]`. -/
private theorem norm_integral_comp_le (hmem : ∀ t ω, X t ω ∈ Icc (0 : ℝ) 1) {g : ℝ → ℝ}
    {B : ℝ} (hB : ∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ B) (t : ℝ≥0) (ω : Ω) :
    ‖∫ s in (0 : ℝ)..(t : ℝ), g (X (Real.toNNReal s) ω)‖ ≤ B * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (f := fun s => g (X (Real.toNNReal s) ω)) (C := B) fun s _ => hB _ (hmem _ ω)
  simpa using h

/-! ### Integrating continuous functions of a state against a finite measure -/

/-- A continuous function of a measurable `[0, 1]`-valued state is integrable. -/
private theorem integrable_continuousMap_comp {ν : Measure Ω} [IsFiniteMeasure ν] {Y : Ω → I}
    (hY : Measurable Y) (g : C(I, ℝ)) : Integrable (fun ω => g (Y ω)) ν :=
  Integrable.of_bound (g.continuous.measurable.comp hY).aestronglyMeasurable ‖g‖
    (ae_of_all _ fun _ => g.norm_coe_le_norm _)

/-- Integration of `g ∘ Y` against a finite measure, as a continuous linear functional of
`g ∈ C([0, 1], ℝ)`. -/
private noncomputable def integralCLM (ν : Measure Ω) [IsFiniteMeasure ν] {Y : Ω → I}
    (hY : Measurable Y) : C(I, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ ω, g (Y ω) ∂ν
      map_add' := fun f g => by
        simpa using integral_add (integrable_continuousMap_comp (ν := ν) hY f)
          (integrable_continuousMap_comp hY g)
      map_smul' := fun c g => by simpa using integral_const_mul (μ := ν) c fun ω => g (Y ω) }
    (ν.real univ) fun g => by
      have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun ω => g (Y ω)) (C := ‖g‖)
        (ae_of_all _ fun ω => g.norm_coe_le_norm _)
      simpa [mul_comm] using h

private theorem integralCLM_apply (ν : Measure Ω) [IsFiniteMeasure ν] {Y : Ω → I}
    (hY : Measurable Y) (g : C(I, ℝ)) : integralCLM ν hY g = ∫ ω, g (Y ω) ∂ν :=
  rfl

/-! ### The polynomial martingale identity -/

/-- The Markov property, integrated over an event of the past. -/
private theorem setIntegral_markov [IsFiniteMeasure μ] (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    {s t : ℝ≥0} (hst : s ≤ t) (g : C(I, ℝ)) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) ∂μ =
      ∫ ω in A, wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)) ∂μ := by
  have hY : Measurable fun ω => projIcc (0 : ℝ) 1 zero_le_one (X t ω) :=
    continuous_projIcc.measurable.comp ((hadapt t).mono (ℱ.le t)).measurable
  rw [← setIntegral_condExp (ℱ.le s) (integrable_continuousMap_comp hY g) hA]
  exact integral_congr_ae (ae_restrict_of_ae (hmarkov s t hst g))

private theorem eval_eq_toContinuousMapOn (q : ℝ[X]) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    q.eval x = q.toContinuousMapOn I (projIcc (0 : ℝ) 1 zero_le_one x) := by
  rw [toContinuousMapOn_apply, projIcc_of_mem _ hx]
  rfl

/-- **Polynomial Dynkin identity on events of the past.** -/
private theorem setIntegral_poly [IsFiniteMeasure μ] (hmem : ∀ t ω, X t ω ∈ Icc (0 : ℝ) 1)
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (p : ℝ[X]) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, p.eval (X t ω) ∂μ - ∫ ω in A, p.eval (X s ω) ∂μ =
      ∫ ω in A, (∫ r in (s : ℝ)..(t : ℝ), (polyGenerator p).eval (X (Real.toNNReal r) ω)) ∂μ := by
  have hmeas : ∀ r, Measurable (X r) := fun r => ((hadapt r).mono (ℱ.le r)).measurable
  have hY : Measurable fun ω => projIcc (0 : ℝ) 1 zero_le_one (X s ω) :=
    continuous_projIcc.measurable.comp (hmeas s)
  set Λ := integralCLM (μ.restrict A) hY with hΛ
  set Lp := (polyGenerator p).toContinuousMapOn I
  have hst' : (s : ℝ) ≤ t := hst
  -- Markov property in terms of `Λ`.
  have hmk : ∀ r : ℝ≥0, s ≤ r → ∀ q : ℝ[X],
      ∫ ω in A, q.eval (X r ω) ∂μ = Λ (wfSemigroup ((r : ℝ) - s) (q.toContinuousMapOn I)) := by
    intro r hr q
    simp_rw [eval_eq_toContinuousMapOn q (hmem r _)]
    rw [setIntegral_markov hadapt hmarkov hr _ hA, hΛ, integralCLM_apply]
  -- Left side: the semigroup identity.
  have hL : ∫ ω in A, p.eval (X t ω) ∂μ - ∫ ω in A, p.eval (X s ω) ∂μ =
      ∫ u in (0 : ℝ)..((t : ℝ) - s), Λ (wfSemigroup u Lp) := by
    rw [hmk t hst, hmk s le_rfl, sub_self, wfSemigroup_zero, one_apply_eq_self,
      ← map_sub, wfSemigroup_sub_eq_integral p (sub_nonneg.2 hst'),
      Λ.intervalIntegral_comp_comm]
    exact ((continuousOn_wfSemigroup_poly _).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc
      (sub_nonneg.2 hst')
  rw [hL]
  -- Right side: Fubini, then the Markov property at each intermediate time.
  have hjoint : StronglyMeasurable (Function.uncurry fun (ω : Ω) (r : ℝ) =>
      (polyGenerator p).eval (X (Real.toNNReal r) ω)) :=
    (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun r ω => (polyGenerator p).eval (X (Real.toNNReal r) ω))
      (fun ω => (polyGenerator p).continuous.comp ((hcont ω).comp continuous_real_toNNReal))
      (fun r => ((polyGenerator p).continuous.measurable.comp (hmeas _)).stronglyMeasurable)
      ).comp_measurable measurable_swap
  obtain ⟨B, hB⟩ := exists_bound_Icc (polyGenerator p).continuous
  have : IsFiniteMeasure (volume.restrict (Ioc (s : ℝ) t)) :=
    ⟨by simp [Real.volume_Ioc]⟩
  have hint : Integrable (Function.uncurry fun (ω : Ω) (r : ℝ) =>
      (polyGenerator p).eval (X (Real.toNNReal r) ω))
      ((μ.restrict A).prod (volume.restrict (Ioc (s : ℝ) t))) :=
    Integrable.of_bound hjoint.aestronglyMeasurable B (ae_of_all _ fun z => hB _ (hmem _ _))
  simp_rw [intervalIntegral.integral_of_le hst']
  rw [integral_integral_swap hint, ← intervalIntegral.integral_of_le hst']
  have hcongr : EqOn (fun r : ℝ => ∫ ω in A, (polyGenerator p).eval (X (Real.toNNReal r) ω) ∂μ)
      (fun r => Λ (wfSemigroup (r - s) Lp)) (uIcc (s : ℝ) t) := by
    intro r hr
    rw [uIcc_of_le hst'] at hr
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg s).trans hr.1
    have hsr : s ≤ Real.toNNReal r := Real.le_toNNReal_iff_coe_le hr0 |>.2 hr.1
    simp only [hmk _ hsr, Real.coe_toNNReal _ hr0, Lp]
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_comp_sub_right (fun u => Λ (wfSemigroup u Lp)), sub_self]

/-! ### `C²` polynomial approximation on `[0, 1]` -/

/-- A polynomial antiderivative. -/
private noncomputable def antideriv (q : ℝ[X]) : ℝ[X] :=
  q.sum fun n a => C (a / (n + 1)) * Polynomial.X ^ (n + 1)

private theorem derivative_antideriv (q : ℝ[X]) : derivative (antideriv q) = q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [antideriv, sum_add_index _ _ _ (fun n => by simp) (fun n a b => by
      rw [add_div, C_add, add_mul])]
    rw [derivative_add, ← antideriv, ← antideriv, hp, hq]
  | monomial n a =>
    rw [antideriv, sum_monomial_index _ _ (by simp), derivative_C_mul_X_pow,
      ← C_mul_X_pow_eq_monomial]
    congr 2
    push_cast
    field_simp

/-- **`C²` polynomial approximation.** A `C²` function on `ℝ` is approximated uniformly on
`[0, 1]` by a polynomial together with its first and second derivatives.

Source: integrate twice a Weierstrass approximation of `f''`
(`exists_polynomial_near_of_continuousOn`); the errors in `f'` and `f` follow from the mean value
inequality. -/
theorem exists_polynomial_near_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Icc (0 : ℝ) 1,
      |p.eval x - f x| ≤ ε ∧ |(derivative p).eval x - deriv f x| ≤ ε ∧
        |(derivative (derivative p)).eval x - deriv (deriv f) x| ≤ ε := by
  have hdf : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have hf2 : Continuous (deriv (deriv f)) := by
    have h := hf.continuous_iteratedDeriv 2 le_rfl
    simpa [iteratedDeriv_eq_iterate] using h
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 1 _ hf2.continuousOn ε hε
  set Q1 := antideriv q
  set Q2 := antideriv Q1
  refine ⟨C (f 0 - Q2.eval 0) + C (deriv f 0 - Q1.eval 0) * Polynomial.X + Q2, ?_⟩
  set p := C (f 0 - Q2.eval 0) + C (deriv f 0 - Q1.eval 0) * Polynomial.X + Q2
  have hp1 : derivative p = C (deriv f 0 - Q1.eval 0) + Q1 := by
    simp [p, Q2, derivative_antideriv]
  have hp2 : derivative (derivative p) = q := by
    simp [hp1, Q1, derivative_antideriv]
  -- Error in the first derivative.
  set g1 : ℝ → ℝ := fun x => (derivative p).eval x - deriv f x
  have hg1 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g1
      ((derivative (derivative p)).eval x - deriv (deriv f) x) (Icc 0 1) x := fun x _ =>
    ((Polynomial.hasDerivAt _ x).sub (hdf x).hasDerivAt).hasDerivWithinAt
  have hb1 : ∀ x ∈ Ico (0 : ℝ) 1, ‖(derivative (derivative p)).eval x - deriv (deriv f) x‖ ≤ ε :=
    fun x hx => by
      rw [hp2, Real.norm_eq_abs]
      exact (hq x (Ico_subset_Icc_self hx)).le
  have he1 : ∀ x ∈ Icc (0 : ℝ) 1, |g1 x| ≤ ε := by
    intro x hx
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hg1 hb1 x hx
    have h0 : g1 0 = 0 := by simp [g1, hp1]
    rw [h0, sub_zero, Real.norm_eq_abs, sub_zero] at h
    exact h.trans (mul_le_of_le_one_right hε.le hx.2)
  -- Error in the function.
  set g0 : ℝ → ℝ := fun x => p.eval x - f x
  have hg0 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g0 (g1 x) (Icc 0 1) x := fun x _ =>
    ((Polynomial.hasDerivAt _ x).sub (hf.differentiable two_ne_zero x).hasDerivAt).hasDerivWithinAt
  have hb0 : ∀ x ∈ Ico (0 : ℝ) 1, ‖g1 x‖ ≤ ε := fun x hx => he1 x (Ico_subset_Icc_self hx)
  refine fun x hx => ⟨?_, he1 x hx, by rw [hp2]; exact (hq x hx).le⟩
  · have h := norm_image_sub_le_of_norm_deriv_le_segment' hg0 hb0 x hx
    have h0 : g0 0 = 0 := by simp [g0, p]
    rw [h0, sub_zero, Real.norm_eq_abs, sub_zero] at h
    exact h.trans (mul_le_of_le_one_right hε.le hx.2)

/-! ### Passage from polynomials to `C²` test functions -/

private theorem integrable_comp [IsFiniteMeasure μ] (hmem : ∀ t ω, X t ω ∈ Icc (0 : ℝ) 1)
    (hadapt : StronglyAdapted ℱ X) {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ≥0) :
    Integrable (fun ω => g (X t ω)) μ := by
  obtain ⟨B, hB⟩ := exists_bound_Icc hg
  exact Integrable.of_bound
    (hg.measurable.comp ((hadapt t).mono (ℱ.le t)).measurable).aestronglyMeasurable B
    (ae_of_all _ fun ω => hB _ (hmem t ω))

private theorem integrable_integral_comp [IsFiniteMeasure μ]
    (hmem : ∀ t ω, X t ω ∈ Icc (0 : ℝ) 1) (hcont : ∀ ω, Continuous fun t => X t ω)
    (hadapt : StronglyAdapted ℱ X) {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ≥0) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ), g (X (Real.toNNReal s) ω)) μ := by
  obtain ⟨B, hB⟩ := exists_bound_Icc hg
  exact Integrable.of_bound
    ((stronglyMeasurable_integral_comp hcont hadapt hg t).mono (ℱ.le t)).aestronglyMeasurable
    (B * t) (ae_of_all _ fun ω => norm_integral_comp_le hmem hB t ω)

private theorem abs_integral_sub_le {ν : Measure Ω} [IsFiniteMeasure ν] {F G : Ω → ℝ}
    (hF : Integrable F ν) (hG : Integrable G ν) {c : ℝ} (h : ∀ ω, |F ω - G ω| ≤ c) :
    |∫ ω, F ω ∂ν - ∫ ω, G ω ∂ν| ≤ c * ν.real univ := by
  rw [← integral_sub hF hG]
  have h' := norm_integral_le_of_norm_le_const (μ := ν) (f := fun ω => F ω - G ω) (C := c)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact h ω)
  simpa using h'

/-- The increment of `∫₀ᵗ g (X r) dr` over an event of the past. -/
private noncomputable def incr (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (A : Set Ω) (f g : ℝ → ℝ)
    (s t : ℝ≥0) : ℝ :=
  (∫ ω in A, f (X t ω) ∂μ - ∫ ω in A, f (X s ω) ∂μ) -
    (∫ ω in A, (∫ r in (0 : ℝ)..(t : ℝ), g (X (Real.toNNReal r) ω)) ∂μ -
      ∫ ω in A, (∫ r in (0 : ℝ)..(s : ℝ), g (X (Real.toNNReal r) ω)) ∂μ)

private theorem incr_poly_eq_zero [IsFiniteMeasure μ] (hmem : ∀ t ω, X t ω ∈ Icc (0 : ℝ) 1)
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (p : ℝ[X]) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    incr μ X A (fun y => p.eval y) (fun y => (polyGenerator p).eval y) s t = 0 := by
  have hg := (polyGenerator p).continuous
  rw [incr, setIntegral_poly hmem hcont hadapt hmarkov p hst hA,
    ← integral_sub (integrable_integral_comp hmem hcont hadapt hg t).integrableOn
      (integrable_integral_comp hmem hcont hadapt hg s).integrableOn, sub_eq_zero]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun r => (polyGenerator p).eval
      (X (Real.toNNReal r) ω)) volume a b := fun a b =>
    (hg.comp ((hcont ω).comp continuous_real_toNNReal)).intervalIntegrable a b
  exact (intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)).symm

private theorem abs_generator_sub_le {f : ℝ → ℝ} {p : ℝ[X]} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |generator 0 f x - (polyGenerator p).eval x| ≤
      |(derivative (derivative p)).eval x - deriv (deriv f) x| := by
  have h : generator 0 f x - (polyGenerator p).eval x =
      x * (1 - x) / 2 * (deriv (deriv f) x - (derivative (derivative p)).eval x) := by
    simp only [generator, polyGenerator, eval_mul, eval_C, eval_X, eval_sub, eval_one]
    ring
  rw [h, abs_mul, abs_sub_comm (deriv (deriv f) x)]
  have h0 : 0 ≤ x * (1 - x) / 2 := by nlinarith [hx.1, hx.2]
  have h1 : x * (1 - x) / 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  rw [abs_of_nonneg h0]
  exact mul_le_of_le_one_left (abs_nonneg _) h1

private theorem incr_contDiff_eq_zero [IsFiniteMeasure μ] (hmem : ∀ t ω, X t ω ∈ Icc (0 : ℝ) 1)
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hLf : Continuous (generator 0 f)) {s t : ℝ≥0}
    (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    incr μ X A f (generator 0 f) s t = 0 := by
  set m := (μ.restrict A).real univ
  set K := m * (2 + t + s) + 1
  have hm : 0 ≤ m := measureReal_nonneg
  have hK : 0 < K := by positivity
  -- Each polynomial approximation gives an error bound.
  have hbound : ∀ ε > 0, |incr μ X A f (generator 0 f) s t| ≤ ε * K := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_contDiff_two hf hε
    have hg := (polyGenerator p).continuous
    have hd : ∀ u : ℝ≥0, |∫ ω in A, f (X u ω) ∂μ - ∫ ω in A, p.eval (X u ω) ∂μ| ≤ ε * m :=
      fun u => abs_integral_sub_le (integrable_comp hmem hadapt hf.continuous u).integrableOn
        (integrable_comp hmem hadapt p.continuous u).integrableOn fun ω => by
          rw [abs_sub_comm]
          exact (hp _ (hmem u ω)).1
    have hi : ∀ u : ℝ≥0,
        |∫ ω in A, (∫ r in (0 : ℝ)..(u : ℝ), generator 0 f (X (Real.toNNReal r) ω)) ∂μ -
          ∫ ω in A, (∫ r in (0 : ℝ)..(u : ℝ), (polyGenerator p).eval (X (Real.toNNReal r) ω)) ∂μ|
          ≤ ε * u * m := by
      intro u
      refine abs_integral_sub_le (integrable_integral_comp hmem hcont hadapt hLf u).integrableOn
        (integrable_integral_comp hmem hcont hadapt hg u).integrableOn fun ω => ?_
      have hi1 : IntervalIntegrable (fun r => generator 0 f (X (Real.toNNReal r) ω)) volume 0 u :=
        (hLf.comp ((hcont ω).comp continuous_real_toNNReal)).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun r => (polyGenerator p).eval (X (Real.toNNReal r) ω))
          volume 0 u :=
        (hg.comp ((hcont ω).comp continuous_real_toNNReal)).intervalIntegrable _ _
      rw [← intervalIntegral.integral_sub hi1 hi2]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := u)
        (f := fun r => generator 0 f (X (Real.toNNReal r) ω) -
          (polyGenerator p).eval (X (Real.toNNReal r) ω)) (C := ε) fun r _ =>
          (abs_generator_sub_le (hmem _ ω)).trans (hp _ (hmem _ ω)).2.2
      simpa using h
    have h0 := incr_poly_eq_zero hmem hcont hadapt hmarkov p hst hA
    have hdiff : incr μ X A f (generator 0 f) s t =
        incr μ X A f (generator 0 f) s t -
          incr μ X A (fun y => p.eval y) (fun y => (polyGenerator p).eval y) s t := by
      rw [h0, sub_zero]
    rw [hdiff]
    unfold incr
    calc _ ≤ ε * m + ε * m + ε * t * m + ε * s * m := by
          have := hd t; have := hd s; have := hi t; have := hi s
          rw [abs_le] at *
          constructor <;> linarith
      _ ≤ ε * K := by
          simp only [K]
          nlinarith [NNReal.coe_nonneg t, NNReal.coe_nonneg s]
  -- Letting `ε → 0`.
  by_contra hne
  have hpos : 0 < |incr μ X A f (generator 0 f) s t| := abs_pos.2 hne
  have h := hbound (|incr μ X A f (generator 0 f) s t| / (2 * K)) (by positivity)
  rw [div_mul_eq_mul_div, mul_comm (2 : ℝ) K, ← div_div, mul_div_assoc, div_self hK.ne',
    mul_one] at h
  linarith

/-- **Neutral Wright–Fisher martingale problem from the Markov property.** Let `X` be a
continuous `[0, 1]`-valued process adapted to a filtration `ℱ` under a finite measure `μ`, and
suppose `X` is Markov with respect to `ℱ` with the neutral Wright–Fisher transition semigroup:
for `s ≤ t` and every continuous `g` on `[0, 1]`,
`μ[g (X t) | ℱ s] = (wfSemigroup (t - s) g) (X s)` almost surely. Then `X` solves the neutral
Wright–Fisher martingale problem `IsWrightFisherSolution 0 ℱ μ X`: for every `C²` test function
`f`, `f (X t) - f (X 0) - ∫₀ᵗ (x (1 - x) / 2 · f'') (X s) ds` is an `ℱ`-martingale.

The semigroup is only known to have the generator `x (1 - x) / 2 · p''` on polynomials
(`hasDerivAt_wfSemigroup_toContinuousMapOn`). The proof derives the martingale identity on
polynomials from the Markov property, Fubini's theorem and the semigroup identity
`wfSemigroup_sub_eq_integral`, and passes to `C²` test functions through the simultaneous
uniform approximation of `f` and `f''` on `[0, 1]` by polynomials
(`exists_polynomial_near_contDiff_two`), the error terms being bounded uniformly on the
sample space.

Source: Ethier & Kurtz (1986), ch. 4, Prop. 1.7 (Markov processes solve the martingale problem
for their generator), and ch. 10 (polynomials as a core for the Wright–Fisher generator, here
replaced by direct `C²` approximation). -/
theorem isWrightFisherSolution_zero_of_markov [IsFiniteMeasure μ]
    (hmem : ∀ t ω, X t ω ∈ Icc (0 : ℝ) 1) (hcont : ∀ ω, Continuous fun t => X t ω)
    (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω))) :
    KimuraFixationProcess.IsWrightFisherSolution 0 ℱ μ X := by
  refine ⟨hmem, hcont, hadapt, fun f hf => ?_⟩
  have hf0 : Continuous f := hf.continuous
  have hf1 : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hf2 : Continuous (deriv (deriv f)) := by
    have h := hf.continuous_iteratedDeriv 2 le_rfl
    simpa [iteratedDeriv_eq_iterate] using h
  have hLf : Continuous (generator 0 f) := by
    unfold generator
    fun_prop
  set M : ℝ≥0 → Ω → ℝ := fun t ω => f (X t ω) - f (X 0 ω) -
    ∫ s in (0 : ℝ)..(t : ℝ), generator 0 f (X (Real.toNNReal s) ω) with hM
  have hadM : StronglyAdapted ℱ M := fun t =>
    ((hf0.comp_stronglyMeasurable (hadapt t)).sub
      (hf0.comp_stronglyMeasurable ((hadapt 0).mono (ℱ.mono (show (0 : ℝ≥0) ≤ t from bot_le))))).sub
      (stronglyMeasurable_integral_comp hcont hadapt hLf t)
  have hintM : ∀ t, Integrable (M t) μ := fun t =>
    ((integrable_comp hmem hadapt hf0 t).sub (integrable_comp hmem hadapt hf0 0)).sub
      (integrable_integral_comp hmem hcont hadapt hLf t)
  refine ⟨hadM, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hintM t)
    (fun A _ _ => (hintM s).integrableOn) (fun A hA _ => ?_)
    (hadM s).aestronglyMeasurable).symm
  have h := incr_contDiff_eq_zero hmem hcont hadapt hmarkov hf hLf hst hA
  have hi := fun u => integrable_comp (μ := μ) hmem hadapt hf0 u
  have hI := fun u => integrable_integral_comp (μ := μ) hmem hcont hadapt hLf u
  simp only [hM]
  have hs0 : Integrable (fun ω => f (X s ω) - f (X 0 ω)) μ := (hi s).sub (hi 0)
  have ht0 : Integrable (fun ω => f (X t ω) - f (X 0 ω)) μ := (hi t).sub (hi 0)
  rw [integral_sub hs0.integrableOn (hI s).integrableOn,
    integral_sub ht0.integrableOn (hI t).integrableOn,
    integral_sub (hi s).integrableOn (hi 0).integrableOn,
    integral_sub (hi t).integrableOn (hi 0).integrableOn]
  unfold incr at h
  linarith

end MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
