/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianExponentialTightness
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics










open Filter MeasureTheory Set Topology
open ProbabilityTheory

namespace StatMech.FrontierA


noncomputable def clippedPower (order : Nat) (A : Real) :
    BoundedContinuousFunction Real Real where
  toFun x := max (-|A|) (min (x ^ order) |A|)
  continuous_toFun := by fun_prop
  map_bounded' := by
    refine ⟨2 * |A|, ?_⟩
    intro x y
    rw [Real.dist_eq]
    have hbound (z : Real) :
        |max (-|A|) (min (z ^ order) |A|)| <= |A| := by
      rw [abs_le]
      constructor
      · exact le_max_left _ _
      · exact max_le (neg_le_self (abs_nonneg A)) (min_le_right _ _)
    calc
      |max (-|A|) (min (x ^ order) |A|) -
          max (-|A|) (min (y ^ order) |A|)| <=
          |max (-|A|) (min (x ^ order) |A|)| +
            |max (-|A|) (min (y ^ order) |A|)| := abs_sub _ _
      _ <= |A| + |A| := add_le_add (hbound x) (hbound y)
      _ = 2 * |A| := by ring

theorem clippedPower_eq_self
    (order : Nat) {A x : Real} (hA : 0 <= A) (hx : |x ^ order| <= A) :
    clippedPower order A x = x ^ order := by
  change max (-|A|) (min (x ^ order) |A|) = x ^ order
  rw [abs_of_nonneg hA]
  rw [min_eq_left (abs_le.mp hx).2]
  rw [max_eq_right]
  exact (abs_le.mp hx).1

theorem abs_sub_clippedPower_le
    (order : Nat) {A : Real} (hA : 0 <= A) (x : Real) :
    |x ^ order - clippedPower order A x| <= |x| ^ order := by
  change |x ^ order - max (-|A|) (min (x ^ order) |A|)| <= |x| ^ order
  rw [← abs_pow]
  by_cases hlow : x ^ order < -A
  · have hmin : min (x ^ order) A = x ^ order :=
      min_eq_left (hlow.le.trans (neg_le_self hA))
    rw [abs_of_nonneg hA, hmin, max_eq_left hlow.le]
    have hp : x ^ order <= 0 := hlow.le.trans (neg_nonpos.mpr hA)
    have hdiff : x ^ order - -A <= 0 := by linarith
    rw [abs_of_nonpos hdiff]
    rw [abs_of_nonpos hp]
    linarith
  · have hnegA : -A <= x ^ order := le_of_not_gt hlow
    by_cases hhigh : x ^ order <= A
    · rw [abs_of_nonneg hA, min_eq_left hhigh, max_eq_right hnegA,
        sub_self, abs_zero]
      exact abs_nonneg _
    · have hAhigh : A < x ^ order := lt_of_not_ge hhigh
      rw [abs_of_nonneg hA, min_eq_right hAhigh.le,
        max_eq_right (neg_le_self hA)]
      have hp : 0 <= x ^ order := hA.trans hAhigh.le
      have hdiff : 0 <= x ^ order - A := by linarith
      rw [abs_of_nonneg hdiff]
      rw [abs_of_nonneg hp]
      linarith


theorem integral_exp_abs_le_of_weakLimit_uniform
    (muN : Nat -> ProbabilityMeasure Real) (mu : ProbabilityMeasure Real)
    (hlim : Tendsto muN atTop (nhds mu))
    (a C : Real)
    (hint : forall n, Integrable (fun x : Real => Real.exp (a * |x|))
      (muN n : Measure Real))
    (hbound : forall n,
      (∫ x, Real.exp (a * |x|) ∂(muN n : Measure Real)) <= C) :
    (∫ x, Real.exp (a * |x|) ∂(mu : Measure Real)) <= C := by
  have hintLimit := integrable_exp_abs_of_weakLimit_uniform
    muN mu hlim a C hint hbound
  have htruncBound (n : Nat) :
      (∫ x, truncatedExpAbs a n x ∂(mu : Measure Real)) <= C := by
    have hconv :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim)
        (truncatedExpAbs a n)
    apply le_of_tendsto hconv
    filter_upwards with k
    exact (integral_mono (BoundedContinuousFunction.integrable _ _)
      (hint k) (truncatedExpAbs_le_exp a n)).trans (hbound k)
  have hconv : Tendsto
      (fun n => ∫ x, truncatedExpAbs a n x ∂(mu : Measure Real))
      atTop (nhds (∫ x, Real.exp (a * |x|) ∂(mu : Measure Real))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x : Real => Real.exp (a * |x|))
    · filter_upwards with n
      exact (truncatedExpAbs a n).continuous.aestronglyMeasurable
    · filter_upwards with n
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (truncatedExpAbs_nonneg a n x)]
        exact truncatedExpAbs_le_exp a n x
    · exact hintLimit
    · filter_upwards with x
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop
        (Nat.ceil (Real.exp (a * |x|)) + 1)] with n hn
      have hxn : Real.exp (a * |x|) <= n := by
        have hceil : Nat.ceil (Real.exp (a * |x|)) <= n :=
          (Nat.le_add_right _ 1).trans hn
        calc
          Real.exp (a * |x|) <= Nat.ceil (Real.exp (a * |x|)) :=
            Nat.le_ceil _
          _ <= n := by exact_mod_cast hceil
      change Real.exp (a * |x|) = min (Real.exp (a * |x|)) n
      exact (min_eq_left hxn).symm
  exact le_of_tendsto hconv (Filter.Eventually.of_forall htruncBound)



theorem zero_mem_interior_integrableExpSet_of_integrable_exp_abs
    (mu : Measure Real) (a : Real) (ha : 0 < a)
    (hint : Integrable (fun x : Real => Real.exp (a * |x|)) mu) :
    (0 : Real) ∈ interior (integrableExpSet id mu) := by
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset (Metric.ball_mem_nhds 0 ha) ?_
  intro t ht
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  have hdom : ∀ x : Real,
      Real.exp (t * id x) <= Real.exp (a * |x|) := by
    intro x
    apply Real.exp_le_exp.mpr
    calc
      t * id x <= |t * x| := le_abs_self _
      _ = |t| * |x| := abs_mul t x
      _ <= a * |x| := mul_le_mul_of_nonneg_right ht.le (abs_nonneg x)
  exact hint.mono (by fun_prop)
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hdom x)

private theorem integral_power_sub_clipped_abs_le
    (mu : Measure Real) [IsFiniteMeasure mu]
    (order : Nat) (a C c M : Real)
    (ha : 0 < a) (hM : 0 <= M) (hc : 0 <= c)
    (hint : Integrable (fun x : Real => Real.exp (a * |x|)) mu)
    (hbound : (∫ x, Real.exp (a * |x|) ∂mu) <= C)
    (htail : ∀ t : Real, M <= t ->
      t ^ order <= c * Real.exp (a * t)) :
    |∫ x, x ^ order ∂mu -
        ∫ x, clippedPower order (M ^ order) x ∂mu| <= c * C := by
  have hzero := zero_mem_interior_integrableExpSet_of_integrable_exp_abs
    mu a ha hint
  have hpow : Integrable (fun x : Real => x ^ order) mu :=
    integrable_pow_of_mem_interior_integrableExpSet hzero order
  have hclip : Integrable (clippedPower order (M ^ order)) mu := by
    exact BoundedContinuousFunction.integrable _ _
  have herr : Integrable
      (fun x : Real => |x ^ order - clippedPower order (M ^ order) x|) mu :=
    (hpow.sub hclip).norm
  have hpoint (x : Real) :
      |x ^ order - clippedPower order (M ^ order) x| <=
        c * Real.exp (a * |x|) := by
    by_cases hx : M <= |x|
    · exact (abs_sub_clippedPower_le order (pow_nonneg hM order) x).trans
        (htail |x| hx)
    · have hx' : |x| <= M := le_of_not_ge hx
      have hp : |x ^ order| <= M ^ order := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg x) hx' order
      rw [clippedPower_eq_self order (pow_nonneg hM order) hp,
        sub_self, abs_zero]
      exact mul_nonneg hc (Real.exp_pos _).le
  calc
    |∫ x, x ^ order ∂mu -
        ∫ x, clippedPower order (M ^ order) x ∂mu| =
        |∫ x, x ^ order - clippedPower order (M ^ order) x ∂mu| := by
      rw [integral_sub hpow hclip]
    _ <= ∫ x, |x ^ order - clippedPower order (M ^ order) x| ∂mu :=
      abs_integral_le_integral_abs
    _ <= ∫ x, c * Real.exp (a * |x|) ∂mu := by
      exact integral_mono herr (hint.const_mul c) hpoint
    _ = c * (∫ x, Real.exp (a * |x|) ∂mu) := by
      rw [integral_const_mul]
    _ <= c * C := mul_le_mul_of_nonneg_left hbound hc



theorem integral_pow_tendsto_of_weakLimit_uniform_exp
    (muN : Nat -> ProbabilityMeasure Real) (mu : ProbabilityMeasure Real)
    (hlim : Tendsto muN atTop (nhds mu))
    (a C : Real) (ha : 0 < a)
    (hint : forall n, Integrable (fun x : Real => Real.exp (a * |x|))
      (muN n : Measure Real))
    (hbound : forall n,
      (∫ x, Real.exp (a * |x|) ∂(muN n : Measure Real)) <= C)
    (order : Nat) :
    Tendsto (fun n => ∫ x, x ^ order ∂(muN n : Measure Real))
      atTop (nhds (∫ x, x ^ order ∂(mu : Measure Real))) := by
  have hlimitInt := integrable_exp_abs_of_weakLimit_uniform
    muN mu hlim a C hint hbound
  have hlimitBound := integral_exp_abs_le_of_weakLimit_uniform
    muN mu hlim a C hint hbound
  have hC : 0 <= C := by
    have hnonneg : 0 <=
        ∫ x, Real.exp (a * |x|) ∂(muN 0 : Measure Real) :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    exact hnonneg.trans (hbound 0)
  apply Metric.tendsto_atTop.2
  intro eps heps
  let c : Real := eps / (3 * (C + 1))
  have hden : 0 < 3 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have hc : 0 < c := div_pos heps hden
  have hcC : c * C < eps / 3 := by
    dsimp only [c]
    have hfrac : C / (C + 1) < 1 := by
      exact (div_lt_one (by linarith)).mpr (by linarith)
    calc
      eps / (3 * (C + 1)) * C = eps / 3 * (C / (C + 1)) := by
        field_simp
      _ < eps / 3 * 1 := mul_lt_mul_of_pos_left hfrac (by positivity)
      _ = eps / 3 := mul_one _
  have hev := (isLittleO_pow_exp_pos_mul_atTop order ha).bound hc
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hev
  let M : Real := max M₀ 0
  have hM : 0 <= M := le_max_right _ _
  have htail (t : Real) (ht : M <= t) :
      t ^ order <= c * Real.exp (a * t) := by
    have hraw := hM₀ t ((le_max_left M₀ 0).trans ht)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hM.trans ht) order),
      abs_of_pos (Real.exp_pos _)] using hraw
  let f : BoundedContinuousFunction Real Real := clippedPower order (M ^ order)
  have hclipConv :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hclipConv) (eps / 3) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have htailN := integral_power_sub_clipped_abs_le
    (muN n : Measure Real) order a C c M ha hM hc.le
      (hint n) (hbound n) htail
  have htailLimit := integral_power_sub_clipped_abs_le
    (mu : Measure Real) order a C c M ha hM hc.le
      hlimitInt hlimitBound htail
  have hclip := hN n hn
  rw [Real.dist_eq] at hclip ⊢
  have htri := dist_triangle4
      (∫ x, x ^ order ∂(muN n : Measure Real))
      (∫ x, f x ∂(muN n : Measure Real))
      (∫ x, f x ∂(mu : Measure Real))
      (∫ x, x ^ order ∂(mu : Measure Real))
  rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq] at htri
  have hlast :
      |∫ x, f x ∂(mu : Measure Real) -
        ∫ x, x ^ order ∂(mu : Measure Real)| <= c * C := by
    rw [abs_sub_comm]
    exact htailLimit
  dsimp only [f] at hclip htri hlast
  linarith




theorem weakLimit_eq_of_projection_cumulant_limits_uniform_exp
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    (muN : Nat -> ProbabilityMeasure E)
    (mu nu : ProbabilityMeasure E)
    (hlim : Tendsto muN atTop (nhds mu))
    (variance : E -> Real) (cumulants : Nat -> E -> Nat -> Real)
    (hrecurrence : ∀ t : E,
      HasScalarMomentCumulantRecurrence
        (fun scale order =>
          ∫ x, x ^ order
            ∂((muN scale : Measure E).map
              (InnerProductSpace.toDualMap Real E t)))
        (fun scale order => cumulants scale t order))
    (hcumulants : ∀ (t : E) (order : Nat),
      Tendsto (fun scale => cumulants scale t order) atTop
        (nhds (scalarGaussianCumulant (variance t) order)))
    (a C : E -> Real) (ha : ∀ t, 0 < a t)
    (hint : ∀ (t : E) (scale : Nat), Integrable
      (fun x : Real => Real.exp (a t * |x|))
      ((muN scale : Measure E).map
        (InnerProductSpace.toDualMap Real E t)))
    (hbound : ∀ (t : E) (scale : Nat),
      (∫ x, Real.exp (a t * |x|)
        ∂((muN scale : Measure E).map
          (InnerProductSpace.toDualMap Real E t))) <= C t)
    (hnuExp : ∀ t : E, (0 : Real) ∈ interior
      (integrableExpSet id
        ((nu : Measure E).map (InnerProductSpace.toDualMap Real E t))))
    (hnuWick : ∀ t : E, ScalarWickMoments (variance t)
      (fun order => ∫ x, x ^ order
        ∂((nu : Measure E).map (InnerProductSpace.toDualMap Real E t)))) :
    (mu : Measure E) = (nu : Measure E) := by
  apply probabilityMeasure_eq_of_projectionWickMoments_of_localExp
    (mu : Measure E) (nu : Measure E) variance
  · intro t
    let L := InnerProductSpace.toDualMap Real E t
    let muNt : Nat -> ProbabilityMeasure Real := fun scale =>
      (muN scale).map L.continuous.measurable.aemeasurable
    let muProj : ProbabilityMeasure Real :=
      mu.map L.continuous.measurable.aemeasurable
    have hlimt : Tendsto muNt atTop (nhds muProj) := by
      exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        muN mu hlim L.continuous
    apply zero_mem_interior_integrableExpSet_of_weakLimit_uniform
      muNt muProj hlimt (a t) (C t) (ha t)
    · intro scale
      simpa only [muNt, ProbabilityMeasure.map,
        ProbabilityMeasure.coe_mk] using hint t scale
    · intro scale
      simpa only [muNt, ProbabilityMeasure.map,
        ProbabilityMeasure.coe_mk] using hbound t scale
  · exact hnuExp
  · intro t
    let L := InnerProductSpace.toDualMap Real E t
    let muNt : Nat -> ProbabilityMeasure Real := fun scale =>
      (muN scale).map L.continuous.measurable.aemeasurable
    let muProj : ProbabilityMeasure Real :=
      mu.map L.continuous.measurable.aemeasurable
    have hlimt : Tendsto muNt atTop (nhds muProj) := by
      exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        muN mu hlim L.continuous
    have hmoments (order : Nat) : Tendsto
        (fun scale => ∫ x, x ^ order ∂(muNt scale : Measure Real))
        atTop (nhds (∫ x, x ^ order ∂(muProj : Measure Real))) := by
      apply integral_pow_tendsto_of_weakLimit_uniform_exp
        muNt muProj hlimt (a t) (C t) (ha t)
      · intro scale
        simpa only [muNt, ProbabilityMeasure.map,
          ProbabilityMeasure.coe_mk] using hint t scale
      · intro scale
        simpa only [muNt, ProbabilityMeasure.map,
          ProbabilityMeasure.coe_mk] using hbound t scale
    have hwick := scalarWickMoments_of_cumulant_limits
      (fun scale order => ∫ x, x ^ order ∂(muNt scale : Measure Real))
      (fun scale order => cumulants scale t order)
      (fun order => ∫ x, x ^ order ∂(muProj : Measure Real))
      (variance t) (by
        simpa only [muNt, ProbabilityMeasure.map,
          ProbabilityMeasure.coe_mk] using hrecurrence t)
      hmoments (hcumulants t)
    simpa only [muProj, ProbabilityMeasure.map,
      ProbabilityMeasure.coe_mk] using hwick
  · exact hnuWick

end StatMech.FrontierA
