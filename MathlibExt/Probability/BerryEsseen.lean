/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ProbabilityTheory ENNReal NNReal

namespace MathlibExt.Probability.BerryEsseenWanted

/-!
# Berry–Esseen theorem

The uniform CLT rate for normalized i.i.d. sums.
-/

private noncomputable def stdNormalCDF (w : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Iic w)

private lemma stdNormalCDF_nonneg (w : ℝ) : 0 ≤ stdNormalCDF w := measureReal_nonneg

private lemma stdNormalCDF_le_one (w : ℝ) : stdNormalCDF w ≤ 1 := by
  unfold stdNormalCDF
  have huniv : (gaussianReal 0 (1 : ℝ≥0)).real Set.univ = 1 := by
    rw [Measure.real, measure_univ, ENNReal.toReal_one]
  rw [← huniv]
  exact measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)

private lemma stdNormalCDF_sub_eq_integral {a b : ℝ} (h : a ≤ b) :
    stdNormalCDF b - stdNormalCDF a = ∫ x in a..b, gaussianPDFReal 0 1 x := by
  have hdisj : Disjoint (Set.Iic a) (Set.Ioc a b) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_Iic] at hx1
    rw [Set.mem_Ioc] at hx2
    exact absurd (lt_of_le_of_lt hx1 hx2.1) (lt_irrefl _)
  have h2 : stdNormalCDF b
      = stdNormalCDF a + (gaussianReal 0 (1 : ℝ≥0)).real (Set.Ioc a b) := by
    unfold stdNormalCDF
    rw [← Set.Iic_union_Ioc_eq_Iic h]
    exact measureReal_union hdisj measurableSet_Ioc (measure_ne_top _ _) (measure_ne_top _ _)
  have h3 : (gaussianReal 0 (1 : ℝ≥0)).real (Set.Ioc a b)
      = ∫ x in a..b, gaussianPDFReal 0 1 x := by
    rw [intervalIntegral.integral_of_le h, Measure.real,
      gaussianReal_apply_eq_integral 0 one_ne_zero]
    rw [ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Ioc
      (fun x _ => le_of_lt (gaussianPDFReal_pos 0 1 x one_ne_zero))
  rw [h2, add_sub_cancel_left]
  exact h3.symm ▸ rfl

private lemma continuous_gaussianPDFReal_std : Continuous (gaussianPDFReal 0 1) := by
  have h := gaussianPDFReal_def (0 : ℝ) (1 : ℝ≥0)
  rw [h]
  exact continuous_const.mul
    (Real.continuous_exp.comp (((continuous_id.sub continuous_const).pow 2).neg.div_const _))

private lemma stdNormalCDF_eq_add (u : ℝ) :
    stdNormalCDF u = stdNormalCDF 0 + ∫ x in (0 : ℝ)..u, gaussianPDFReal 0 1 x := by
  rcases le_total 0 u with h | h
  · have hsub := stdNormalCDF_sub_eq_integral h (a := 0) (b := u)
    linarith
  · have hsub := stdNormalCDF_sub_eq_integral h (a := u) (b := 0)
    rw [intervalIntegral.integral_symm] at hsub
    linarith

private lemma hasDerivAt_stdNormalCDF (w : ℝ) :
    HasDerivAt stdNormalCDF (gaussianPDFReal 0 1 w) w := by
  have heq : stdNormalCDF
      = fun u => (∫ x in (0 : ℝ)..u, gaussianPDFReal 0 1 x) + stdNormalCDF 0 := by
    funext u
    rw [stdNormalCDF_eq_add u, add_comm]
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (continuous_gaussianPDFReal_std.intervalIntegrable 0 w)
    (continuous_gaussianPDFReal_std.stronglyMeasurable.stronglyMeasurableAtFilter)
    (continuous_gaussianPDFReal_std.continuousAt)).add_const _

private lemma continuous_stdNormalCDF : Continuous stdNormalCDF :=
  continuous_iff_continuousAt.mpr fun w => (hasDerivAt_stdNormalCDF w).continuousAt

private lemma stdNormalCDF_mono : Monotone stdNormalCDF := by
  intro a b h
  unfold stdNormalCDF
  exact measureReal_mono (Set.Iic_subset_Iic.mpr h) (measure_ne_top _ _)

private lemma map_neg_gaussianReal_std :
    Measure.map (fun x : ℝ => -x) (gaussianReal 0 (1 : ℝ≥0)) = gaussianReal 0 1 := by
  rw [gaussianReal_map_neg]
  simp

private lemma neg_preimage_Iic_neg (w : ℝ) :
    (fun x : ℝ => -x) ⁻¹' (Set.Iic (-w)) = Set.Ici w := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici, neg_le_neg_iff]

private lemma gaussianReal_Iio_eq_Iic (w : ℝ) :
    (gaussianReal 0 (1 : ℝ≥0)).real (Set.Iio w)
      = (gaussianReal 0 1).real (Set.Iic w) := by
  have h1 : Set.Iic w = Set.Iio w ∪ {w} := by
    ext x
    simp only [Set.mem_Iic, Set.mem_Iio, Set.mem_union, Set.mem_singleton_iff,
      le_iff_lt_or_eq]
  have hnull : (gaussianReal 0 (1 : ℝ≥0)).real {w} = 0 := by
    have h0 : (gaussianReal 0 (1 : ℝ≥0)) {w} = 0 :=
      @NullSingletonClass.measure_singleton _ _ _
        (nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) one_ne_zero) w
    unfold Measure.real
    rw [h0]
    exact ENNReal.toReal_zero
  have hdisj : Disjoint (Set.Iio w) ({w} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_Iio] at hx1
    rw [Set.mem_singleton_iff] at hx2
    rw [hx2] at hx1
    exact absurd hx1 (lt_irrefl _)
  have h2 : (gaussianReal 0 (1 : ℝ≥0)).real (Set.Iio w ∪ {w})
      = (gaussianReal 0 1).real (Set.Iio w) := by
    rw [measureReal_union hdisj (measurableSet_singleton w)
      (measure_ne_top _ _) (measure_ne_top _ _), hnull, add_zero]
  rw [← h1] at h2
  exact h2.symm

private lemma stdNormalCDF_neg (w : ℝ) : stdNormalCDF (-w) = 1 - stdNormalCDF w := by
  unfold stdNormalCDF
  have h1 : (gaussianReal 0 (1 : ℝ≥0)).real (Set.Iic (-w))
      = (gaussianReal 0 1).real (Set.Ici w) := by
    conv_lhs => rw [← map_neg_gaussianReal_std]
    rw [map_measureReal_apply measurable_neg measurableSet_Iic, neg_preimage_Iic_neg]
  have h2 : (gaussianReal 0 (1 : ℝ≥0)).real (Set.Ici w)
      = 1 - (gaussianReal 0 1).real (Set.Iio w) := by
    rw [← Set.compl_Iio]
    exact probReal_compl_eq_one_sub measurableSet_Iio
  rw [h1, h2, gaussianReal_Iio_eq_Iic]

private lemma one_sub_stdNormalCDF_eq_integral_Ioi (w : ℝ) :
    1 - stdNormalCDF w = ∫ t in Set.Ioi w, gaussianPDFReal 0 1 t := by
  unfold stdNormalCDF
  have h1 : (gaussianReal 0 (1 : ℝ≥0)).real (Set.Ioi w)
      = 1 - (gaussianReal 0 1).real (Set.Iic w) := by
    rw [← Set.compl_Iic]
    exact probReal_compl_eq_one_sub measurableSet_Iic
  rw [← h1, Measure.real, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Ioi
    (fun x _ => le_of_lt (gaussianPDFReal_pos 0 1 x one_ne_zero))

private lemma hasDerivAt_exponent_std (t : ℝ) :
    HasDerivAt (fun u : ℝ => -(u - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
      (-(t - 0) / ((1 : ℝ≥0) : ℝ)) t := by
  have h1 : HasDerivAt (fun u : ℝ => u - 0) 1 t := (hasDerivAt_id t).sub_const 0
  have h2 := h1.pow 2
  have h3 := h2.neg.div_const (2 * ((1 : ℝ≥0) : ℝ))
  refine h3.congr_deriv ?_
  simp only [NNReal.coe_one, mul_one]
  ring

private lemma hasDerivAt_neg_gaussianPDFReal_std (t : ℝ) :
    HasDerivAt (fun u => -(gaussianPDFReal 0 1 u)) (t * gaussianPDFReal 0 1 t) t := by
  have hdef := gaussianPDFReal_def (0 : ℝ) (1 : ℝ≥0)
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-(u - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))))
      (Real.exp (-(t - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
        * (-(t - 0) / ((1 : ℝ≥0) : ℝ))) t :=
    (hasDerivAt_exponent_std t).exp
  have hC := (hexp.const_mul ((√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹)).neg
  have hval : -((√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
        * (Real.exp (-(t - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
          * (-(t - 0) / ((1 : ℝ≥0) : ℝ))))
      = t * gaussianPDFReal 0 1 t := by
    rw [hdef]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    ring
  have hfun : (-(fun y : ℝ => (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
        * Real.exp (-(y - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))))
      = fun u => -(gaussianPDFReal 0 1 u) := by
    funext u
    rw [hdef]
    rfl
  rw [hfun] at hC
  exact hC.congr_deriv hval

private lemma tendsto_neg_gaussianPDFReal_std_atTop :
    Filter.Tendsto (fun u => -(gaussianPDFReal 0 1 u)) Filter.atTop (nhds 0) := by
  have hdef := gaussianPDFReal_def (0 : ℝ) (1 : ℝ≥0)
  have htop : Filter.Tendsto (fun u : ℝ => -(u - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
      Filter.atTop Filter.atBot := by
    have hpow : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop (by norm_num)
    have h1 := Filter.tendsto_neg_atTop_atBot.comp
      (hpow.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    refine h1.congr' (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.comp_def, NNReal.coe_one, mul_one]
    ring
  have hexp0 : Filter.Tendsto
      (fun u : ℝ => Real.exp (-(u - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp htop
  have hphi0 : Filter.Tendsto (gaussianPDFReal 0 1) Filter.atTop (nhds 0) := by
    have hC := hexp0.const_mul ((√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹)
    have hfun : (fun x : ℝ => (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
          * Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))))
        = gaussianPDFReal 0 1 := by
      rw [hdef]
    rw [hfun] at hC
    simpa using hC
  have hneg := hphi0.neg
  simpa using hneg

private lemma integrable_mul_gaussianPDFReal_std :
    Integrable (fun t => t * gaussianPDFReal 0 1 t) volume := by
  have hdef := gaussianPDFReal_def (0 : ℝ) (1 : ℝ≥0)
  have hbase := integrable_mul_exp_neg_mul_sq (show (0 : ℝ) < 1 / 2 by norm_num)
  have heq : (fun t => t * gaussianPDFReal 0 1 t)
      = fun t => (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
        * (t * Real.exp (-(1 / 2) * t ^ 2)) := by
    funext t
    have hexp_eq : -(t - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) = -(1 / 2) * t ^ 2 := by
      simp [NNReal.coe_one]
      ring
    simp only [hdef]
    rw [hexp_eq]
    ring
  rw [heq]
  exact hbase.const_mul _

private lemma mul_one_sub_stdNormalCDF_le {w : ℝ} (hw : 0 < w) :
    w * (1 - stdNormalCDF w) ≤ gaussianPDFReal 0 1 w := by
  have hanti : ∫ t in Set.Ioi w, t * gaussianPDFReal 0 1 t
      = gaussianPDFReal 0 1 w := by
    have hderiv : ∀ t ∈ Set.Ioi w, HasDerivAt (fun u => -(gaussianPDFReal 0 1 u))
        (t * gaussianPDFReal 0 1 t) t :=
      fun t _ => hasDerivAt_neg_gaussianPDFReal_std t
    have hcont : ContinuousWithinAt (fun u => -(gaussianPDFReal 0 1 u)) (Set.Ici w) w :=
      (continuous_gaussianPDFReal_std.neg).continuousWithinAt
    have hint : IntegrableOn (fun t => t * gaussianPDFReal 0 1 t) (Set.Ioi w) volume :=
      integrable_mul_gaussianPDFReal_std.integrableOn
    have hlim := tendsto_neg_gaussianPDFReal_std_atTop
    have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
    simpa using h
  have hglob_phi : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi w) volume :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hglob_w : IntegrableOn (fun t => (t / w) * gaussianPDFReal 0 1 t)
      (Set.Ioi w) volume := by
    have heq : (fun t => (t / w) * gaussianPDFReal 0 1 t)
        = fun t => (1 / w) * (t * gaussianPDFReal 0 1 t) := by
      funext t
      ring
    rw [heq]
    exact (integrable_mul_gaussianPDFReal_std.const_mul _).integrableOn
  have hle : ∫ t in Set.Ioi w, gaussianPDFReal 0 1 t
      ≤ ∫ t in Set.Ioi w, (t / w) * gaussianPDFReal 0 1 t := by
    apply setIntegral_mono_on hglob_phi hglob_w measurableSet_Ioi
    intro t ht
    rw [Set.mem_Ioi] at ht
    have h1w : (1 : ℝ) ≤ t / w := by
      rw [le_div_iff₀ hw]
      linarith
    calc gaussianPDFReal 0 1 t = 1 * gaussianPDFReal 0 1 t := (one_mul _).symm
      _ ≤ (t / w) * gaussianPDFReal 0 1 t :=
        mul_le_mul_of_nonneg_right h1w
          (le_of_lt (gaussianPDFReal_pos 0 1 t one_ne_zero))
  have hval : ∫ t in Set.Ioi w, (t / w) * gaussianPDFReal 0 1 t
      = gaussianPDFReal 0 1 w / w := by
    have heq : (fun t => (t / w) * gaussianPDFReal 0 1 t)
        = fun t => (1 / w) * (t * gaussianPDFReal 0 1 t) := by
      funext t
      ring
    rw [heq, integral_const_mul, hanti]
    ring
  rw [one_sub_stdNormalCDF_eq_integral_Ioi]
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hfin : w * (∫ t in Set.Ioi w, gaussianPDFReal 0 1 t)
      ≤ w * (gaussianPDFReal 0 1 w / w) :=
    mul_le_mul_of_nonneg_left (hle.trans (le_of_eq hval)) (le_of_lt hw)
  have hcancel : w * (gaussianPDFReal 0 1 w / w) = gaussianPDFReal 0 1 w := by
    have hring : w * (gaussianPDFReal 0 1 w / w)
        = (w / w) * gaussianPDFReal 0 1 w := by
      ring
    rw [hring, div_self hw0, one_mul]
  rwa [hcancel] at hfin

private noncomputable def steinEg (w : ℝ) : ℝ := Real.sqrt (2 * Real.pi) * Real.exp (w ^ 2 / 2)

private noncomputable def steinSolution (z w : ℝ) : ℝ :=
  (stdNormalCDF (min w z) - stdNormalCDF w * stdNormalCDF z) * steinEg w

private noncomputable def steinSolutionDeriv (z w : ℝ) : ℝ :=
  w * steinSolution z w + (if w ≤ z then (1 : ℝ) else 0) - stdNormalCDF z

private lemma continuous_steinEg : Continuous steinEg := by
  have h2 : Continuous (fun x : ℝ => x ^ 2 / 2) :=
    (continuous_id.pow 2).div_const 2
  have hexp : Continuous (fun x : ℝ => Real.exp (x ^ 2 / 2)) :=
    Real.continuous_exp.comp h2
  have hmul : Continuous
      (fun x : ℝ => Real.sqrt (2 * Real.pi) * Real.exp (x ^ 2 / 2)) :=
    continuous_const.mul hexp
  unfold steinEg
  exact hmul

private lemma continuous_steinSolution (z : ℝ) : Continuous (steinSolution z) := by
  unfold steinSolution
  exact (((continuous_stdNormalCDF.comp (continuous_id.min continuous_const)).sub
    (continuous_stdNormalCDF.mul continuous_const)).mul continuous_steinEg)

private lemma hasDerivAt_steinEg (w : ℝ) : HasDerivAt steinEg (w * steinEg w) w := by
  have h1 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) w w := by
    have h := (hasDerivAt_pow 2 w).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    have e12 : (2 : ℕ) - 1 = 1 := rfl
    simp only [e12, Nat.cast_ofNat, pow_one]
    ring
  have h2 := h1.exp.const_mul (Real.sqrt (2 * Real.pi))
  have hfun : (fun y : ℝ => Real.sqrt (2 * Real.pi) * Real.exp (y ^ 2 / 2)) = steinEg :=
    rfl
  rw [hfun] at h2
  refine h2.congr_deriv ?_
  unfold steinEg
  ring

private lemma gaussianPDFReal_mul_steinEg (w : ℝ) : gaussianPDFReal 0 1 w * steinEg w = 1 := by
  have hdef := gaussianPDFReal_def (0 : ℝ) (1 : ℝ≥0)
  have hsqrt : (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ = (Real.sqrt (2 * Real.pi))⁻¹ := by
    congr 1
    congr 1
    simp [NNReal.coe_one]
  have e : Real.exp (-(w - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) * Real.exp (w ^ 2 / 2)
      = 1 := by
    rw [← Real.exp_add]
    have hz : -(w - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) + w ^ 2 / 2 = 0 := by
      simp [NNReal.coe_one]
      ring
    rw [hz, Real.exp_zero]
  have assoc : (Real.sqrt (2 * Real.pi))⁻¹
        * Real.exp (-(w - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
        * (Real.sqrt (2 * Real.pi) * Real.exp (w ^ 2 / 2))
      = ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi))
        * (Real.exp (-(w - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) * Real.exp (w ^ 2 / 2)) := by
    ring
  unfold steinEg
  rw [hdef, hsqrt, assoc, e, inv_mul_cancel₀]
  · ring
  · exact Real.sqrt_ne_zero'.mpr (by positivity)

private lemma steinSolution_eventuallyEq_left {z w : ℝ} (h : w < z) :
    (steinSolution z) =ᶠ[nhds w]
      fun u => (stdNormalCDF u * (1 - stdNormalCDF z)) * steinEg u := by
  have hmem : Set.Iio z ∈ nhds w := Iio_mem_nhds h
  filter_upwards [hmem] with u hu
  rw [Set.mem_Iio] at hu
  unfold steinSolution
  rw [min_eq_left (le_of_lt hu)]
  ring

private lemma hasDerivAt_steinSolution_of_lt {z w : ℝ} (h : w < z) :
    HasDerivAt (steinSolution z) (steinSolutionDeriv z w) w := by
  have hE1 : HasDerivAt (fun u => stdNormalCDF u * (1 - stdNormalCDF z))
      (gaussianPDFReal 0 1 w * (1 - stdNormalCDF z)) w :=
    (hasDerivAt_stdNormalCDF w).mul_const _
  have hF : HasDerivAt (fun u => (stdNormalCDF u * (1 - stdNormalCDF z)) * steinEg u)
      ((gaussianPDFReal 0 1 w * (1 - stdNormalCDF z)) * steinEg w
        + (stdNormalCDF w * (1 - stdNormalCDF z)) * (w * steinEg w)) w :=
    hE1.mul (hasDerivAt_steinEg w)
  have hval : (gaussianPDFReal 0 1 w * (1 - stdNormalCDF z)) * steinEg w
        + (stdNormalCDF w * (1 - stdNormalCDF z)) * (w * steinEg w)
      = steinSolutionDeriv z w := by
    have e1 : (gaussianPDFReal 0 1 w * (1 - stdNormalCDF z)) * steinEg w
        = (1 - stdNormalCDF z) * (gaussianPDFReal 0 1 w * steinEg w) := by
      ring
    have hmin : min w z = w := min_eq_left (le_of_lt h)
    have hif : (if w ≤ z then (1 : ℝ) else 0) = 1 := by
      simp [le_of_lt h]
    unfold steinSolutionDeriv steinSolution
    rw [hmin, hif, e1, gaussianPDFReal_mul_steinEg]
    ring
  rw [hval] at hF
  exact hF.congr_of_eventuallyEq (steinSolution_eventuallyEq_left h)

private lemma steinSolution_eventuallyEq_right {z w : ℝ} (h : z < w) :
    (steinSolution z) =ᶠ[nhds w]
      fun u => (stdNormalCDF z * (1 - stdNormalCDF u)) * steinEg u := by
  have hmem : Set.Ioi z ∈ nhds w := Ioi_mem_nhds h
  filter_upwards [hmem] with u hu
  rw [Set.mem_Ioi] at hu
  unfold steinSolution
  rw [min_eq_right (le_of_lt hu)]
  ring

private lemma hasDerivAt_steinSolution_of_gt {z w : ℝ} (h : z < w) :
    HasDerivAt (steinSolution z) (steinSolutionDeriv z w) w := by
  have hsub : HasDerivAt (fun u : ℝ => (1 : ℝ) - stdNormalCDF u)
      (-(gaussianPDFReal 0 1 w)) w :=
    (hasDerivAt_stdNormalCDF w).const_sub 1
  have hE1 : HasDerivAt (fun u => stdNormalCDF z * (1 - stdNormalCDF u))
      (stdNormalCDF z * (-(gaussianPDFReal 0 1 w))) w :=
    hsub.const_mul _
  have hF : HasDerivAt (fun u => (stdNormalCDF z * (1 - stdNormalCDF u)) * steinEg u)
      ((stdNormalCDF z * (-(gaussianPDFReal 0 1 w))) * steinEg w
        + (stdNormalCDF z * (1 - stdNormalCDF w)) * (w * steinEg w)) w :=
    hE1.mul (hasDerivAt_steinEg w)
  have hval : (stdNormalCDF z * (-(gaussianPDFReal 0 1 w))) * steinEg w
        + (stdNormalCDF z * (1 - stdNormalCDF w)) * (w * steinEg w)
      = steinSolutionDeriv z w := by
    have e1 : (stdNormalCDF z * (-(gaussianPDFReal 0 1 w))) * steinEg w
        = -(stdNormalCDF z * (gaussianPDFReal 0 1 w * steinEg w)) := by
      ring
    have hmin : min w z = z := min_eq_right (le_of_lt h)
    have hif : (if w ≤ z then (1 : ℝ) else 0) = 0 := by
      simp [not_le_of_gt h]
    unfold steinSolutionDeriv steinSolution
    rw [hmin, hif, e1, gaussianPDFReal_mul_steinEg]
    ring
  rw [hval] at hF
  exact hF.congr_of_eventuallyEq (steinSolution_eventuallyEq_right h)

private lemma hasDerivAt_steinSolution_of_ne {z w : ℝ} (h : w ≠ z) :
    HasDerivAt (steinSolution z) (steinSolutionDeriv z w) w := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact hasDerivAt_steinSolution_of_lt hlt
  · exact hasDerivAt_steinSolution_of_gt hgt

private lemma steinSolutionDeriv_sub (z w : ℝ) :
    steinSolutionDeriv z w - w * steinSolution z w
      = (if w ≤ z then (1 : ℝ) else 0) - stdNormalCDF z := by
  unfold steinSolutionDeriv
  ring

private lemma gaussianPDFReal_std_neg (w : ℝ) :
    gaussianPDFReal 0 1 (-w) = gaussianPDFReal 0 1 w := by
  have hdef := gaussianPDFReal_def (0 : ℝ) (1 : ℝ≥0)
  have e : -(-w - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))
      = -(w - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) := by
    simp only [NNReal.coe_one, mul_one, sub_zero, neg_sq]
  simp only [hdef, e]

private lemma neg_mul_stdNormalCDF_le {w : ℝ} (hw : w < 0) :
    (-w) * stdNormalCDF w ≤ gaussianPDFReal 0 1 w := by
  have h := mul_one_sub_stdNormalCDF_le (show (0 : ℝ) < -w by linarith)
  rw [stdNormalCDF_neg, gaussianPDFReal_std_neg] at h
  simpa using h

private lemma steinEg_nonneg (w : ℝ) : 0 ≤ steinEg w := by
  unfold steinEg
  exact mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (Real.exp_pos _))

private lemma steinEg_pos (w : ℝ) : 0 < steinEg w := by
  unfold steinEg
  exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _)

private lemma steinSolution_eq_left {z w : ℝ} (h : w ≤ z) :
    steinSolution z w = stdNormalCDF w * (1 - stdNormalCDF z) * steinEg w := by
  unfold steinSolution
  rw [min_eq_left h]
  ring

private lemma steinSolution_eq_right {z w : ℝ} (h : z ≤ w) :
    steinSolution z w = stdNormalCDF z * (1 - stdNormalCDF w) * steinEg w := by
  unfold steinSolution
  rw [min_eq_right h]
  ring

private lemma steinSolution_nonneg (z w : ℝ) : 0 ≤ steinSolution z w := by
  rcases le_total w z with h | h
  · rw [steinSolution_eq_left h]
    exact mul_nonneg
      (mul_nonneg (stdNormalCDF_nonneg w) (by linarith [stdNormalCDF_le_one z]))
      (steinEg_nonneg w)
  · rw [steinSolution_eq_right h]
    exact mul_nonneg
      (mul_nonneg (stdNormalCDF_nonneg z) (by linarith [stdNormalCDF_le_one w]))
      (steinEg_nonneg w)

private lemma steinSolution_le_mid (z w : ℝ) :
    steinSolution z w
      ≤ stdNormalCDF w * (1 - stdNormalCDF w) * steinEg w := by
  have hEg := steinEg_nonneg w
  rcases le_total w z with h | h
  · rw [steinSolution_eq_left h]
    have hmono : stdNormalCDF w ≤ stdNormalCDF z := stdNormalCDF_mono h
    calc stdNormalCDF w * (1 - stdNormalCDF z) * steinEg w
        = stdNormalCDF w * ((1 - stdNormalCDF z) * steinEg w) := by ring
      _ ≤ stdNormalCDF w * ((1 - stdNormalCDF w) * steinEg w) := by
          apply mul_le_mul_of_nonneg_left _ (stdNormalCDF_nonneg w)
          apply mul_le_mul_of_nonneg_right _ hEg
          linarith
      _ = stdNormalCDF w * (1 - stdNormalCDF w) * steinEg w := by ring
  · rw [steinSolution_eq_right h]
    have hmono : stdNormalCDF z ≤ stdNormalCDF w := stdNormalCDF_mono h
    have h2 : 0 ≤ 1 - stdNormalCDF w := by linarith [stdNormalCDF_le_one w]
    calc stdNormalCDF z * (1 - stdNormalCDF w) * steinEg w
        = (1 - stdNormalCDF w) * (stdNormalCDF z * steinEg w) := by ring
      _ ≤ (1 - stdNormalCDF w) * (stdNormalCDF w * steinEg w) := by
          apply mul_le_mul_of_nonneg_left _ h2
          apply mul_le_mul_of_nonneg_right hmono hEg
      _ = stdNormalCDF w * (1 - stdNormalCDF w) * steinEg w := by ring

private lemma wRminus_ge {w : ℝ} (hw : w ≤ 0) :
    -1 ≤ w * (stdNormalCDF w * steinEg w) := by
  rcases eq_or_lt_of_le hw with rfl | hlt
  · rw [zero_mul]
    norm_num
  · have h := neg_mul_stdNormalCDF_le hlt
    have e : (-w) * stdNormalCDF w * steinEg w
        = -(w * (stdNormalCDF w * steinEg w)) := by
      ring
    have h2 : (-w) * stdNormalCDF w * steinEg w ≤ 1 := by
      have e2 : (-w) * stdNormalCDF w * steinEg w
          = ((-w) * stdNormalCDF w) * steinEg w := by
        ring
      rw [e2]
      calc ((-w) * stdNormalCDF w) * steinEg w
          ≤ gaussianPDFReal 0 1 w * steinEg w :=
            mul_le_mul_of_nonneg_right h (le_of_lt (steinEg_pos w))
        _ = 1 := gaussianPDFReal_mul_steinEg w
    linarith [h2, e]

private lemma wRplus_le {w : ℝ} (hw : 0 ≤ w) :
    w * ((1 - stdNormalCDF w) * steinEg w) ≤ 1 := by
  rcases eq_or_lt_of_le hw with rfl | hgt
  · rw [zero_mul]
    norm_num
  · have h := mul_one_sub_stdNormalCDF_le hgt
    have e : w * ((1 - stdNormalCDF w) * steinEg w)
        = (w * (1 - stdNormalCDF w)) * steinEg w := by
      ring
    rw [e]
    calc (w * (1 - stdNormalCDF w)) * steinEg w
        ≤ gaussianPDFReal 0 1 w * steinEg w :=
          mul_le_mul_of_nonneg_right h (le_of_lt (steinEg_pos w))
      _ = 1 := gaussianPDFReal_mul_steinEg w

private lemma mid_mul_steinEg_le_two (w : ℝ) :
    stdNormalCDF w * (1 - stdNormalCDF w) * steinEg w ≤ 2 := by
  rcases le_total 1 w with hw | hw
  · have hpos : (0 : ℝ) < w := by linarith
    have h1 : 1 - stdNormalCDF w ≤ gaussianPDFReal 0 1 w / w := by
      rw [le_div_iff₀ hpos]
      have h := mul_one_sub_stdNormalCDF_le hpos
      linarith [h]
    calc stdNormalCDF w * (1 - stdNormalCDF w) * steinEg w
        = stdNormalCDF w * ((1 - stdNormalCDF w) * steinEg w) := by ring
      _ ≤ 1 * ((gaussianPDFReal 0 1 w / w) * steinEg w) := by
          exact mul_le_mul (stdNormalCDF_le_one w)
            (mul_le_mul_of_nonneg_right h1 (steinEg_nonneg w))
            (mul_nonneg (by linarith [stdNormalCDF_le_one w]) (steinEg_nonneg w))
            (by norm_num)
      _ = 1 * (gaussianPDFReal 0 1 w * steinEg w / w) := by
          rw [div_mul_eq_mul_div]
      _ = 1 * (1 / w) := by
          rw [gaussianPDFReal_mul_steinEg]
      _ ≤ 1 := by
          rw [one_mul, div_le_one hpos]
          exact hw
      _ ≤ 2 := by norm_num
  · rcases le_total w (-1) with hw2 | hw2
    · have hneg : w < 0 := by linarith
      have h1 : stdNormalCDF w ≤ gaussianPDFReal 0 1 w / (-w) := by
        rw [le_div_iff₀ (show (0 : ℝ) < -w by linarith)]
        have h := neg_mul_stdNormalCDF_le hneg
        linarith [h]
      calc stdNormalCDF w * (1 - stdNormalCDF w) * steinEg w
          = (1 - stdNormalCDF w) * (stdNormalCDF w * steinEg w) := by ring
        _ ≤ 1 * ((gaussianPDFReal 0 1 w / (-w)) * steinEg w) := by
            exact mul_le_mul (by linarith [stdNormalCDF_nonneg w])
              (mul_le_mul_of_nonneg_right h1 (steinEg_nonneg w))
              (mul_nonneg (stdNormalCDF_nonneg w) (steinEg_nonneg w))
              (by norm_num)
        _ = 1 * (gaussianPDFReal 0 1 w * steinEg w / (-w)) := by
            rw [div_mul_eq_mul_div]
        _ = 1 * (1 / (-w)) := by
            rw [gaussianPDFReal_mul_steinEg]
        _ ≤ 1 := by
            rw [one_mul, div_le_one (show (0 : ℝ) < -w by linarith)]
            linarith [hw2]
        _ ≤ 2 := by norm_num
    · have hPhi : stdNormalCDF w * (1 - stdNormalCDF w) ≤ 1 / 4 := by
        nlinarith [sq_nonneg (stdNormalCDF w - 1 / 2)]
      have hw2sq : w ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - w by linarith)
          (show (0 : ℝ) ≤ 1 + w by linarith)]
      have hEg : steinEg w ≤ Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ) := by
        unfold steinEg
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply Real.exp_le_exp.mpr
        linarith [hw2sq]
      have hsqrt8 : Real.sqrt (2 * Real.pi) ≤ 3 := by
        have hle : 2 * Real.pi ≤ 9 := by
          have hpi4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
          linarith [Real.pi_pos]
        calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt hle
          _ = 3 := by
              rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hexp2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
        have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 ≤ 2 ^ 2 := by
          have hadd : (1 / 2 : ℝ) + 1 / 2 = 1 := by ring
          have hbase : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) ≤ 2 * 2 := by
            rw [← Real.exp_add, hadd]
            have h := Real.exp_one_lt_d9
            norm_num at h ⊢
            linarith
          nlinarith [hbase]
        have h := abs_le_of_sq_le_sq hsq (by norm_num)
        rwa [abs_of_nonneg (le_of_lt (Real.exp_pos _))] at h
      have hEg6 : steinEg w ≤ 6 := by
        have hmul := mul_le_mul hsqrt8 hexp2 (le_of_lt (Real.exp_pos _)) (by norm_num)
        linarith [hEg, hmul]
      calc stdNormalCDF w * (1 - stdNormalCDF w) * steinEg w
          ≤ (1 / 4) * 6 := mul_le_mul hPhi hEg6 (steinEg_nonneg w) (by norm_num)
        _ ≤ 2 := by norm_num

private lemma steinSolution_le_two (z w : ℝ) : steinSolution z w ≤ 2 :=
  le_trans (steinSolution_le_mid z w) (mid_mul_steinEg_le_two w)

private lemma abs_stdNormalCDF_le_one (z : ℝ) : |stdNormalCDF z| ≤ 1 := by
  rw [abs_of_nonneg (stdNormalCDF_nonneg z)]
  exact stdNormalCDF_le_one z

private lemma neg_w_Rminus_le_one {w : ℝ} (hw : w ≤ 0) :
    (-w) * (stdNormalCDF w * steinEg w) ≤ 1 := by
  rcases eq_or_lt_of_le hw with rfl | hlt
  · simp
  · have h := neg_mul_stdNormalCDF_le hlt
    have e : (-w) * (stdNormalCDF w * steinEg w)
        = ((-w) * stdNormalCDF w) * steinEg w := by
      ring
    rw [e]
    calc ((-w) * stdNormalCDF w) * steinEg w
        ≤ gaussianPDFReal 0 1 w * steinEg w :=
          mul_le_mul_of_nonneg_right h (le_of_lt (steinEg_pos w))
      _ = 1 := gaussianPDFReal_mul_steinEg w

private lemma steinDeriv_eq_left {z w : ℝ} (hle : w ≤ z) :
    steinSolutionDeriv z w
      = (1 - stdNormalCDF z) * (1 + w * (stdNormalCDF w * steinEg w)) := by
  have hf := steinSolution_eq_left hle
  have hif : (if w ≤ z then (1 : ℝ) else 0) = 1 := by simp [hle]
  unfold steinSolutionDeriv
  rw [hf, hif]
  ring

private lemma steinDeriv_eq_right {z w : ℝ} (hlt : z < w) :
    steinSolutionDeriv z w
      = stdNormalCDF z * (w * ((1 - stdNormalCDF w) * steinEg w) - 1) := by
  have hf := steinSolution_eq_right (le_of_lt hlt)
  have hif : (if w ≤ z then (1 : ℝ) else 0) = 0 := by simp [not_le_of_gt hlt]
  unfold steinSolutionDeriv
  rw [hf, hif]
  ring

private lemma abs_steinDeriv_caseA {z w : ℝ} (hle : w ≤ z) (hw0 : w ≤ 0) :
    |steinSolutionDeriv z w| ≤ 1 := by
  rw [steinDeriv_eq_left hle]
  have hK : 0 ≤ 1 - stdNormalCDF z := by linarith [stdNormalCDF_le_one z]
  have hK1 : 1 - stdNormalCDF z ≤ 1 := by linarith [stdNormalCDF_nonneg z]
  have hX : -1 ≤ w * (stdNormalCDF w * steinEg w) := wRminus_ge hw0
  have hX0 : w * (stdNormalCDF w * steinEg w) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hw0
      (mul_nonneg (stdNormalCDF_nonneg w) (steinEg_nonneg w))
  have h1 : 0 ≤ 1 + w * (stdNormalCDF w * steinEg w) := by linarith
  have h2 : 1 + w * (stdNormalCDF w * steinEg w) ≤ 1 := by linarith
  have hlo : 0 ≤ (1 - stdNormalCDF z) * (1 + w * (stdNormalCDF w * steinEg w)) :=
    mul_nonneg hK h1
  have hhi : (1 - stdNormalCDF z) * (1 + w * (stdNormalCDF w * steinEg w)) ≤ 1 := by
    calc (1 - stdNormalCDF z) * (1 + w * (stdNormalCDF w * steinEg w))
        ≤ 1 * 1 := mul_le_mul hK1 h2 h1 (by norm_num)
      _ = 1 := mul_one 1
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

private lemma abs_steinDeriv_caseB {z w : ℝ} (hle : w ≤ z) (hw0 : 0 ≤ w) :
    |steinSolutionDeriv z w| ≤ 1 := by
  rw [steinDeriv_eq_left hle]
  have hK : 0 ≤ 1 - stdNormalCDF z := by linarith [stdNormalCDF_le_one z]
  have hKw : 1 - stdNormalCDF z ≤ 1 - stdNormalCDF w := by
    linarith [stdNormalCDF_mono hle]
  have hR : w * ((1 - stdNormalCDF w) * steinEg w) ≤ 1 := wRplus_le hw0
  have hblo : 0 ≤ (1 - stdNormalCDF z) * (1 + w * (stdNormalCDF w * steinEg w)) :=
    mul_nonneg hK (by
      have hXnn : 0 ≤ w * (stdNormalCDF w * steinEg w) :=
        mul_nonneg hw0
          (mul_nonneg (stdNormalCDF_nonneg w) (steinEg_nonneg w))
      linarith)
  have hbhi : (1 - stdNormalCDF z) * (1 + w * (stdNormalCDF w * steinEg w)) ≤ 1 := by
    have step1 : (1 - stdNormalCDF z) * (1 + w * (stdNormalCDF w * steinEg w))
        ≤ (1 - stdNormalCDF w) * (1 + w * (stdNormalCDF w * steinEg w)) := by
      have hXnn : 0 ≤ w * (stdNormalCDF w * steinEg w) :=
        mul_nonneg hw0
          (mul_nonneg (stdNormalCDF_nonneg w) (steinEg_nonneg w))
      exact mul_le_mul_of_nonneg_right hKw (by linarith)
    have step3 : stdNormalCDF w * (w * ((1 - stdNormalCDF w) * steinEg w))
        ≤ stdNormalCDF w * 1 :=
      mul_le_mul_of_nonneg_left hR (stdNormalCDF_nonneg w)
    calc (1 - stdNormalCDF z) * (1 + w * (stdNormalCDF w * steinEg w))
        ≤ (1 - stdNormalCDF w) * (1 + w * (stdNormalCDF w * steinEg w)) := step1
      _ = (1 - stdNormalCDF w)
          + stdNormalCDF w * (w * ((1 - stdNormalCDF w) * steinEg w)) := by
          ring
      _ ≤ (1 - stdNormalCDF w) + stdNormalCDF w * 1 :=
          add_le_add (le_refl _) step3
      _ = 1 := by ring
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

private lemma abs_steinDeriv_caseC {z w : ℝ} (hlt : z < w) (hw0 : 0 ≤ w) :
    |steinSolutionDeriv z w| ≤ 1 := by
  rw [steinDeriv_eq_right hlt]
  have hRnn : 0 ≤ w * ((1 - stdNormalCDF w) * steinEg w) :=
    mul_nonneg hw0
      (mul_nonneg (by linarith [stdNormalCDF_le_one w]) (steinEg_nonneg w))
  have hR : w * ((1 - stdNormalCDF w) * steinEg w) ≤ 1 := wRplus_le hw0
  have hYlo : (-1 : ℝ) ≤ w * ((1 - stdNormalCDF w) * steinEg w) - 1 := by linarith
  have hYhi : w * ((1 - stdNormalCDF w) * steinEg w) - 1 ≤ 0 := by linarith
  have hPnn : 0 ≤ stdNormalCDF z := stdNormalCDF_nonneg z
  have h1 := mul_le_mul_of_nonneg_left hYlo hPnn
  have h2 : (-1 : ℝ) ≤ stdNormalCDF z * (-1) := by
    have h3 : (-1 : ℝ) ≤ -stdNormalCDF z := neg_le_neg (stdNormalCDF_le_one z)
    linarith [h3]
  have hlo : (-1 : ℝ)
      ≤ stdNormalCDF z * (w * ((1 - stdNormalCDF w) * steinEg w) - 1) := by
    linarith [h1, h2]
  have hhi : stdNormalCDF z * (w * ((1 - stdNormalCDF w) * steinEg w) - 1) ≤ 1 := by
    have h3 := mul_le_mul_of_nonneg_left hYhi hPnn
    have h4 : stdNormalCDF z * 0 = 0 := mul_zero _
    linarith [h3, h4]
  rw [abs_le]
  exact ⟨hlo, hhi⟩

private lemma abs_steinDeriv_caseD {z w : ℝ} (hlt : z < w) (hw0 : w ≤ 0) :
    |steinSolutionDeriv z w| ≤ 1 := by
  rcases eq_or_lt_of_le hw0 with rfl | hneg
  · rw [steinDeriv_eq_right hlt]
    have e0 : stdNormalCDF z
          * ((0 : ℝ) * ((1 - stdNormalCDF 0) * steinEg 0) - 1)
        = -stdNormalCDF z := by
      ring
    rw [e0, abs_neg]
    exact abs_stdNormalCDF_le_one z
  · rw [steinDeriv_eq_right hlt]
    have hR0 : w * ((1 - stdNormalCDF w) * steinEg w) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hw0
        (mul_nonneg (by linarith [stdNormalCDF_le_one w]) (steinEg_nonneg w))
    have hhi : stdNormalCDF z * (w * ((1 - stdNormalCDF w) * steinEg w) - 1)
        ≤ 1 := by
      have h3 : stdNormalCDF z * (w * ((1 - stdNormalCDF w) * steinEg w) - 1)
          ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (stdNormalCDF_nonneg z) (by linarith)
      linarith [h3]
    have hlo : (-1 : ℝ)
        ≤ stdNormalCDF z * (w * ((1 - stdNormalCDF w) * steinEg w) - 1) := by
      have hzw : stdNormalCDF z ≤ stdNormalCDF w :=
        stdNormalCDF_mono (le_of_lt hlt)
      have hSnn : (0 : ℝ)
          ≤ 1 + (-w) * ((1 - stdNormalCDF w) * steinEg w) :=
        add_nonneg (by norm_num)
          (mul_nonneg (by linarith)
            (mul_nonneg (by linarith [stdNormalCDF_le_one w]) (steinEg_nonneg w)))
      have e : stdNormalCDF z * (w * ((1 - stdNormalCDF w) * steinEg w) - 1)
          = -(stdNormalCDF z
            * (1 + (-w) * ((1 - stdNormalCDF w) * steinEg w))) := by
        ring
      have hge : -(stdNormalCDF w
            * (1 + (-w) * ((1 - stdNormalCDF w) * steinEg w)))
          ≤ -(stdNormalCDF z
            * (1 + (-w) * ((1 - stdNormalCDF w) * steinEg w))) :=
        neg_le_neg (mul_le_mul_of_nonneg_right hzw hSnn)
      have e2 : -(stdNormalCDF w
            * (1 + (-w) * ((1 - stdNormalCDF w) * steinEg w)))
          = -stdNormalCDF w
            - (1 - stdNormalCDF w) * ((-w) * (stdNormalCDF w * steinEg w)) := by
        ring
      have hR1 : (-w) * (stdNormalCDF w * steinEg w) ≤ 1 :=
        neg_w_Rminus_le_one (le_of_lt hneg)
      have hfin : (-1 : ℝ) ≤ -stdNormalCDF w
          - (1 - stdNormalCDF w) * ((-w) * (stdNormalCDF w * steinEg w)) := by
        have hT : (1 - stdNormalCDF w) * ((-w) * (stdNormalCDF w * steinEg w))
            ≤ (1 - stdNormalCDF w) * 1 :=
          mul_le_mul_of_nonneg_left hR1 (by linarith [stdNormalCDF_le_one w])
        linarith [hT]
      linarith [e, hge, e2, hfin]
    rw [abs_le]
    exact ⟨hlo, hhi⟩

private lemma abs_steinSolutionDeriv_le_one (z w : ℝ) :
    |steinSolutionDeriv z w| ≤ 1 := by
  rcases le_total w z with hle | hle
  · rcases le_total w 0 with hw0 | hw0
    · exact abs_steinDeriv_caseA hle hw0
    · exact abs_steinDeriv_caseB hle hw0
  · rcases eq_or_lt_of_le hle with heq | hlt
    · have hle' : w ≤ z := le_of_eq heq.symm
      rcases le_total w 0 with hw0 | hw0
      · exact abs_steinDeriv_caseA hle' hw0
      · exact abs_steinDeriv_caseB hle' hw0
    · rcases le_total w 0 with hw0 | hw0
      · exact abs_steinDeriv_caseD hlt hw0
      · exact abs_steinDeriv_caseC hlt hw0

private lemma abs_steinSolution_sub_le_of_mem {z y y' : ℝ} (hyy : y < y')
    (hz : z ∉ Set.Ioo y y') :
    |steinSolution z y - steinSolution z y'| ≤ |y - y'| := by
  have hcont : ContinuousOn (steinSolution z) (Set.Icc y y') :=
    (continuous_steinSolution z).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo y y',
      HasDerivAt (steinSolution z) (steinSolutionDeriv z x) x := by
    intro x hx
    apply hasDerivAt_steinSolution_of_ne
    intro hxz
    apply hz
    rw [← hxz]
    exact hx
  obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope _ _ hyy hcont hderiv
  have hgc : |steinSolutionDeriv z c| ≤ 1 := abs_steinSolutionDeriv_le_one z c
  have hpos : (0 : ℝ) < y' - y := by linarith
  have hne : y' - y ≠ 0 := ne_of_gt hpos
  have e : steinSolution z y' - steinSolution z y
      = steinSolutionDeriv z c * (y' - y) := by
    rw [hc, div_mul_cancel₀ _ hne]
  have hsym : |steinSolution z y - steinSolution z y'|
      = |steinSolution z y' - steinSolution z y| := abs_sub_comm _ _
  have hsym2 : |y' - y| = |y - y'| := abs_sub_comm _ _
  rw [hsym, e, abs_mul, hsym2]
  calc |steinSolutionDeriv z c| * |y - y'| ≤ 1 * |y - y'| :=
        mul_le_mul_of_nonneg_right hgc (abs_nonneg _)
    _ = |y - y'| := one_mul _

private lemma abs_steinSolution_sub_le_aux {z y y' : ℝ} (h : y ≤ y') :
    |steinSolution z y - steinSolution z y'| ≤ |y - y'| := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · simp
  · by_cases hzI : z ∈ Set.Ioo y y'
    · obtain ⟨hyz, hzy'⟩ := Set.mem_Ioo.mp hzI
      have h1 : |steinSolution z y - steinSolution z z| ≤ |y - z| := by
        apply abs_steinSolution_sub_le_of_mem hyz
        intro hz2
        rw [Set.mem_Ioo] at hz2
        exact absurd hz2.2 (lt_irrefl _)
      have h2 : |steinSolution z z - steinSolution z y'| ≤ |z - y'| := by
        apply abs_steinSolution_sub_le_of_mem hzy'
        intro hz2
        rw [Set.mem_Ioo] at hz2
        exact absurd hz2.1 (lt_irrefl _)
      have e : |y - y'| = |y - z| + |z - y'| := by
        rw [abs_of_nonpos (by linarith : y - y' ≤ 0),
          abs_of_nonpos (by linarith : y - z ≤ 0),
          abs_of_nonpos (by linarith : z - y' ≤ 0)]
        ring
      calc |steinSolution z y - steinSolution z y'|
          ≤ |steinSolution z y - steinSolution z z|
            + |steinSolution z z - steinSolution z y'| := abs_sub_le _ _ _
        _ ≤ |y - z| + |z - y'| := add_le_add h1 h2
        _ = |y - y'| := e.symm
    · exact abs_steinSolution_sub_le_of_mem hlt hzI

private lemma abs_steinSolution_sub_le (z y y' : ℝ) :
    |steinSolution z y - steinSolution z y'| ≤ |y - y'| := by
  rcases le_total y y' with h | h
  · exact abs_steinSolution_sub_le_aux h
  · have h1 := abs_steinSolution_sub_le_aux (z := z) (y := y') (y' := y) h
    rwa [← abs_sub_comm (steinSolution z y) (steinSolution z y'),
      ← abs_sub_comm y y'] at h1

/-- Indicator window: 1 if `|y - z| ≤ |x|`, else 0. -/
private noncomputable def steinWindow (y x z : ℝ) : ℝ :=
  if |y - z| ≤ |x| then 1 else 0

private lemma steinWindow_nonneg (y x z : ℝ) : 0 ≤ steinWindow y x z := by
  unfold steinWindow
  split <;> norm_num

private lemma steinWindow_le_one (y x z : ℝ) : steinWindow y x z ≤ 1 := by
  unfold steinWindow
  split <;> norm_num

private lemma ind_eq_of_window_lt {y x z : ℝ} (h : ¬ |y - z| ≤ |x|) :
    (if y + x ≤ z then (1 : ℝ) else 0) = (if y ≤ z then 1 else 0) := by
  by_cases h1 : y ≤ z <;> by_cases h2 : y + x ≤ z
  · simp [h1, h2]
  · exfalso; apply h
    have hyz : |y - z| = z - y := by
      rw [abs_of_nonpos (by linarith : y - z ≤ 0)]
      ring
    have hlt : z - y < x := by
      have : y + x > z := not_le.mp h2
      linarith
    rw [hyz]
    exact le_trans (le_of_lt hlt) (le_abs_self x)
  · exfalso; apply h
    have hyz : |y - z| = y - z := abs_of_nonneg (by linarith : 0 ≤ y - z)
    have hle : y - z ≤ -x := by linarith
    rw [hyz]
    calc y - z ≤ -x := hle
      _ ≤ |x| := neg_le_abs x
  · simp [h1, h2]

private lemma abs_ind_sub_le_window (y x z : ℝ) :
    |(if y + x ≤ z then (1 : ℝ) else 0) - (if y ≤ z then 1 else 0)|
      ≤ steinWindow y x z := by
  unfold steinWindow
  by_cases h : |y - z| ≤ |x|
  · simp only [h, ite_true]
    by_cases h1 : y ≤ z <;> by_cases h2 : y + x ≤ z <;> simp [h1, h2]
  · simp only [h, ite_false]
    rw [ind_eq_of_window_lt h]
    simp

/-- N5(a): Lipschitz-type bound on `g` with window term. -/
private lemma steinSolutionDeriv_sub_le (z y x : ℝ) :
    |steinSolutionDeriv z (y + x) - steinSolutionDeriv z y|
      ≤ (|y| + 2) * |x| + steinWindow y x z := by
  have hdecomp : steinSolutionDeriv z (y + x) - steinSolutionDeriv z y
      = y * (steinSolution z (y + x) - steinSolution z y)
        + x * steinSolution z (y + x)
        + ((if y + x ≤ z then (1 : ℝ) else 0) - (if y ≤ z then 1 else 0)) := by
    unfold steinSolutionDeriv
    ring
  have h1 : |y * (steinSolution z (y + x) - steinSolution z y)| ≤ |y| * |x| := by
    calc |y * (steinSolution z (y + x) - steinSolution z y)|
        = |y| * |steinSolution z (y + x) - steinSolution z y| := abs_mul _ _
      _ ≤ |y| * |(y + x) - y| := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact abs_steinSolution_sub_le z _ _
      _ = |y| * |x| := by congr 1; congr 1; ring
  have h2 : |x * steinSolution z (y + x)| ≤ 2 * |x| := by
    calc |x * steinSolution z (y + x)| = |x| * |steinSolution z (y + x)| := abs_mul _ _
      _ ≤ |x| * 2 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_nonneg (steinSolution_nonneg z _)]
          exact steinSolution_le_two z _
      _ = 2 * |x| := by ring
  have h3 := abs_ind_sub_le_window y x z
  rw [hdecomp]
  have e1 : |y * (steinSolution z (y + x) - steinSolution z y)
      + x * steinSolution z (y + x)
      + ((if y + x ≤ z then (1 : ℝ) else 0) - (if y ≤ z then 1 else 0))|
    ≤ |y * (steinSolution z (y + x) - steinSolution z y)
      + x * steinSolution z (y + x)|
      + |(if y + x ≤ z then (1 : ℝ) else 0) - (if y ≤ z then 1 else 0)| :=
    abs_add_le _ _
  have e2 : |y * (steinSolution z (y + x) - steinSolution z y)
      + x * steinSolution z (y + x)|
    ≤ |y * (steinSolution z (y + x) - steinSolution z y)|
      + |x * steinSolution z (y + x)| :=
    abs_add_le _ _
  have e3 : |y * (steinSolution z (y + x) - steinSolution z y)|
      + |x * steinSolution z (y + x)|
      + |(if y + x ≤ z then (1 : ℝ) else 0) - (if y ≤ z then 1 else 0)|
    ≤ |y| * |x| + 2 * |x| + steinWindow y x z :=
    add_le_add (add_le_add h1 h2) h3
  calc |y * (steinSolution z (y + x) - steinSolution z y)
        + x * steinSolution z (y + x)
        + ((if y + x ≤ z then (1 : ℝ) else 0) - (if y ≤ z then 1 else 0))|
      ≤ |y * (steinSolution z (y + x) - steinSolution z y)
        + x * steinSolution z (y + x)|
        + |(if y + x ≤ z then (1 : ℝ) else 0) - (if y ≤ z then 1 else 0)| := e1
    _ ≤ |y * (steinSolution z (y + x) - steinSolution z y)|
        + |x * steinSolution z (y + x)|
        + |(if y + x ≤ z then (1 : ℝ) else 0) - (if y ≤ z then 1 else 0)| :=
      add_le_add e2 (le_refl _)
    _ ≤ |y| * |x| + 2 * |x| + steinWindow y x z := e3
    _ = (|y| + 2) * |x| + steinWindow y x z := by ring

private lemma mem_uIcc_abs_le {t x : ℝ} (h : t ∈ Set.uIcc 0 x) : |t| ≤ |x| := by
  rw [Set.uIcc_eq_union] at h
  rcases h with h | h
  · rw [Set.mem_Icc] at h
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg h.1, abs_of_nonneg hx]
      exact h.2
    · have hx0 : x = 0 := le_antisymm hx (le_trans h.1 h.2)
      have ht0 : t = 0 := le_antisymm (le_trans h.2 hx) h.1
      simp [hx0, ht0]
  · rw [Set.mem_Icc] at h
    rcases le_total 0 x with hx | hx
    · have hx0 : x = 0 := le_antisymm (le_trans h.1 h.2) hx
      have ht0 : t = 0 := le_antisymm h.2 (hx0 ▸ h.1)
      simp [hx0, ht0]
    · rw [abs_of_nonpos (by linarith : t ≤ 0), abs_of_nonpos hx]
      linarith

/-- N5(b): Taylor-type bound on `f`. -/
private lemma steinSolution_taylor_le (z y x : ℝ) :
    |steinSolution z (y + x) - steinSolution z y - x * steinSolutionDeriv z y|
      ≤ (|y| + 2) * x ^ 2 + 2 * |x| * steinWindow y x z := by
  by_cases hwin : |y - z| ≤ |x|
  · have hW : steinWindow y x z = 1 := by
      unfold steinWindow
      simp [hwin]
    have e1 : |steinSolution z (y + x) - steinSolution z y| ≤ |x| := by
      calc |steinSolution z (y + x) - steinSolution z y|
          ≤ |(y + x) - y| := abs_steinSolution_sub_le z _ _
        _ = |x| := by congr 1; ring
    have e2 : |x * steinSolutionDeriv z y| ≤ |x| := by
      calc |x * steinSolutionDeriv z y| = |x| * |steinSolutionDeriv z y| := abs_mul _ _
        _ ≤ |x| * 1 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact abs_steinSolutionDeriv_le_one z y
        _ = |x| := mul_one _
    have e3 : |steinSolution z (y + x) - steinSolution z y
        - x * steinSolutionDeriv z y| ≤ 2 * |x| := by
      have hle : |steinSolution z (y + x) - steinSolution z y
          - x * steinSolutionDeriv z y|
        ≤ |steinSolution z (y + x) - steinSolution z y|
          + |x * steinSolutionDeriv z y| := by
        rw [sub_eq_add_neg]
        have h := abs_add_le (steinSolution z (y + x) - steinSolution z y)
          (-(x * steinSolutionDeriv z y))
        rwa [abs_neg] at h
      linarith [hle, e1, e2]
    have hnn : 0 ≤ (|y| + 2) * x ^ 2 := by
      apply mul_nonneg (by linarith [abs_nonneg y]) (sq_nonneg x)
    rw [hW]
    linarith [e3, hnn]
  · have hW : steinWindow y x z = 0 := by
      unfold steinWindow
      simp [hwin]
    have hne : ∀ t ∈ Set.uIcc (0 : ℝ) x, y + t ≠ z := by
      intro t ht hcon
      apply hwin
      have habs : |y - z| = |t| := by
        have : y - z = -(t) := by linarith
        rw [this, abs_neg]
      rw [habs]
      exact mem_uIcc_abs_le ht
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
        HasDerivWithinAt (fun s => steinSolution z (y + s) - s * steinSolutionDeriv z y)
          (steinSolutionDeriv z (y + t) - steinSolutionDeriv z y)
          (Set.uIcc 0 x) t := by
      intro t ht
      have h1 : HasDerivAt (fun s => steinSolution z (y + s))
          (steinSolutionDeriv z (y + t)) (t) := by
        have hbase := hasDerivAt_steinSolution_of_ne (z := z) (w := y + t)
          (hne t ht)
        have hinner : HasDerivAt (fun s : ℝ => y + s) 1 t := by
          simpa using (hasDerivAt_id t).const_add y
        simpa [Function.comp_def] using hbase.comp t hinner
      have h2 : HasDerivAt (fun s : ℝ => s * steinSolutionDeriv z y)
          (steinSolutionDeriv z y) t := by
        simpa using (hasDerivAt_id t).mul_const (steinSolutionDeriv z y)
      have hsub := h1.sub h2
      have e : steinSolutionDeriv z (y + t) - steinSolutionDeriv z y
          = steinSolutionDeriv z (y + t) - steinSolutionDeriv z y := rfl
      rw [← e]
      have e2 : (fun s => steinSolution z (y + s) - s * steinSolutionDeriv z y)
          = (fun s => steinSolution z (y + s)) - (fun s => s * steinSolutionDeriv z y) := by
        rfl
      rw [e2]
      exact hsub.hasDerivWithinAt
    have hbound : ∀ t ∈ Set.uIcc (0 : ℝ) x,
        ‖steinSolutionDeriv z (y + t) - steinSolutionDeriv z y‖
          ≤ (|y| + 2) * |x| := by
      intro t ht
      have hle := steinSolutionDeriv_sub_le z y t
      have hWt : steinWindow y t z = 0 := by
        unfold steinWindow
        have : ¬ |y - z| ≤ |t| := by
          intro hcon
          apply hwin
          exact le_trans hcon (mem_uIcc_abs_le ht)
        simp [this]
      rw [hWt, add_zero] at hle
      have hle2 : |steinSolutionDeriv z (y + t) - steinSolutionDeriv z y|
          ≤ (|y| + 2) * |x| := by
        calc |steinSolutionDeriv z (y + t) - steinSolutionDeriv z y|
            ≤ (|y| + 2) * |t| := hle
          _ ≤ (|y| + 2) * |x| := by
              apply mul_le_mul_of_nonneg_left _ (by linarith [abs_nonneg y])
              exact mem_uIcc_abs_le ht
      simpa using hle2
    have hconv : Convex ℝ (Set.uIcc (0 : ℝ) x) := convex_uIcc 0 x
    have h0 : (0 : ℝ) ∈ Set.uIcc 0 x := Set.left_mem_uIcc
    have hx : x ∈ Set.uIcc (0 : ℝ) x := Set.right_mem_uIcc
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound hconv h0 hx
    have hval : (fun s => steinSolution z (y + s) - s * steinSolutionDeriv z y) x
        - (fun s => steinSolution z (y + s) - s * steinSolutionDeriv z y) 0
        = steinSolution z (y + x) - steinSolution z y
          - x * steinSolutionDeriv z y := by
      simp
      ring
    rw [hval] at hmvt
    have hnorm : ‖x - 0‖ = |x| := by simp
    rw [hnorm] at hmvt
    have hfin : |steinSolution z (y + x) - steinSolution z y
        - x * steinSolutionDeriv z y|
        ≤ (|y| + 2) * |x| * |x| := by
      simpa using hmvt
    have hsq : (|y| + 2) * |x| * |x| = (|y| + 2) * x ^ 2 := by
      rw [mul_assoc, ← pow_two, sq_abs]
    rw [hsq] at hfin
    rw [hW, mul_zero, add_zero]
    exact hfin

/-- Pointwise bound `x^2 ≤ 1/4 + 2|x|^3`. -/
private lemma sq_le_quarter_add_two_abs_cube (x : ℝ) :
    x ^ 2 ≤ 1 / 4 + 2 * |x| ^ 3 := by
  rcases le_total |x| (1 / 2) with h | h
  · have hx2 : x ^ 2 ≤ 1 / 4 := by
      have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      rw [this]
      calc |x| ^ 2 ≤ (1 / 2) ^ 2 := by
            apply pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = 1 / 4 := by norm_num
    have hnn3 : (0 : ℝ) ≤ |x| ^ 3 := pow_nonneg (abs_nonneg x) 3
    linarith
  · have hx2 : x ^ 2 ≤ 2 * |x| ^ 3 := by
      have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      rw [hsq]
      have hpos : (0 : ℝ) < |x| := lt_of_lt_of_le (by norm_num) h
      have h1 : (1 : ℝ) ≤ 2 * |x| := by linarith
      calc |x| ^ 2 = |x| ^ 2 * 1 := (mul_one _).symm
        _ ≤ |x| ^ 2 * (2 * |x|) := by
            apply mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = 2 * |x| ^ 3 := by ring
    linarith

/-- N6(b): second moment bounded by third absolute moment on a probability space. -/
private lemma integral_sq_le_quarter_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Ω → ℝ} (hξ : MemLp ξ 3 P) :
    P[fun ω => ξ ω ^ 2] ≤ 1 / 4 + 2 * P[fun ω => |ξ ω| ^ 3] := by
  have hP2 : MemLp ξ 2 P := hξ.mono_exponent (by norm_num)
  have hint2 : Integrable (fun ω => ξ ω ^ 2) P := hP2.integrable_sq
  have hint3 : Integrable (fun ω => |ξ ω| ^ 3) P := by
    have h3 := hξ.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using h3
  have hconst : Integrable (fun _ : Ω => (1 / 4 : ℝ)) P :=
    integrable_const _
  have hrhs : Integrable (fun ω => 1 / 4 + 2 * |ξ ω| ^ 3) P :=
    hconst.add (hint3.const_mul 2)
  have hle : (fun ω => ξ ω ^ 2) ≤ (fun ω => 1 / 4 + 2 * |ξ ω| ^ 3) := by
    intro ω
    exact sq_le_quarter_add_two_abs_cube (ξ ω)
  have h := integral_mono hint2 hrhs hle
  have hadd : P[fun ω => 1 / 4 + 2 * |ξ ω| ^ 3]
      = 1 / 4 + 2 * P[fun ω => |ξ ω| ^ 3] := by
    rw [integral_add hconst (hint3.const_mul 2), integral_const, integral_const_mul]
    simp [Measure.real]
  rwa [hadd] at h

/-- N6(c): first absolute moment bounded by root of second moment. -/
private lemma integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    P[fun ω => |Y ω|] ≤ Real.sqrt (P[fun ω => Y ω ^ 2]) := by
  have hnn : 0 ≤ P[fun ω => |Y ω|] := integral_nonneg (fun ω => abs_nonneg _)
  have hnn2 : 0 ≤ P[fun ω => Y ω ^ 2] :=
    integral_nonneg (fun ω => sq_nonneg _)
  rw [Real.le_sqrt hnn hnn2]
  have hmem : MemLp (fun ω => |Y ω|) 2 P := hY.norm
  have hvar := variance_nonneg (fun ω => |Y ω|) P
  have heq := variance_eq_sub hmem
  rw [heq] at hvar
  simp only [Pi.pow_apply, sq_abs] at hvar
  linarith [hvar]

/-- Squared form of N6(c): `(∫|Y|)² ≤ ∫Y²`. -/
private lemma sq_integral_abs_le_integral_sq {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    (P[fun ω => |Y ω|]) ^ 2 ≤ P[fun ω => Y ω ^ 2] := by
  have h := integral_abs_le_sqrt_integral_sq hY
  have hnn : 0 ≤ P[fun ω => |Y ω|] :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hnn2 : 0 ≤ P[fun ω => Y ω ^ 2] :=
    integral_nonneg (fun ω => sq_nonneg _)
  calc (P[fun ω => |Y ω|]) ^ 2
      ≤ (Real.sqrt (P[fun ω => Y ω ^ 2])) ^ 2 :=
        pow_le_pow_left₀ hnn h 2
    _ = P[fun ω => Y ω ^ 2] := Real.sq_sqrt hnn2

/-- Cauchy–Schwarz step: `(∫ξ²)² ≤ (∫|ξ|³)(∫|ξ|)`, via Hölder with `p = q = 2`
applied to `|ξ|√|ξ|` and `√|ξ|`. -/
private lemma sq_integral_sq_le_mul {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Ω → ℝ} (hξ : MemLp ξ 3 P) :
    (P[fun ω => ξ ω ^ 2]) ^ 2
      ≤ P[fun ω => |ξ ω| ^ 3] * P[fun ω => |ξ ω|] := by
  have hξm : AEStronglyMeasurable ξ P := hξ.aestronglyMeasurable
  have hcontf : Continuous (fun x : ℝ => |x| * Real.sqrt |x|) :=
    continuous_abs.mul (Real.continuous_sqrt.comp continuous_abs)
  have hcontg : Continuous (fun x : ℝ => Real.sqrt |x|) :=
    Real.continuous_sqrt.comp continuous_abs
  have hfm : AEStronglyMeasurable (fun ω => |ξ ω| * Real.sqrt |ξ ω|) P :=
    hcontf.comp_aestronglyMeasurable hξm
  have hgm : AEStronglyMeasurable (fun ω => Real.sqrt |ξ ω|) P :=
    hcontg.comp_aestronglyMeasurable hξm
  have h3 : Integrable (fun ω => |ξ ω| ^ 3) P := by
    have h := hξ.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using h
  have hξ1 : MemLp ξ 1 P := hξ.mono_exponent (by norm_num)
  have h1 : Integrable (fun ω => |ξ ω|) P := by
    have h := hξ1.norm
    rw [memLp_one_iff_integrable] at h
    simpa [Real.norm_eq_abs] using h
  have hf2 : Integrable (fun ω => (|ξ ω| * Real.sqrt |ξ ω|) ^ 2) P := by
    have heq : (fun ω => (|ξ ω| * Real.sqrt |ξ ω|) ^ 2)
        = (fun ω => |ξ ω| ^ 3) := by
      funext ω
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
      ring
    rw [heq]
    exact h3
  have hMf : MemLp (fun ω => |ξ ω| * Real.sqrt |ξ ω|) 2 P :=
    (memLp_two_iff_integrable_sq hfm).mpr hf2
  have hg2 : Integrable (fun ω => (Real.sqrt |ξ ω|) ^ 2) P := by
    have heq : (fun ω => (Real.sqrt |ξ ω|) ^ 2)
        = (fun ω => |ξ ω|) := by
      funext ω
      exact Real.sq_sqrt (abs_nonneg _)
    rw [heq]
    exact h1
  have hMg : MemLp (fun ω => Real.sqrt |ξ ω|) 2 P :=
    (memLp_two_iff_integrable_sq hgm).mpr hg2
  have hMf' : MemLp (fun ω => |ξ ω| * Real.sqrt |ξ ω|)
      (ENNReal.ofReal 2) P := by
    simpa using hMf
  have hMg' : MemLp (fun ω => Real.sqrt |ξ ω|)
      (ENNReal.ofReal 2) P := by
    simpa using hMg
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P)
    Real.HolderConjugate.two_two
    (f := fun ω => |ξ ω| * Real.sqrt |ξ ω|)
    (g := fun ω => Real.sqrt |ξ ω|)
    (Filter.Eventually.of_forall
      (fun ω => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)))
    (Filter.Eventually.of_forall
      (fun ω => Real.sqrt_nonneg _)) hMf' hMg'
  have hLHS : (∫ a, (fun ω => |ξ ω| * Real.sqrt |ξ ω|) a
        * (fun ω => Real.sqrt |ξ ω|) a ∂P)
      = P[fun ω => ξ ω ^ 2] := by
    apply integral_congr_ae
    filter_upwards with ω
    show (|ξ ω| * Real.sqrt |ξ ω|) * Real.sqrt |ξ ω| = ξ ω ^ 2
    have hsq : Real.sqrt |ξ ω| * Real.sqrt |ξ ω| = |ξ ω| :=
      Real.mul_self_sqrt (abs_nonneg _)
    calc (|ξ ω| * Real.sqrt |ξ ω|) * Real.sqrt |ξ ω|
        = |ξ ω| * (Real.sqrt |ξ ω| * Real.sqrt |ξ ω|) := by ring
      _ = |ξ ω| * |ξ ω| := by rw [hsq]
      _ = ξ ω ^ 2 := by rw [← pow_two, sq_abs]
  have hR1 : (∫ a, ((fun ω => |ξ ω| * Real.sqrt |ξ ω|) a) ^ (2 : ℝ) ∂P)
      = P[fun ω => |ξ ω| ^ 3] := by
    apply integral_congr_ae
    filter_upwards with ω
    show (|ξ ω| * Real.sqrt |ξ ω|) ^ (2 : ℝ) = |ξ ω| ^ 3
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (abs_nonneg _)]
    ring
  have hR2 : (∫ a, ((fun ω => Real.sqrt |ξ ω|) a) ^ (2 : ℝ) ∂P)
      = P[fun ω => |ξ ω|] := by
    apply integral_congr_ae
    filter_upwards with ω
    show (Real.sqrt |ξ ω|) ^ (2 : ℝ) = |ξ ω|
    rw [Real.rpow_two, Real.sq_sqrt (abs_nonneg _)]
  rw [hLHS, hR1, hR2] at hH
  have hS2 : 0 ≤ P[fun ω => ξ ω ^ 2] :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hS3 : 0 ≤ P[fun ω => |ξ ω| ^ 3] :=
    integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) _)
  have hS1 : 0 ≤ P[fun ω => |ξ ω|] :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hsq : ((P[fun ω => |ξ ω| ^ 3]) ^ ((1 : ℝ) / 2)
      * (P[fun ω => |ξ ω|]) ^ ((1 : ℝ) / 2)) ^ 2
      = P[fun ω => |ξ ω| ^ 3] * P[fun ω => |ξ ω|] := by
    rw [mul_pow]
    have h12 : (1 : ℝ) / 2 * ((2 : ℕ) : ℝ) = 1 := by norm_num
    have e1 : ((P[fun ω => |ξ ω| ^ 3]) ^ ((1 : ℝ) / 2)) ^ 2
        = P[fun ω => |ξ ω| ^ 3] := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hS3, h12,
        Real.rpow_one]
    have e2 : ((P[fun ω => |ξ ω|]) ^ ((1 : ℝ) / 2)) ^ 2
        = P[fun ω => |ξ ω|] := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hS1, h12,
        Real.rpow_one]
    rw [e1, e2]
  calc (P[fun ω => ξ ω ^ 2]) ^ 2
      ≤ ((P[fun ω => |ξ ω| ^ 3]) ^ ((1 : ℝ) / 2)
        * (P[fun ω => |ξ ω|]) ^ ((1 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left₀ hS2 hH 2
    _ = P[fun ω => |ξ ω| ^ 3] * P[fun ω => |ξ ω|] := hsq

/-- N6(a): Lyapunov inequality `(∫ξ²)(∫|ξ|) ≤ ∫|ξ|³` on a probability space. -/
private lemma integral_sq_mul_integral_abs_le {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Ω → ℝ} (hξ : MemLp ξ 3 P) :
    P[fun ω => ξ ω ^ 2] * P[fun ω => |ξ ω|]
      ≤ P[fun ω => |ξ ω| ^ 3] := by
  have hξ2 : MemLp ξ 2 P := hξ.mono_exponent (by norm_num)
  have hA := sq_integral_abs_le_integral_sq hξ2
  have hB := sq_integral_sq_le_mul hξ
  have hS2 : 0 ≤ P[fun ω => ξ ω ^ 2] :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hS3 : 0 ≤ P[fun ω => |ξ ω| ^ 3] :=
    integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) _)
  have hS1 : 0 ≤ P[fun ω => |ξ ω|] :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hC : (P[fun ω => ξ ω ^ 2] * P[fun ω => |ξ ω|]) ^ 2
      ≤ P[fun ω => |ξ ω| ^ 3]
        * (P[fun ω => ξ ω ^ 2] * P[fun ω => |ξ ω|]) := by
    have hmul : (P[fun ω => ξ ω ^ 2]) ^ 2 * (P[fun ω => |ξ ω|]) ^ 2
        ≤ (P[fun ω => |ξ ω| ^ 3] * P[fun ω => |ξ ω|])
          * P[fun ω => ξ ω ^ 2] := by
      apply mul_le_mul hB hA (sq_nonneg _) _
      exact mul_nonneg hS3 hS1
    calc (P[fun ω => ξ ω ^ 2] * P[fun ω => |ξ ω|]) ^ 2
        = (P[fun ω => ξ ω ^ 2]) ^ 2 * (P[fun ω => |ξ ω|]) ^ 2 := by
          ring
      _ ≤ (P[fun ω => |ξ ω| ^ 3] * P[fun ω => |ξ ω|])
          * P[fun ω => ξ ω ^ 2] := hmul
      _ = P[fun ω => |ξ ω| ^ 3]
          * (P[fun ω => ξ ω ^ 2] * P[fun ω => |ξ ω|]) := by ring
  rcases eq_or_lt_of_le (mul_nonneg hS2 hS1) with h0 | hpos
  · rw [← h0]
    exact hS3
  · have hC2 : (P[fun ω => ξ ω ^ 2] * P[fun ω => |ξ ω|])
        * (P[fun ω => ξ ω ^ 2] * P[fun ω => |ξ ω|])
        ≤ P[fun ω => |ξ ω| ^ 3]
          * (P[fun ω => ξ ω ^ 2] * P[fun ω => |ξ ω|]) := by
      rwa [pow_two] at hC
    exact (mul_le_mul_iff_left₀ hpos).mp hC2

/-- N7: second moment of an independent centered sum. -/
private lemma integral_sq_finsetSum_of_iIndepFun {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hindep : iIndepFun ξ P) {t : Finset ℕ}
    (hmem : ∀ j ∈ t, MemLp (ξ j) 2 P)
    (hmean : ∀ j ∈ t, P[ξ j] = 0) :
    P[fun ω => (∑ j ∈ t, ξ j ω) ^ 2]
      = ∑ j ∈ t, P[fun ω => (ξ j ω) ^ 2] := by
  have hpair : Set.Pairwise (↑t : Set ℕ)
      fun i j => (ξ i) ⟂ᵢ[P] (ξ j) := by
    intro i _ j _ hij
    exact hindep.indepFun hij
  have hvar := IndepFun.variance_sum hmem hpair
  have hsum_mem : MemLp (∑ i ∈ t, ξ i) 2 P := memLp_finsetSum' t hmem
  have hint_each : ∀ j ∈ t, Integrable (ξ j) P := fun j hj => by
    have h1 : MemLp (ξ j) 1 P := (hmem j hj).mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp h1
  have hmean_sum : P[∑ i ∈ t, ξ i] = 0 := by
    have e : (∑ i ∈ t, ξ i) = (fun ω => ∑ i ∈ t, ξ i ω) := by
      funext ω
      exact Finset.sum_apply _ _ _
    rw [e, integral_finsetSum t (fun j hj => hint_each j hj)]
    trans ∑ _j ∈ t, (0 : ℝ)
    · exact Finset.sum_congr rfl (fun j hj => hmean j hj)
    · simp
  have hsub := variance_eq_sub hsum_mem
  have hsum_sq : P[(∑ i ∈ t, ξ i) ^ 2]
      = P[fun ω => (∑ j ∈ t, ξ j ω) ^ 2] := by
    have e2 : ((∑ i ∈ t, ξ i) ^ 2)
        = (fun ω => (∑ j ∈ t, ξ j ω) ^ 2) := by
      funext ω
      simp only [Pi.pow_apply]
      congr 1
      exact Finset.sum_apply _ _ _
    rw [e2]
  rw [hmean_sum] at hsub
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at hsub
  rw [hsum_sq] at hsub
  have heach : ∀ j ∈ t, Var[ξ j; P] = P[fun ω => (ξ j ω) ^ 2] := by
    intro j hj
    have h := variance_eq_sub (hmem j hj)
    rw [hmean j hj] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero] at h
    have e3 : ((ξ j) ^ 2) = (fun ω => (ξ j ω) ^ 2) := by
      funext ω
      simp only [Pi.pow_apply]
    rw [e3] at h
    exact h
  rw [← hsub, hvar]
  exact Finset.sum_congr rfl heach

/-- Leave-one-out rewriting: `Vᵢ + ξᵢ = W` pointwise. -/
private lemma sum_erase_add_pointwise {Ω : Type*} {ξ : ℕ → Ω → ℝ}
    {s : Finset ℕ} {i : ℕ} (hi : i ∈ s) (ω : Ω) :
    (∑ j ∈ s.erase i, ξ j ω) + ξ i ω = ∑ j ∈ s, ξ j ω := by
  calc (∑ j ∈ s.erase i, ξ j ω) + ξ i ω
      = ξ i ω + (∑ j ∈ s.erase i, ξ j ω) := by ring
    _ = ∑ j ∈ s, ξ j ω :=
        Finset.add_sum_erase s (fun j => ξ j ω) hi

/-- N8: Stein expansion by independence. -/
private lemma integral_sum_mul_eq_sum_leaveOneOut {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hmeas : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) {s : Finset ℕ}
    (hint : ∀ i ∈ s, Integrable (ξ i) P)
    (hmean : ∀ i ∈ s, P[ξ i] = 0)
    {f : ℝ → ℝ} (hfmeas : Measurable f) {M : ℝ}
    (hbdd : ∀ x, ‖f x‖ ≤ M) :
    (∫ ω, (∑ i ∈ s, ξ i ω) * f (∑ i ∈ s, ξ i ω) ∂P)
      = ∑ i ∈ s, ∫ ω, ξ i ω
        * (f (∑ j ∈ s, ξ j ω)
          - f ((∑ j ∈ s.erase i, ξ j) ω)) ∂P := by
  have hWmeas : Measurable (fun ω => ∑ j ∈ s, ξ j ω) :=
    Finset.measurable_sum s (fun j _ => hmeas j)
  have hfW : AEStronglyMeasurable (fun ω => f (∑ j ∈ s, ξ j ω)) P :=
    (hfmeas.comp hWmeas).aestronglyMeasurable
  have hbddW : ∀ᵐ ω ∂P, ‖(fun ω => f (∑ j ∈ s, ξ j ω)) ω‖ ≤ M :=
    Filter.Eventually.of_forall (fun ω => hbdd _)
  have htermW : ∀ i ∈ s,
      Integrable (fun ω => ξ i ω * f (∑ j ∈ s, ξ j ω)) P := by
    intro i hi
    exact (hint i hi).mul_bdd hfW hbddW
  have hVmeas_fun : ∀ i ∈ s, Measurable (∑ j ∈ s.erase i, ξ j) := by
    intro i hi
    have hpt : Measurable (fun ω => ∑ j ∈ s.erase i, ξ j ω) :=
      Finset.measurable_sum _ (fun j _ => hmeas j)
    have heq : (∑ j ∈ s.erase i, ξ j)
        = (fun ω => ∑ j ∈ s.erase i, ξ j ω) := by
      funext ω
      exact Finset.sum_apply _ _ _
    rwa [heq]
  have htermV : ∀ i ∈ s,
      Integrable (fun ω => ξ i ω * f ((∑ j ∈ s.erase i, ξ j) ω)) P := by
    intro i hi
    have hfV : AEStronglyMeasurable
        (fun ω => f ((∑ j ∈ s.erase i, ξ j) ω)) P :=
      (hfmeas.comp (hVmeas_fun i hi)).aestronglyMeasurable
    have hbddV : ∀ᵐ ω ∂P,
        ‖(fun ω => f ((∑ j ∈ s.erase i, ξ j) ω)) ω‖ ≤ M :=
      Filter.Eventually.of_forall (fun ω => hbdd _)
    exact (hint i hi).mul_bdd hfV hbddV
  have hzero : ∀ i ∈ s,
      (∫ ω, ξ i ω * f ((∑ j ∈ s.erase i, ξ j) ω) ∂P) = 0 := by
    intro i hi
    have h1 : IndepFun (∑ j ∈ s.erase i, ξ j) (ξ i) P :=
      hindep.indepFun_finsetSum_of_notMem hmeas
        (Finset.notMem_erase i s)
    have h2 : (ξ i) ⟂ᵢ[P] (∑ j ∈ s.erase i, ξ j) := h1.symm
    have h3 : ((fun x : ℝ => x) ∘ (ξ i)) ⟂ᵢ[P]
        (f ∘ (∑ j ∈ s.erase i, ξ j)) :=
      IndepFun.comp h2 measurable_id hfmeas
    have hX : AEStronglyMeasurable ((fun x : ℝ => x) ∘ (ξ i)) P :=
      (measurable_id.comp (hmeas i)).aestronglyMeasurable
    have hY : AEStronglyMeasurable (f ∘ (∑ j ∈ s.erase i, ξ j)) P :=
      (hfmeas.comp (hVmeas_fun i hi)).aestronglyMeasurable
    have hfact := IndepFun.integral_fun_mul_eq_mul_integral h3 hX hY
    have eX : (∫ ω, ((fun x : ℝ => x) ∘ (ξ i)) ω ∂P) = 0 := by
      simp only [Function.comp_def]
      exact hmean i hi
    have eXY : (∫ ω, ((fun x : ℝ => x) ∘ (ξ i)) ω
          * (f ∘ (∑ j ∈ s.erase i, ξ j)) ω ∂P)
        = ∫ ω, ξ i ω * f ((∑ j ∈ s.erase i, ξ j) ω) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      show ((fun x : ℝ => x) ∘ (ξ i)) ω
          * (f ∘ (∑ j ∈ s.erase i, ξ j)) ω
        = ξ i ω * f ((∑ j ∈ s.erase i, ξ j) ω)
      simp only [Function.comp_def]
    rw [← eXY, hfact, eX, zero_mul]
  have hdiff : ∀ i ∈ s,
      (∫ ω, ξ i ω * (f (∑ j ∈ s, ξ j ω)
        - f ((∑ j ∈ s.erase i, ξ j) ω)) ∂P)
      = ∫ ω, ξ i ω * f (∑ j ∈ s, ξ j ω) ∂P := by
    intro i hi
    have e2 : (∫ ω, ξ i ω * (f (∑ j ∈ s, ξ j ω)
          - f ((∑ j ∈ s.erase i, ξ j) ω)) ∂P)
        = ∫ ω, (ξ i ω * f (∑ j ∈ s, ξ j ω)
          - ξ i ω * f ((∑ j ∈ s.erase i, ξ j) ω)) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      show ξ i ω * (f (∑ j ∈ s, ξ j ω)
          - f ((∑ j ∈ s.erase i, ξ j) ω))
        = ξ i ω * f (∑ j ∈ s, ξ j ω)
          - ξ i ω * f ((∑ j ∈ s.erase i, ξ j) ω)
      rw [mul_sub]
    rw [e2, integral_sub (htermW i hi) (htermV i hi), hzero i hi,
      sub_zero]
  have hsplit : (∫ ω, (∑ i ∈ s, ξ i ω) * f (∑ i ∈ s, ξ i ω) ∂P)
      = ∑ i ∈ s, ∫ ω, ξ i ω * f (∑ j ∈ s, ξ j ω) ∂P := by
    have e : (fun ω => (∑ i ∈ s, ξ i ω) * f (∑ i ∈ s, ξ i ω))
        = (fun ω => ∑ i ∈ s, ξ i ω * f (∑ j ∈ s, ξ j ω)) := by
      funext ω
      rw [Finset.sum_mul]
    rw [e, integral_finsetSum s (fun i hi => htermW i hi)]
  rw [hsplit]
  exact Finset.sum_congr rfl (fun i hi => (hdiff i hi).symm)

/-- N9: independence factorization for window events. -/
private lemma integral_pow_mul_window_le {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ V : Ω → ℝ} (hξ : Measurable ξ) (hV : Measurable V)
    (hindep : ξ ⟂ᵢ[P] V) {z A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hwin : ∀ r : ℝ, 0 ≤ r →
      P.real {ω | |V ω - z| ≤ r} ≤ A * r + B)
    {k : ℕ} (hk : Integrable (fun ω => |ξ ω| ^ k) P)
    (hk1 : Integrable (fun ω => |ξ ω| ^ (k + 1)) P) :
    (∫ ω, |ξ ω| ^ k * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0) ∂P)
      ≤ A * (∫ ω, |ξ ω| ^ (k + 1) ∂P)
        + B * (∫ ω, |ξ ω| ^ k ∂P) := by
  have hWmeas : MeasurableSet {p : ℝ × ℝ | |p.2 - z| ≤ |p.1|} :=
    measurableSet_le
      (continuous_abs.measurable.comp (measurable_snd.sub_const z))
      (continuous_abs.measurable.comp measurable_fst)
  have hwinmeas : ∀ x : ℝ, MeasurableSet {y : ℝ | |y - z| ≤ |x|} :=
    fun x => measurableSet_le
      (continuous_abs.measurable.comp (measurable_id.sub_const z))
      measurable_const
  have hjvmeas : Measurable (fun ω => (ξ ω, V ω)) :=
    hξ.prodMk hV
  have hF_eq : (fun p : ℝ × ℝ => ENNReal.ofReal
        (|p.1| ^ k * (if |p.2 - z| ≤ |p.1| then (1 : ℝ) else 0)))
      = (fun p : ℝ × ℝ => (ENNReal.ofReal |p.1|) ^ k
        * ({p : ℝ × ℝ | |p.2 - z| ≤ |p.1|}.indicator 1 p)) := by
    funext p
    rw [ENNReal.ofReal_mul (pow_nonneg (abs_nonneg _) _),
      ENNReal.ofReal_pow (abs_nonneg _)]
    split_ifs with h
    · have hm : p ∈ {p : ℝ × ℝ | |p.2 - z| ≤ |p.1|} := h
      rw [Set.indicator_of_mem hm]
      simp
    · have hm : p ∉ {p : ℝ × ℝ | |p.2 - z| ≤ |p.1|} := h
      rw [Set.indicator_of_notMem hm]
      simp
  have hFmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (|p.1| ^ k * (if |p.2 - z| ≤ |p.1| then (1 : ℝ) else 0))) := by
    rw [hF_eq]
    exact ((ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp measurable_fst)).pow_const
      k).mul (Measurable.indicator measurable_one hWmeas)
  have hjoint : P.map (fun ω => (ξ ω, V ω))
      = (P.map ξ).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hξ.aemeasurable hV.aemeasurable).mp hindep
  have hintLHS : Integrable
      (fun ω => |ξ ω| ^ k
        * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) P := by
    have hS : MeasurableSet {ω | |V ω - z| ≤ |ξ ω|} :=
      hWmeas.preimage hjvmeas
    have hind : AEStronglyMeasurable
        (fun ω => (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) P := by
      have h : Measurable ({ω | |V ω - z| ≤ |ξ ω|}.indicator
          (fun _ : Ω => (1 : ℝ))) :=
        Measurable.indicator measurable_const hS
      exact h.aestronglyMeasurable
    have hbdd : ∀ᵐ ω ∂P,
        ‖(fun ω => (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) ω‖
          ≤ 1 := by
      filter_upwards with ω
      by_cases h : |V ω - z| ≤ |ξ ω| <;> simp [h]
    exact hk.mul_bdd hind hbdd
  have hnnLHS : 0 ≤ᵐ[P] (fun ω => |ξ ω| ^ k
      * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) := by
    filter_upwards with ω
    apply mul_nonneg (pow_nonneg (abs_nonneg _) _)
    by_cases h : |V ω - z| ≤ |ξ ω| <;> simp [h]
  have hLHS : ENNReal.ofReal
        (∫ ω, |ξ ω| ^ k
          * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0) ∂P)
      = ∫⁻ p, ENNReal.ofReal
        (|p.1| ^ k * (if |p.2 - z| ≤ |p.1| then (1 : ℝ) else 0))
        ∂(P.map (fun ω => (ξ ω, V ω))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hintLHS hnnLHS,
      lintegral_map hFmeas hjvmeas]
  have hinner : ∀ x : ℝ, (∫⁻ y, (fun p : ℝ × ℝ => ENNReal.ofReal
        (|p.1| ^ k * (if |p.2 - z| ≤ |p.1| then (1 : ℝ) else 0)))
        (x, y) ∂(P.map V))
      ≤ ENNReal.ofReal (A * |x| ^ (k + 1) + B * |x| ^ k) := by
    intro x
    have e1 : (∫⁻ y, ENNReal.ofReal
          (|x| ^ k * (if |y - z| ≤ |x| then (1 : ℝ) else 0))
          ∂(P.map V))
        = (ENNReal.ofReal (|x| ^ k))
          * ((P.map V) {y | |y - z| ≤ |x|}) := by
      have e : (fun y => ENNReal.ofReal
            (|x| ^ k * (if |y - z| ≤ |x| then (1 : ℝ) else 0)))
          = fun y => (ENNReal.ofReal (|x| ^ k))
            * (({y : ℝ | |y - z| ≤ |x|}.indicator 1) y) := by
        funext y
        rw [ENNReal.ofReal_mul (pow_nonneg (abs_nonneg _) _)]
        split_ifs with h
        · have hm : y ∈ {y : ℝ | |y - z| ≤ |x|} := h
          rw [Set.indicator_of_mem hm]
          simp
        · have hm : y ∉ {y : ℝ | |y - z| ≤ |x|} := h
          rw [Set.indicator_of_notMem hm]
          simp
      rw [e, lintegral_const_mul _
        (Measurable.indicator measurable_one (hwinmeas x)),
        lintegral_indicator_one (hwinmeas x)]
    have hmap : ((P.map V) {y | |y - z| ≤ |x|})
        = ENNReal.ofReal (P.real (V ⁻¹' {y | |y - z| ≤ |x|})) := by
      have hne : (P.map V) {y | |y - z| ≤ |x|} ≠ ∞ :=
        measure_ne_top _ _
      have hrr : ((P.map V) {y | |y - z| ≤ |x|}).toReal
          = P.real (V ⁻¹' {y | |y - z| ≤ |x|}) := by
        rw [← measureReal_def]
        exact map_measureReal_apply hV (hwinmeas x)
      rw [← ENNReal.ofReal_toReal hne, hrr]
    have hle : P.real (V ⁻¹' {y | |y - z| ≤ |x|}) ≤ A * |x| + B :=
      hwin |x| (abs_nonneg _)
    have hmul : ENNReal.ofReal (|x| ^ k)
          * ENNReal.ofReal (P.real (V ⁻¹' {y | |y - z| ≤ |x|}))
        = ENNReal.ofReal
          (|x| ^ k * P.real (V ⁻¹' {y | |y - z| ≤ |x|})) :=
      (ENNReal.ofReal_mul (pow_nonneg (abs_nonneg _) k)).symm
    have hshow : (∫⁻ y, (fun p : ℝ × ℝ => ENNReal.ofReal
          (|p.1| ^ k * (if |p.2 - z| ≤ |p.1| then (1 : ℝ) else 0)))
          (x, y) ∂(P.map V))
        = ∫⁻ y, ENNReal.ofReal
          (|x| ^ k * (if |y - z| ≤ |x| then (1 : ℝ) else 0))
          ∂(P.map V) := rfl
    rw [hshow, e1, hmap, hmul]
    apply ENNReal.ofReal_le_ofReal
    calc |x| ^ k * P.real (V ⁻¹' {y | |y - z| ≤ |x|})
        ≤ |x| ^ k * (A * |x| + B) :=
          mul_le_mul_of_nonneg_left hle
            (pow_nonneg (abs_nonneg _) _)
      _ = A * |x| ^ (k + 1) + B * |x| ^ k := by
          rw [pow_succ]
          ring
  have hpow1 : Measurable (fun x : ℝ => |x| ^ (k + 1)) :=
    (continuous_abs.measurable.comp measurable_id).pow_const (k + 1)
  have hpow0 : Measurable (fun x : ℝ => |x| ^ k) :=
    (continuous_abs.measurable.comp measurable_id).pow_const k
  have hAmul : Measurable (fun x : ℝ => A * |x| ^ (k + 1)) :=
    measurable_const.mul hpow1
  have hBmul : Measurable (fun x : ℝ => B * |x| ^ k) :=
    measurable_const.mul hpow0
  have hGmeas : Measurable (fun x : ℝ => ENNReal.ofReal
      (A * |x| ^ (k + 1) + B * |x| ^ k)) :=
    ENNReal.measurable_ofReal.comp (hAmul.add hBmul)
  have hRHS : ENNReal.ofReal
        (A * (∫ ω, |ξ ω| ^ (k + 1) ∂P)
          + B * (∫ ω, |ξ ω| ^ k ∂P))
      = ∫⁻ x, ENNReal.ofReal (A * |x| ^ (k + 1) + B * |x| ^ k)
        ∂(P.map ξ) := by
    have hint : Integrable
        (fun ω => A * |ξ ω| ^ (k + 1) + B * |ξ ω| ^ k) P :=
      (hk1.const_mul A).add (hk.const_mul B)
    have hnn : 0 ≤ᵐ[P]
        (fun ω => A * |ξ ω| ^ (k + 1) + B * |ξ ω| ^ k) := by
      filter_upwards with ω
      exact add_nonneg (mul_nonneg hA (pow_nonneg (abs_nonneg _) _))
        (mul_nonneg hB (pow_nonneg (abs_nonneg _) _))
    have hbase := ofReal_integral_eq_lintegral_ofReal hint hnn
    have eInt : (∫ ω, A * |ξ ω| ^ (k + 1) + B * |ξ ω| ^ k ∂P)
        = A * (∫ ω, |ξ ω| ^ (k + 1) ∂P)
          + B * (∫ ω, |ξ ω| ^ k ∂P) := by
      rw [integral_add (hk1.const_mul A) (hk.const_mul B),
        integral_const_mul, integral_const_mul]
    have hmap2 : (∫⁻ ω, ENNReal.ofReal
          (A * |ξ ω| ^ (k + 1) + B * |ξ ω| ^ k) ∂P)
        = ∫⁻ x, ENNReal.ofReal (A * |x| ^ (k + 1) + B * |x| ^ k)
          ∂(P.map ξ) := by
      have h := lintegral_map (μ := P) hGmeas hξ
      -- h : ∫⁻ x, G x ∂map = ∫⁻ ω, G (ξ ω) ∂P
      exact h.symm
    rw [← eInt, hbase]
    exact hmap2
  have hF_aemeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (|p.1| ^ k * (if |p.2 - z| ≤ |p.1| then (1 : ℝ) else 0)))
      ((P.map ξ).prod (P.map V)) := hFmeas.aemeasurable
  have hle : (∫⁻ p, ENNReal.ofReal
        (|p.1| ^ k * (if |p.2 - z| ≤ |p.1| then (1 : ℝ) else 0))
        ∂(P.map ξ).prod (P.map V))
      ≤ ENNReal.ofReal (A * (∫ ω, |ξ ω| ^ (k + 1) ∂P)
        + B * (∫ ω, |ξ ω| ^ k ∂P)) := by
    rw [lintegral_prod _ hF_aemeas, hRHS]
    apply lintegral_mono
    intro x
    exact hinner x
  have hRHS_nn : 0 ≤ A * (∫ ω, |ξ ω| ^ (k + 1) ∂P)
      + B * (∫ ω, |ξ ω| ^ k ∂P) :=
    add_nonneg
      (mul_nonneg hA
        (integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _))
      (mul_nonneg hB
        (integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _))
  rw [hjoint] at hLHS
  rw [← hLHS] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hRHS_nn).mp hle

/-- Clamp function for the concentration inequality. -/
private noncomputable def clampFun (a b δ : ℝ) (w : ℝ) : ℝ :=
  max (a - δ) (min w (b + δ)) - (a + b) / 2

private lemma clampFun_mono (a b δ : ℝ) :
    Monotone (clampFun a b δ) := by
  intro u v huv
  unfold clampFun
  have h1 : min u (b + δ) ≤ min v (b + δ) :=
    min_le_min huv le_rfl
  have h2 : max (a - δ) (min u (b + δ))
      ≤ max (a - δ) (min v (b + δ)) :=
    max_le_max le_rfl h1
  exact sub_le_sub_right h2 _

private lemma clampFun_measurable (a b δ : ℝ) :
    Measurable (clampFun a b δ) :=
  (clampFun_mono a b δ).measurable

private lemma abs_clampFun_le (a b δ : ℝ) (hab : a ≤ b)
    (hδ : 0 ≤ δ) (w : ℝ) :
    |clampFun a b δ w| ≤ (b - a) / 2 + δ := by
  have hlo : a - δ ≤ max (a - δ) (min w (b + δ)) :=
    le_max_left _ _
  have hhi : max (a - δ) (min w (b + δ)) ≤ b + δ :=
    max_le (by linarith) (min_le_right _ _)
  unfold clampFun
  rw [abs_le]
  constructor <;> linarith

private lemma clamp_mul_nonneg (a b δ v x : ℝ) :
    0 ≤ x * (clampFun a b δ v - clampFun a b δ (v - x)) := by
  rcases le_total 0 x with hx | hx
  · have h : clampFun a b δ (v - x) ≤ clampFun a b δ v :=
      clampFun_mono a b δ (by linarith)
    exact mul_nonneg hx (by linarith)
  · have h : clampFun a b δ v ≤ clampFun a b δ (v - x) :=
      clampFun_mono a b δ (by linarith)
    exact mul_nonneg_of_nonpos_of_nonpos hx (by linarith)

private lemma clampFun_eq_of_mem (a b δ w : ℝ) (hlo : a - δ ≤ w)
    (hhi : w ≤ b + δ) :
    clampFun a b δ w = w - (a + b) / 2 := by
  unfold clampFun
  rw [min_eq_left hhi, max_eq_right hlo]

/-- N10a key pointwise bound on the event. -/
private lemma clamp_key_le (a b δ v x : ℝ) (hδ : 0 ≤ δ)
    (hav : a ≤ v) (hvb : v ≤ b) :
    |x| * min δ |x|
      ≤ x * (clampFun a b δ v - clampFun a b δ (v - x)) := by
  have hmono := clampFun_mono a b δ
  have hsign : x * (clampFun a b δ v - clampFun a b δ (v - x))
      = |x| * |clampFun a b δ v - clampFun a b δ (v - x)| := by
    rcases le_total 0 x with hx | hx
    · have hd : 0 ≤ clampFun a b δ v - clampFun a b δ (v - x) :=
        sub_nonneg.mpr (hmono (by linarith))
      rw [abs_of_nonneg hx, abs_of_nonneg hd]
    · have hd : clampFun a b δ v - clampFun a b δ (v - x) ≤ 0 :=
        sub_nonpos.mpr (hmono (by linarith))
      rw [abs_of_nonpos hx, abs_of_nonpos hd]
      ring
  rw [hsign]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rcases le_total |x| δ with hle | hle
  · have hmin : min δ |x| = |x| := min_eq_right hle
    rw [hmin]
    have hx_bnd := abs_le.mp hle
    have h1 : a - δ ≤ v - x := by linarith [hav, hx_bnd.2]
    have h2 : v - x ≤ b + δ := by linarith [hvb, hx_bnd.1]
    have e1 := clampFun_eq_of_mem a b δ v (by linarith) (by linarith)
    have e2 := clampFun_eq_of_mem a b δ (v - x) h1 h2
    rw [e1, e2]
    have heq : (v - (a + b) / 2) - (v - x - (a + b) / 2) = x := by
      ring
    rw [heq]
  · have hmin : min δ |x| = δ := min_eq_left hle
    rw [hmin]
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [sub_zero, sub_self, abs_zero]
      simpa using hle
    · rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · have habsx : |x| = -x := abs_of_neg hneg
        have hδx : δ ≤ -x := by rwa [habsx] at hle
        have e1 := clampFun_eq_of_mem a b δ v (by linarith)
          (by linarith)
        have hmin2 : v + δ ≤ min (v - x) (b + δ) :=
          le_min (by linarith) (by linarith)
        have hmax : v + δ ≤ max (a - δ) (min (v - x) (b + δ)) :=
          le_trans hmin2 (le_max_right _ _)
        have eV : clampFun a b δ (v - x)
            = max (a - δ) (min (v - x) (b + δ)) - (a + b) / 2 :=
          rfl
        have hge : δ ≤ clampFun a b δ (v - x)
            - clampFun a b δ v := by
          rw [e1, eV]
          linarith [hmax]
        calc δ ≤ clampFun a b δ (v - x) - clampFun a b δ v := hge
          _ ≤ |clampFun a b δ (v - x) - clampFun a b δ v| :=
            le_abs_self _
          _ = |clampFun a b δ v - clampFun a b δ (v - x)| :=
            abs_sub_comm _ _
      · have habsx : |x| = x := abs_of_nonneg hpos.le
        have hδx : δ ≤ x := by rwa [habsx] at hle
        have hvx_le : v - x ≤ b + δ := by linarith [hvb, hpos.le, hδ]
        have e1 := clampFun_eq_of_mem a b δ v (by linarith)
          (by linarith)
        have hmax : max (a - δ) (min (v - x) (b + δ)) ≤ v - δ := by
          rw [min_eq_left hvx_le]
          exact max_le (by linarith) (by linarith)
        have eV : clampFun a b δ (v - x)
            = max (a - δ) (min (v - x) (b + δ)) - (a + b) / 2 :=
          rfl
        have hge : δ ≤ clampFun a b δ v - clampFun a b δ (v - x) := by
          rw [e1, eV]
          linarith [hmax]
        exact le_trans hge (le_abs_self _)

/-- The summand `h(x) = min δ |x| · |x|` for the concentration proof. -/
private noncomputable def concH (δ : ℝ) (x : ℝ) : ℝ :=
  min δ |x| * |x|

private lemma continuous_concH (δ : ℝ) : Continuous (concH δ) := by
  unfold concH
  exact (continuous_const.min continuous_abs).mul continuous_abs

private lemma concH_nonneg (δ : ℝ) (hδ : 0 ≤ δ) (x : ℝ) :
    0 ≤ concH δ x := by
  unfold concH
  exact mul_nonneg (le_min hδ (abs_nonneg _)) (abs_nonneg _)

private lemma concH_sq_le (δ : ℝ) (hδ : 0 ≤ δ) (x : ℝ) :
    (concH δ x) ^ 2 ≤ δ * |x| ^ 3 := by
  have hmin1 : min δ |x| ≤ δ := min_le_left _ _
  have hmin2 : min δ |x| ≤ |x| := min_le_right _ _
  have hsq : (min δ |x|) ^ 2 ≤ δ * |x| :=
    calc (min δ |x|) ^ 2
        = min δ |x| * min δ |x| := pow_two _
      _ ≤ δ * |x| :=
        mul_le_mul hmin1 hmin2 (le_min hδ (abs_nonneg _)) hδ
  unfold concH
  rw [mul_pow]
  calc (min δ |x|) ^ 2 * |x| ^ 2
      ≤ (δ * |x|) * |x| ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = δ * |x| ^ 3 := by ring

private lemma concH_aux_lower {δ x : ℝ} (hδ : 0 < δ) :
    x ^ 2 - |x| ^ 3 / (4 * δ) ≤ δ * |x| := by
  have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hmain : (0:ℝ) ≤ |x| ^ 3 - 4 * δ * |x| ^ 2 + 4 * δ ^ 2 * |x| := by
    have h := mul_nonneg (abs_nonneg x) (sq_nonneg (|x| - 2 * δ))
    have hexpand : |x| * (|x| - 2 * δ) ^ 2
        = |x| ^ 3 - 4 * δ * |x| ^ 2 + 4 * δ ^ 2 * |x| := by ring
    rwa [hexpand] at h
  have h4δ : (0:ℝ) < 4 * δ := by linarith
  have hdiv : |x| ^ 3 / (4 * δ) * (4 * δ) = |x| ^ 3 :=
    div_mul_cancel₀ _ (ne_of_gt h4δ)
  rw [hsq, sub_le_iff_le_add]
  have hmul : |x| ^ 2 * (4 * δ)
      ≤ (δ * |x| + |x| ^ 3 / (4 * δ)) * (4 * δ) := by
    rw [add_mul, hdiv]
    linarith [hmain]
  exact (mul_le_mul_iff_left₀ h4δ).mp hmul

private lemma concH_lower {δ x : ℝ} (hδ : 0 < δ) :
    x ^ 2 - |x| ^ 3 / (4 * δ) ≤ concH δ x := by
  unfold concH
  rcases le_total |x| δ with h | h
  · rw [min_eq_right h]
    have h2 : |x| * |x| = x ^ 2 := by rw [← pow_two, sq_abs]
    rw [h2]
    have hnn : (0:ℝ) ≤ |x| ^ 3 / (4 * δ) :=
      div_nonneg (pow_nonneg (abs_nonneg _) _)
        (le_of_lt (by linarith : (0:ℝ) < 4 * δ))
    linarith
  · rw [min_eq_left h]
    exact concH_aux_lower hδ

/-- N10b(i): the averaged clamp increment is at least `1/4`. -/
private lemma integral_concH_ge_quarter {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} {t : Finset ℕ}
    (hmem : ∀ j ∈ t, MemLp (ξ j) 3 P)
    (hvar_lo : 1 / 2 ≤ ∑ j ∈ t, P[fun ω => (ξ j ω) ^ 2])
    {γ : ℝ} (hγ : 0 < γ)
    (hγ3 : ∑ j ∈ t, P[fun ω => |ξ j ω| ^ 3] ≤ γ) :
    1 / 4 ≤ P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)] := by
  have hmem2 : ∀ j ∈ t, MemLp (ξ j) 2 P :=
    fun j hj => (hmem j hj).mono_exponent (by norm_num)
  have hint_sq : ∀ j ∈ t, Integrable (fun ω => (ξ j ω) ^ 2) P :=
    fun j hj => (hmem2 j hj).integrable_sq
  have hint_cube : ∀ j ∈ t, Integrable (fun ω => |ξ j ω| ^ 3) P := by
    intro j hj
    have h := (hmem j hj).integrable_norm_rpow (by norm_num)
      (by norm_num)
    simpa using h
  have hint_abs : ∀ j ∈ t, Integrable (fun ω => |ξ j ω|) P := by
    intro j hj
    have h1 : MemLp (ξ j) 1 P :=
      (hmem j hj).mono_exponent (by norm_num)
    have h := h1.norm
    rw [memLp_one_iff_integrable] at h
    simpa [Real.norm_eq_abs] using h
  have hae : ∀ j ∈ t, AEStronglyMeasurable
      (fun ω => concH γ (ξ j ω)) P := by
    intro j hj
    exact (continuous_concH γ).comp_aestronglyMeasurable
      (hmem j hj).aestronglyMeasurable
  have hint_h : ∀ j ∈ t,
      Integrable (fun ω => concH γ (ξ j ω)) P := by
    intro j hj
    have hle : ∀ ω, concH γ (ξ j ω) ≤ γ * |ξ j ω| := by
      intro ω
      unfold concH
      exact mul_le_mul_of_nonneg_right (min_le_left _ _)
        (abs_nonneg _)
    exact Integrable.mono_nonneg ((hint_abs j hj).const_mul γ)
      (hae j hj)
      (Filter.Eventually.of_forall
        (fun ω => concH_nonneg γ hγ.le (ξ j ω)))
      (Filter.Eventually.of_forall hle)
  have hdiv_int : ∀ j ∈ t,
      Integrable (fun ω => |ξ j ω| ^ 3 / (4 * γ)) P := by
    intro j hj
    have heq : (fun ω => |ξ j ω| ^ 3 / (4 * γ))
        = fun ω => (4 * γ)⁻¹ * |ξ j ω| ^ 3 := by
      funext ω
      rw [div_eq_inv_mul]
    rw [heq]
    exact (hint_cube j hj).const_mul _
  have hdiv_val : ∀ j ∈ t, (∫ ω, |ξ j ω| ^ 3 / (4 * γ) ∂P)
      = P[fun ω => |ξ j ω| ^ 3] / (4 * γ) := by
    intro j hj
    have heq : (fun ω => |ξ j ω| ^ 3 / (4 * γ))
        = fun ω => (4 * γ)⁻¹ * |ξ j ω| ^ 3 := by
      funext ω
      rw [div_eq_inv_mul]
    rw [heq, integral_const_mul, div_eq_inv_mul]
  have hper : ∀ j ∈ t, P[fun ω => (ξ j ω) ^ 2]
      - P[fun ω => |ξ j ω| ^ 3] / (4 * γ)
      ≤ P[fun ω => concH γ (ξ j ω)] := by
    intro j hj
    have hint_sub : Integrable
        (fun ω => (ξ j ω) ^ 2 - |ξ j ω| ^ 3 / (4 * γ)) P :=
      (hint_sq j hj).sub (hdiv_int j hj)
    have hle := integral_mono hint_sub (hint_h j hj)
      (fun ω => concH_lower hγ)
    rw [integral_sub (hint_sq j hj) (hdiv_int j hj)] at hle
    rw [hdiv_val j hj] at hle
    exact hle
  have hsum := Finset.sum_le_sum hper
  have hHeq : P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]
      = ∑ j ∈ t, P[fun ω => concH γ (ξ j ω)] :=
    integral_finsetSum t (fun j hj => hint_h j hj)
  have hsumdiv : ∑ j ∈ t, (P[fun ω => |ξ j ω| ^ 3] / (4 * γ))
      = (∑ j ∈ t, P[fun ω => |ξ j ω| ^ 3]) / (4 * γ) := by
    simp only [div_eq_inv_mul, ← Finset.mul_sum]
  rw [Finset.sum_sub_distrib, hsumdiv] at hsum
  have h4γ : (0:ℝ) < 4 * γ := by linarith [hγ]
  have hT4 : (∑ j ∈ t, P[fun ω => |ξ j ω| ^ 3]) / (4 * γ)
      ≤ 1 / 4 := by
    rw [div_le_iff₀ h4γ]
    have heq : (1:ℝ) / 4 * (4 * γ) = γ := by ring
    rw [heq]
    exact hγ3
  rw [hHeq]
  linarith [hsum, hvar_lo, hT4]

/-- Deviation of an independent sum from its mean, via its variance. -/
private lemma integral_abs_sum_sub_le_sqrt {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} {Y : ι → Ω → ℝ} (hindep : iIndepFun Y P)
    {t : Finset ι} (hmem : ∀ j ∈ t, MemLp (Y j) 2 P) :
    P[fun ω => |(∑ j ∈ t, Y j ω) - P[fun ω => ∑ j ∈ t, Y j ω]|]
      ≤ Real.sqrt (∑ j ∈ t, P[fun ω => (Y j ω) ^ 2]) := by
  have hpair : Set.Pairwise (↑t : Set ι)
      fun i j => (Y i) ⟂ᵢ[P] (Y j) := by
    intro i _ j _ hij
    exact hindep.indepFun hij
  have hvar := IndepFun.variance_sum hmem hpair
  have hHfun : MemLp (∑ j ∈ t, Y j) 2 P := memLp_finsetSum' t hmem
  have hHpt : MemLp (fun ω => ∑ j ∈ t, Y j ω) 2 P :=
    memLp_finsetSum t hmem
  have hfun_eq : (∑ j ∈ t, Y j) = fun ω => ∑ j ∈ t, Y j ω := by
    funext ω
    exact Finset.sum_apply _ _ _
  have hHint : Integrable (fun ω => ∑ j ∈ t, Y j ω) P := by
    have h1 : MemLp (fun ω => ∑ j ∈ t, Y j ω) 1 P :=
      hHpt.mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp h1
  have hHsq : Integrable (fun ω => (∑ j ∈ t, Y j ω) ^ 2) P :=
    hHpt.integrable_sq
  have hexpand : P[fun ω => ((∑ j ∈ t, Y j ω)
        - P[fun ω => ∑ j ∈ t, Y j ω]) ^ 2]
      = P[fun ω => (∑ j ∈ t, Y j ω) ^ 2]
        - P[fun ω => ∑ j ∈ t, Y j ω] ^ 2 := by
    have e : (fun ω => ((∑ j ∈ t, Y j ω)
          - P[fun ω => ∑ j ∈ t, Y j ω]) ^ 2)
        = (fun ω => (∑ j ∈ t, Y j ω) ^ 2
          - 2 * P[fun ω => ∑ j ∈ t, Y j ω] * (∑ j ∈ t, Y j ω)
          + P[fun ω => ∑ j ∈ t, Y j ω] ^ 2) := by
      funext ω
      ring
    have h2cH : Integrable (fun ω => 2
        * P[fun ω => ∑ j ∈ t, Y j ω] * (∑ j ∈ t, Y j ω)) P :=
      hHint.const_mul (2 * P[fun ω => ∑ j ∈ t, Y j ω])
    have hc2 : Integrable
        (fun _ : Ω => P[fun ω => ∑ j ∈ t, Y j ω] ^ 2) P :=
      integrable_const _
    have hsub' : Integrable (fun ω => (∑ j ∈ t, Y j ω) ^ 2
        - 2 * P[fun ω => ∑ j ∈ t, Y j ω]
          * (∑ j ∈ t, Y j ω)) P :=
      hHsq.sub h2cH
    rw [e, integral_add hsub' hc2, integral_sub hHsq h2cH,
      integral_const_mul, integral_const, probReal_univ, one_smul]
    ring
  have h1 : P[fun ω => (∑ j ∈ t, Y j ω) ^ 2]
      = P[(∑ j ∈ t, Y j) ^ 2] := by
    congr 1
    funext ω
    change (∑ j ∈ t, Y j ω) ^ 2 = ((∑ j ∈ t, Y j) ^ 2) ω
    rw [Pi.pow_apply, Finset.sum_apply]
  have h2 : P[fun ω => ∑ j ∈ t, Y j ω] = P[∑ j ∈ t, Y j] := by
    congr 1
    exact hfun_eq.symm
  have hsub := variance_eq_sub hHfun
  have hvar_eq : P[fun ω => ((∑ j ∈ t, Y j ω)
        - P[fun ω => ∑ j ∈ t, Y j ω]) ^ 2]
      = Var[∑ j ∈ t, Y j; P] := by
    rw [hexpand, hsub, h1, h2]
  have hsq_pt : ∀ j ∈ t, P[(Y j) ^ 2]
      = P[fun ω => (Y j ω) ^ 2] := by
    intro j _
    congr 1
  have hvar_bound : Var[∑ j ∈ t, Y j; P]
      ≤ ∑ j ∈ t, P[fun ω => (Y j ω) ^ 2] := by
    rw [hvar]
    apply Finset.sum_le_sum
    intro j hj
    have h := variance_eq_sub (hmem j hj)
    have hnn : (0:ℝ) ≤ P[Y j] ^ 2 := sq_nonneg _
    rw [h, hsq_pt j hj]
    linarith [hnn]
  have hmem_sub : MemLp (fun ω => (∑ j ∈ t, Y j ω)
      - P[fun ω => ∑ j ∈ t, Y j ω]) 2 P :=
    hHpt.sub (memLp_const _)
  have hcs := sq_integral_abs_le_integral_sq hmem_sub
  have hnn1 : (0:ℝ) ≤ P[fun ω => |(∑ j ∈ t, Y j ω)
      - P[fun ω => ∑ j ∈ t, Y j ω]|] :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hnn2 : (0:ℝ) ≤ ∑ j ∈ t, P[fun ω => (Y j ω) ^ 2] :=
    Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun ω => sq_nonneg _))
  rw [Real.le_sqrt hnn1 hnn2]
  calc (P[fun ω => |(∑ j ∈ t, Y j ω)
      - P[fun ω => ∑ j ∈ t, Y j ω]|]) ^ 2
      ≤ P[fun ω => ((∑ j ∈ t, Y j ω)
        - P[fun ω => ∑ j ∈ t, Y j ω]) ^ 2] := hcs
    _ = Var[∑ j ∈ t, Y j; P] := hvar_eq
    _ ≤ ∑ j ∈ t, P[fun ω => (Y j ω) ^ 2] := hvar_bound

/-- N10b(ii): `H` concentrates around its mean. -/
private lemma integral_abs_concH_sub_le {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hindep : iIndepFun ξ P) {t : Finset ℕ}
    (hmem : ∀ j ∈ t, MemLp (ξ j) 3 P)
    {γ : ℝ} (hγ : 0 < γ)
    (hγ3 : ∑ j ∈ t, P[fun ω => |ξ j ω| ^ 3] ≤ γ) :
    P[fun ω => |(∑ j ∈ t, concH γ (ξ j ω))
      - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]|] ≤ γ := by
  have hmemY : ∀ j ∈ t, MemLp (fun ω => concH γ (ξ j ω)) 2 P := by
    intro j hj
    have hae : AEStronglyMeasurable (fun ω => concH γ (ξ j ω)) P :=
      (continuous_concH γ).comp_aestronglyMeasurable
        (hmem j hj).aestronglyMeasurable
    have hint_cube : Integrable (fun ω => |ξ j ω| ^ 3) P := by
      have h := (hmem j hj).integrable_norm_rpow (by norm_num)
        (by norm_num)
      simpa using h
    have hsq_int : Integrable
        (fun ω => (concH γ (ξ j ω)) ^ 2) P := by
      have hae2 : AEStronglyMeasurable
          (fun ω => (concH γ (ξ j ω)) ^ 2) P :=
        (continuous_pow 2).comp_aestronglyMeasurable hae
      have hle : ∀ᵐ ω ∂P, ‖(concH γ (ξ j ω)) ^ 2‖
          ≤ γ * |ξ j ω| ^ 3 := by
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact concH_sq_le γ hγ.le (ξ j ω)
      exact Integrable.mono' ((hint_cube.const_mul γ)) hae2 hle
    exact (memLp_two_iff_integrable_sq hae).mpr hsq_int
  have hindepY : iIndepFun (fun j => concH γ ∘ ξ j) P :=
    hindep.comp _ (fun _ => (continuous_concH γ).measurable)
  have hmemY' : ∀ j ∈ t, MemLp ((concH γ ∘ ξ j)) 2 P := by
    intro j hj
    exact hmemY j hj
  have hdev := integral_abs_sum_sub_le_sqrt hindepY hmemY'
  -- hdev : ∫|∑(concH∘ξ) − ∫∑..| ≤ √(∑∫(concH∘ξ)²)
  -- convert to pointwise form and bound RHS by γ
  have hconv : P[fun ω => |(∑ j ∈ t, concH γ (ξ j ω))
      - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]|]
      = P[fun ω => |(∑ j ∈ t, (concH γ ∘ ξ j) ω)
        - P[fun ω => ∑ j ∈ t, (concH γ ∘ ξ j) ω]|] := rfl
  rw [hconv]
  have hRHS : Real.sqrt
      (∑ j ∈ t, P[fun ω => ((concH γ ∘ ξ j) ω) ^ 2]) ≤ γ := by
    have hsum : ∑ j ∈ t, P[fun ω => ((concH γ ∘ ξ j) ω) ^ 2]
        ≤ γ ^ 2 := by
      have hper : ∀ j ∈ t, P[fun ω => ((concH γ ∘ ξ j) ω) ^ 2]
          ≤ γ * P[fun ω => |ξ j ω| ^ 3] := by
        intro j hj
        have hint_cube : Integrable (fun ω => |ξ j ω| ^ 3) P := by
          have h := (hmem j hj).integrable_norm_rpow (by norm_num)
            (by norm_num)
          simpa using h
        have hsq_int : Integrable
            (fun ω => ((concH γ ∘ ξ j) ω) ^ 2) P := by
          have hae : AEStronglyMeasurable
              (fun ω => concH γ (ξ j ω)) P :=
            (continuous_concH γ).comp_aestronglyMeasurable
              (hmem j hj).aestronglyMeasurable
          have hae2 : AEStronglyMeasurable
              (fun ω => ((concH γ ∘ ξ j) ω) ^ 2) P :=
            (continuous_pow 2).comp_aestronglyMeasurable
              (by simpa [Function.comp_def] using hae)
          have hle : ∀ᵐ ω ∂P,
              ‖((concH γ ∘ ξ j) ω) ^ 2‖ ≤ γ * |ξ j ω| ^ 3 := by
            filter_upwards with ω
            rw [Function.comp_def, Real.norm_eq_abs,
              abs_of_nonneg (sq_nonneg _)]
            exact concH_sq_le γ hγ.le (ξ j ω)
          exact Integrable.mono' (hint_cube.const_mul γ) hae2 hle
        have hle2 : (fun ω => ((concH γ ∘ ξ j) ω) ^ 2)
            ≤ (fun ω => γ * |ξ j ω| ^ 3) := by
          intro ω
          change ((concH γ ∘ ξ j) ω) ^ 2 ≤ _
          rw [Function.comp_def]
          exact concH_sq_le γ hγ.le (ξ j ω)
        have h := integral_mono hsq_int (hint_cube.const_mul γ) hle2
        rwa [integral_const_mul] at h
      have hsum2 := Finset.sum_le_sum hper
      have hmul : ∑ j ∈ t, γ * P[fun ω => |ξ j ω| ^ 3]
          = γ * ∑ j ∈ t, P[fun ω => |ξ j ω| ^ 3] :=
        (Finset.mul_sum _ _ _).symm
      rw [hmul] at hsum2
      calc ∑ j ∈ t, P[fun ω => ((concH γ ∘ ξ j) ω) ^ 2]
          ≤ γ * ∑ j ∈ t, P[fun ω => |ξ j ω| ^ 3] := hsum2
        _ ≤ γ * γ :=
          mul_le_mul_of_nonneg_left hγ3 hγ.le
        _ = γ ^ 2 := by ring
    calc Real.sqrt (∑ j ∈ t, P[fun ω => ((concH γ ∘ ξ j) ω) ^ 2])
        ≤ Real.sqrt (γ ^ 2) := Real.sqrt_le_sqrt hsum
      _ = γ := Real.sqrt_sq hγ.le
  exact le_trans hdev hRHS

private lemma integrable_concH_comp {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Ω → ℝ} (hmem : MemLp ξ 3 P) {γ : ℝ} (hγ : 0 < γ) :
    Integrable (fun ω => concH γ (ξ ω)) P := by
  have h1 : MemLp ξ 1 P := hmem.mono_exponent (by norm_num)
  have hint_abs : Integrable (fun ω => |ξ ω|) P := by
    have h := h1.norm
    rw [memLp_one_iff_integrable] at h
    simpa [Real.norm_eq_abs] using h
  have hae : AEStronglyMeasurable (fun ω => concH γ (ξ ω)) P :=
    (continuous_concH γ).comp_aestronglyMeasurable
      hmem.aestronglyMeasurable
  exact Integrable.mono_nonneg (hint_abs.const_mul γ) hae
    (Filter.Eventually.of_forall
      (fun ω => concH_nonneg γ hγ.le (ξ ω)))
    (Filter.Eventually.of_forall (fun ω => by
      unfold concH
      exact mul_le_mul_of_nonneg_right (min_le_left _ _)
        (abs_nonneg _)))

/-- N10: concentration inequality for independent sums. -/
private lemma measureReal_Icc_finsetSum_le {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hmeas : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) {t : Finset ℕ}
    (hmem : ∀ j ∈ t, MemLp (ξ j) 3 P)
    (hmean : ∀ j ∈ t, P[ξ j] = 0)
    (hvar_lo : 1 / 2 ≤ ∑ j ∈ t, P[fun ω => (ξ j ω) ^ 2])
    (hvar_hi : ∑ j ∈ t, P[fun ω => (ξ j ω) ^ 2] ≤ 1)
    {γ : ℝ} (hγ : 0 < γ)
    (hγ3 : ∑ j ∈ t, P[fun ω => |ξ j ω| ^ 3] ≤ γ)
    {a b : ℝ} (hab : a ≤ b) :
    P.real {ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}
      ≤ 2 * (b - a) + 8 * γ := by
  have hVmeas : Measurable (fun ω => ∑ j ∈ t, ξ j ω) :=
    Finset.measurable_sum t (fun j _ => hmeas j)
  have hE : MeasurableSet
      {ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b} := by
    have hEq : {ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}
        = (fun ω => ∑ j ∈ t, ξ j ω) ⁻¹' (Set.Icc a b) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_ofPred_eq]
    rw [hEq]
    exact measurableSet_Icc.preimage hVmeas
  have hint : ∀ i ∈ t, Integrable (ξ i) P := by
    intro i hi
    have h1 : MemLp (ξ i) 1 P :=
      (hmem i hi).mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp h1
  have hint_h : ∀ j ∈ t,
      Integrable (fun ω => concH γ (ξ j ω)) P :=
    fun j hj => integrable_concH_comp (hmem j hj) hγ
  have hHint : Integrable (fun ω => ∑ j ∈ t, concH γ (ξ j ω)) P :=
    integrable_finsetSum t hint_h
  have hVint : Integrable (fun ω => ∑ j ∈ t, ξ j ω) P :=
    integrable_finsetSum t (fun i hi => hint i hi)
  have hbdd : ∀ x, ‖clampFun a b γ x‖ ≤ (b - a) / 2 + γ := by
    intro x
    rw [Real.norm_eq_abs]
    exact abs_clampFun_le a b γ hab hγ.le x
  have hN8 := integral_sum_mul_eq_sum_leaveOneOut hmeas hindep
    hint hmean (clampFun_measurable a b γ) hbdd
  -- per-term lower bound
  have hae1E : AEStronglyMeasurable
      (({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
        (1 : Ω → ℝ))) P :=
    (Measurable.indicator measurable_one hE).aestronglyMeasurable
  have hbdd1E : ∀ᵐ ω ∂P,
      ‖({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
        (1 : Ω → ℝ)) ω‖ ≤ (1:ℝ) := by
    filter_upwards with ω
    by_cases h : ω ∈ {ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
      ∧ ∑ j ∈ t, ξ j ω ≤ b}
    · rw [Set.indicator_of_mem h]
      simp
    · rw [Set.indicator_of_notMem h]
      simp
  have hint1E : Integrable
      (({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
        (1 : Ω → ℝ))) P :=
    Integrable.of_bound hae1E 1 hbdd1E
  have hfWae : AEStronglyMeasurable
      (fun ω => clampFun a b γ (∑ j ∈ t, ξ j ω)) P :=
    ((clampFun_measurable a b γ).comp hVmeas).aestronglyMeasurable
  have hfWbdd : ∀ᵐ ω ∂P,
      ‖(fun ω => clampFun a b γ (∑ j ∈ t, ξ j ω)) ω‖
        ≤ (b - a) / 2 + γ :=
    Filter.Eventually.of_forall (fun ω => hbdd _)
  have htermW : ∀ i ∈ t, Integrable
      (fun ω => ξ i ω * clampFun a b γ (∑ j ∈ t, ξ j ω)) P :=
    fun i hi => (hint i hi).mul_bdd hfWae hfWbdd
  have hVmeas_fun : ∀ i ∈ t, Measurable (∑ j ∈ t.erase i, ξ j) := by
    intro i _
    have hpt : Measurable (fun ω => ∑ j ∈ t.erase i, ξ j ω) :=
      Finset.measurable_sum _ (fun j _ => hmeas j)
    have heq : (∑ j ∈ t.erase i, ξ j)
        = (fun ω => ∑ j ∈ t.erase i, ξ j ω) := by
      funext ω
      exact Finset.sum_apply _ _ _
    rwa [heq]
  have htermV : ∀ i ∈ t, Integrable (fun ω => ξ i ω
      * clampFun a b γ ((∑ j ∈ t.erase i, ξ j) ω)) P := by
    intro i hi
    have hfV : AEStronglyMeasurable
        (fun ω => clampFun a b γ ((∑ j ∈ t.erase i, ξ j) ω)) P :=
      ((clampFun_measurable a b γ).comp
        (hVmeas_fun i hi)).aestronglyMeasurable
    have hbddV : ∀ᵐ ω ∂P,
        ‖(fun ω => clampFun a b γ
          ((∑ j ∈ t.erase i, ξ j) ω)) ω‖ ≤ (b - a) / 2 + γ :=
      Filter.Eventually.of_forall (fun ω => hbdd _)
    exact (hint i hi).mul_bdd hfV hbddV
  have hterm1E : ∀ i ∈ t, Integrable (fun ω =>
      ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
        (1 : Ω → ℝ)) ω * concH γ (ξ i ω)) P := by
    intro i hi
    exact Integrable.bdd_mul (hint_h i hi) hae1E hbdd1E
  have hper_le : ∀ i ∈ t,
      P[fun ω => ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
          ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator (1 : Ω → ℝ)) ω
        * concH γ (ξ i ω)]
      ≤ P[fun ω => ξ i ω * (clampFun a b γ (∑ j ∈ t, ξ j ω)
        - clampFun a b γ ((∑ j ∈ t.erase i, ξ j) ω))] := by
    intro i hi
    have hdiff_int : Integrable (fun ω => ξ i ω
        * (clampFun a b γ (∑ j ∈ t, ξ j ω)
          - clampFun a b γ ((∑ j ∈ t.erase i, ξ j) ω))) P := by
      have e : (fun ω => ξ i ω
            * (clampFun a b γ (∑ j ∈ t, ξ j ω)
              - clampFun a b γ ((∑ j ∈ t.erase i, ξ j) ω)))
          = (fun ω => ξ i ω * clampFun a b γ (∑ j ∈ t, ξ j ω))
            - (fun ω => ξ i ω
              * clampFun a b γ ((∑ j ∈ t.erase i, ξ j) ω)) := by
        funext ω
        simp only [Pi.sub_apply, mul_sub]
      rw [e]
      exact (htermW i hi).sub (htermV i hi)
    have hpt : ∀ ω, ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
          ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator (1 : Ω → ℝ)) ω
        * concH γ (ξ i ω)
        ≤ ξ i ω * (clampFun a b γ (∑ j ∈ t, ξ j ω)
          - clampFun a b γ ((∑ j ∈ t.erase i, ξ j) ω)) := by
      intro ω
      have h1 : (∑ j ∈ t.erase i, ξ j) ω
          = ∑ j ∈ t.erase i, ξ j ω :=
        Finset.sum_apply _ _ _
      have h2 : (∑ j ∈ t.erase i, ξ j ω) + ξ i ω
          = ∑ j ∈ t, ξ j ω :=
        sum_erase_add_pointwise hi ω
      have hVeq : (∑ j ∈ t.erase i, ξ j) ω
          = (∑ j ∈ t, ξ j ω) - ξ i ω := by
        rw [h1]
        linarith [h2]
      rw [hVeq]
      by_cases hmemE : ω ∈ {ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
        ∧ ∑ j ∈ t, ξ j ω ≤ b}
      · have hav : a ≤ ∑ j ∈ t, ξ j ω := hmemE.1
        have hvb : ∑ j ∈ t, ξ j ω ≤ b := hmemE.2
        rw [Set.indicator_of_mem hmemE]
        simp only [Pi.one_apply, one_mul]
        unfold concH
        rw [mul_comm]
        exact clamp_key_le a b γ _ _ hγ.le hav hvb
      · rw [Set.indicator_of_notMem hmemE]
        simp only [zero_mul]
        exact clamp_mul_nonneg a b γ _ _
    exact integral_mono (hterm1E i hi) hdiff_int hpt
  have hsum_le : ∑ i ∈ t, P[fun ω =>
      ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
        (1 : Ω → ℝ)) ω * concH γ (ξ i ω)]
      ≤ ∑ i ∈ t, P[fun ω => ξ i ω
        * (clampFun a b γ (∑ j ∈ t, ξ j ω)
          - clampFun a b γ ((∑ j ∈ t.erase i, ξ j) ω))] :=
    Finset.sum_le_sum hper_le
  have hJ_eq : ∑ i ∈ t, P[fun ω =>
      ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
        (1 : Ω → ℝ)) ω * concH γ (ξ i ω)]
      = P[fun ω => ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
          ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator (1 : Ω → ℝ)) ω
        * ∑ j ∈ t, concH γ (ξ j ω)] := by
    rw [← integral_finsetSum t (fun i hi => hterm1E i hi)]
    congr 1
    funext ω
    change (∑ i ∈ t, ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
        ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator (1 : Ω → ℝ)) ω
        * concH γ (ξ i ω))
      = ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
        (1 : Ω → ℝ)) ω * ∑ j ∈ t, concH γ (ξ j ω)
    rw [Finset.mul_sum]
  have hJ_le : P[fun ω => ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
        ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator (1 : Ω → ℝ)) ω
      * ∑ j ∈ t, concH γ (ξ j ω)]
      ≤ P[fun ω => (∑ i ∈ t, ξ i ω)
        * clampFun a b γ (∑ i ∈ t, ξ i ω)] := by
    rw [← hJ_eq, hN8]
    exact hsum_le
  -- lower bound via mean
  have hHsubc : Integrable (fun ω => (∑ j ∈ t, concH γ (ξ j ω))
      - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]) P :=
    hHint.sub (integrable_const _)
  have hintJ : Integrable (fun ω =>
      ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
        (1 : Ω → ℝ)) ω * ∑ j ∈ t, concH γ (ξ j ω)) P :=
    Integrable.bdd_mul hHint hae1E hbdd1E
  have hintC : Integrable (fun ω =>
      P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]
        * ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
          ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator (1 : Ω → ℝ)) ω) P :=
    hint1E.const_mul _
  have hintK : Integrable (fun ω =>
      ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
        (1 : Ω → ℝ)) ω * ((∑ j ∈ t, concH γ (ξ j ω))
          - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)])) P :=
    Integrable.bdd_mul hHsubc hae1E hbdd1E
  have eJK : (fun ω => ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
        ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator (1 : Ω → ℝ)) ω
        * ∑ j ∈ t, concH γ (ξ j ω)
        - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]
          * ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
            ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator (1 : Ω → ℝ)) ω)
      = (fun ω => ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
          ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator (1 : Ω → ℝ)) ω
        * ((∑ j ∈ t, concH γ (ξ j ω))
          - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)])) := by
    funext ω
    ring
  have hc1E : P[fun ω => P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]
        * ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
          (1 : Ω → ℝ)) ω]
      = P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]
        * P.real {ω | a ≤ ∑ j ∈ t, ξ j ω
          ∧ ∑ j ∈ t, ξ j ω ≤ b} := by
    rw [integral_const_mul, integral_indicator_one hE]
  have hsub := integral_sub hintJ hintC
  rw [eJK, hc1E] at hsub
  have hintN : Integrable (fun ω =>
      -|(∑ j ∈ t, concH γ (ξ j ω))
        - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]|) P :=
    (hHsubc.abs).neg
  have hK : -P[fun ω => |(∑ j ∈ t, concH γ (ξ j ω))
      - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]|]
      ≤ P[fun ω => ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
          ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator (1 : Ω → ℝ)) ω
        * ((∑ j ∈ t, concH γ (ξ j ω))
          - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)])] := by
    have hneg : P[fun ω => -|(∑ j ∈ t, concH γ (ξ j ω))
        - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]|]
        = -P[fun ω => |(∑ j ∈ t, concH γ (ξ j ω))
          - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]|] := by
      rw [integral_neg]
    rw [← hneg]
    have hpt : ∀ ω, -|(∑ j ∈ t, concH γ (ξ j ω))
        - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]|
        ≤ ({ω : Ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b}.indicator
          (1 : Ω → ℝ)) ω * ((∑ j ∈ t, concH γ (ξ j ω))
            - P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]) := by
      intro ω
      by_cases h : ω ∈ {ω : Ω | a ≤ ∑ j ∈ t, ξ j ω
        ∧ ∑ j ∈ t, ξ j ω ≤ b}
      · rw [Set.indicator_of_mem h]
        simp only [Pi.one_apply, one_mul]
        exact neg_abs_le _
      · rw [Set.indicator_of_notMem h]
        simp only [zero_mul]
        exact neg_nonpos.mpr (abs_nonneg _)
    exact integral_mono hintN hintK hpt
  have hquarter := integral_concH_ge_quarter hmem hvar_lo hγ hγ3
  have hconc := integral_abs_concH_sub_le hindep hmem hγ hγ3
  -- upper bound
  have hmem2V : MemLp (fun ω => ∑ j ∈ t, ξ j ω) 2 P :=
    memLp_finsetSum t
      (fun j hj => (hmem j hj).mono_exponent (by norm_num))
  have hVabs1 : P[fun ω => |∑ j ∈ t, ξ j ω|] ≤ 1 := by
    have h1 := integral_abs_le_sqrt_integral_sq hmem2V
    have hN7 := integral_sq_finsetSum_of_iIndepFun hindep
      (fun j hj => (hmem j hj).mono_exponent (by norm_num)) hmean
    rw [hN7] at h1
    have h3 : Real.sqrt (∑ j ∈ t, P[fun ω => (ξ j ω) ^ 2]) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hvar_hi
    exact le_trans h1 h3
  have hintAbsV : Integrable (fun ω => |∑ j ∈ t, ξ j ω|) P := by
    have h1 : MemLp (fun ω => ∑ j ∈ t, ξ j ω) 1 P :=
      hmem2V.mono_exponent (by norm_num)
    have h := h1.norm
    rw [memLp_one_iff_integrable] at h
    simpa [Real.norm_eq_abs] using h
  have hMnn : (0:ℝ) ≤ (b - a) / 2 + γ := by linarith [hab, hγ.le]
  have hupper : P[fun ω => (∑ i ∈ t, ξ i ω)
      * clampFun a b γ (∑ i ∈ t, ξ i ω)]
      ≤ (b - a) / 2 + γ := by
    have hpt : ∀ ω, (∑ i ∈ t, ξ i ω)
        * clampFun a b γ (∑ i ∈ t, ξ i ω)
        ≤ ((b - a) / 2 + γ) * |∑ i ∈ t, ξ i ω| := by
      intro ω
      calc (∑ i ∈ t, ξ i ω) * clampFun a b γ (∑ i ∈ t, ξ i ω)
          ≤ |(∑ i ∈ t, ξ i ω) * clampFun a b γ (∑ i ∈ t, ξ i ω)| :=
            le_abs_self _
        _ = |∑ i ∈ t, ξ i ω| * |clampFun a b γ (∑ i ∈ t, ξ i ω)| :=
          abs_mul _ _
        _ ≤ |∑ i ∈ t, ξ i ω| * ((b - a) / 2 + γ) :=
          mul_le_mul_of_nonneg_left
            (abs_clampFun_le a b γ hab hγ.le _) (abs_nonneg _)
        _ = ((b - a) / 2 + γ) * |∑ i ∈ t, ξ i ω| := by ring
    have hintVf : Integrable (fun ω => (∑ i ∈ t, ξ i ω)
        * clampFun a b γ (∑ i ∈ t, ξ i ω)) P := by
      have hfW : AEStronglyMeasurable
          (fun ω => clampFun a b γ (∑ i ∈ t, ξ i ω)) P :=
        ((clampFun_measurable a b γ).comp hVmeas).aestronglyMeasurable
      have hbddW : ∀ᵐ ω ∂P,
          ‖(fun ω => clampFun a b γ (∑ i ∈ t, ξ i ω)) ω‖
            ≤ (b - a) / 2 + γ :=
        Filter.Eventually.of_forall (fun ω => hbdd _)
      exact hVint.mul_bdd hfW hbddW
    have hintMV : Integrable
        (fun ω => ((b - a) / 2 + γ) * |∑ i ∈ t, ξ i ω|) P :=
      hintAbsV.const_mul _
    have hle := integral_mono hintVf hintMV hpt
    rw [integral_const_mul] at hle
    calc P[fun ω => (∑ i ∈ t, ξ i ω)
        * clampFun a b γ (∑ i ∈ t, ξ i ω)]
        ≤ ((b - a) / 2 + γ) * P[fun ω => |∑ i ∈ t, ξ i ω|] := hle
      _ ≤ ((b - a) / 2 + γ) * 1 :=
        mul_le_mul_of_nonneg_left hVabs1 hMnn
      _ = (b - a) / 2 + γ := by ring
  have hPE_nn : (0:ℝ)
      ≤ P.real {ω | a ≤ ∑ j ∈ t, ξ j ω ∧ ∑ j ∈ t, ξ j ω ≤ b} :=
    measureReal_nonneg
  have h1 : (1 / 4) * P.real {ω | a ≤ ∑ j ∈ t, ξ j ω
      ∧ ∑ j ∈ t, ξ j ω ≤ b}
      ≤ P[fun ω => ∑ j ∈ t, concH γ (ξ j ω)]
        * P.real {ω | a ≤ ∑ j ∈ t, ξ j ω
          ∧ ∑ j ∈ t, ξ j ω ≤ b} :=
    mul_le_mul_of_nonneg_right hquarter hPE_nn
  linarith [hsub, hK, hJ_le, hupper, h1, hconc]

/-- N10 corollary: window bound for leave-one-out sums. -/
private lemma measureReal_window_finsetSum_le {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hmeas : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) {t : Finset ℕ}
    (hmem : ∀ j ∈ t, MemLp (ξ j) 3 P)
    (hmean : ∀ j ∈ t, P[ξ j] = 0)
    (hvar_lo : 1 / 2 ≤ ∑ j ∈ t, P[fun ω => (ξ j ω) ^ 2])
    (hvar_hi : ∑ j ∈ t, P[fun ω => (ξ j ω) ^ 2] ≤ 1)
    {γ : ℝ} (hγ : 0 < γ)
    (hγ3 : ∑ j ∈ t, P[fun ω => |ξ j ω| ^ 3] ≤ γ)
    (z r : ℝ) (hr : 0 ≤ r) :
    P.real {ω | |(∑ j ∈ t, ξ j ω) - z| ≤ r}
      ≤ 4 * r + 8 * γ := by
  have hEq : {ω : Ω | |(∑ j ∈ t, ξ j ω) - z| ≤ r}
      = {ω : Ω | z - r ≤ ∑ j ∈ t, ξ j ω
        ∧ ∑ j ∈ t, ξ j ω ≤ z + r} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
  rw [hEq]
  have h := measureReal_Icc_finsetSum_le hmeas hindep hmem hmean
    hvar_lo hvar_hi hγ hγ3 (a := z - r) (b := z + r) (by linarith)
  have heq : (2:ℝ) * ((z + r) - (z - r)) + 8 * γ = 4 * r + 8 * γ := by
    ring
  rwa [heq] at h

/-- `P.real` is at most one on a probability space. -/
private lemma probReal_le_one' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (s : Set Ω) : P.real s ≤ 1 := by
  rw [← probReal_univ (μ := P)]
  exact measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)

/-- Difference of two numbers in `[0,1]` is at most one in absolute value. -/
private lemma abs_sub_le_one_of_unit {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : |a - b| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith

private lemma measurable_steinSolution (z : ℝ) :
    Measurable (steinSolution z) :=
  (continuous_steinSolution z).measurable

private lemma steinSolution_norm_le (z : ℝ) :
    ∀ x, ‖steinSolution z x‖ ≤ 2 := by
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (steinSolution_nonneg z x)]
  exact steinSolution_le_two z x

private lemma measurable_steinSolutionDeriv (z : ℝ) :
    Measurable (steinSolutionDeriv z) := by
  have h1 : Measurable (fun w : ℝ => w * steinSolution z w) :=
    measurable_id.mul (measurable_steinSolution z)
  have h2 : Measurable (fun w : ℝ => if w ≤ z then (1 : ℝ) else 0) := by
    have h : Measurable ((Set.Iic z).indicator (fun _ : ℝ => (1 : ℝ))) :=
      Measurable.indicator measurable_const measurableSet_Iic
    have heq : (fun w : ℝ => if w ≤ z then (1 : ℝ) else 0)
        = (Set.Iic z).indicator (fun _ : ℝ => (1 : ℝ)) := by
      funext w
      show (if w ≤ z then (1 : ℝ) else 0) = _
      by_cases hw : w ≤ z
      · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hw)]
        simp [hw]
      · rw [Set.indicator_of_notMem (fun hmem => hw (Set.mem_Iic.mp hmem))]
        simp [hw]
    rwa [heq]
  have h3 : Measurable (fun w : ℝ => w * steinSolution z w
      + (if w ≤ z then (1 : ℝ) else 0)) := h1.add h2
  have heq : steinSolutionDeriv z = (fun w : ℝ => w * steinSolution z w
      + (if w ≤ z then (1 : ℝ) else 0)) - fun _ => stdNormalCDF z := by
    funext w
    unfold steinSolutionDeriv
    simp [Pi.sub_apply]
  rw [heq]
  exact h3.sub measurable_const

private lemma steinSolutionDeriv_norm_le (z : ℝ) :
    ∀ x, ‖steinSolutionDeriv z x‖ ≤ 1 := by
  intro x
  rw [Real.norm_eq_abs]
  exact abs_steinSolutionDeriv_le_one z x

/-- Stein identity: the CDF error equals the Stein discrepancy. -/
private lemma stein_identity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hmeas : ∀ j, Measurable (ξ j))
    {t : Finset ℕ} (hmem : ∀ j ∈ t, MemLp (ξ j) 3 P) (z : ℝ) :
    P.real {ω | ∑ j ∈ t, ξ j ω ≤ z} - stdNormalCDF z
      = P[fun ω => steinSolutionDeriv z (∑ j ∈ t, ξ j ω)]
        - P[fun ω => (∑ j ∈ t, ξ j ω)
          * steinSolution z (∑ j ∈ t, ξ j ω)] := by
  have hWmeas : Measurable (fun ω => ∑ j ∈ t, ξ j ω) :=
    Finset.measurable_sum t (fun j _ => hmeas j)
  have hD : Integrable (fun ω => steinSolutionDeriv z (∑ j ∈ t, ξ j ω)) P :=
    Integrable.of_bound
      ((measurable_steinSolutionDeriv z).comp hWmeas).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => steinSolutionDeriv_norm_le z _))
  have hWint : Integrable (fun ω => ∑ j ∈ t, ξ j ω) P :=
    integrable_finsetSum t (fun j hj => by
      have h1 : MemLp (ξ j) 1 P := (hmem j hj).mono_exponent (by norm_num)
      exact memLp_one_iff_integrable.mp h1)
  have hWf : Integrable (fun ω => (∑ j ∈ t, ξ j ω)
      * steinSolution z (∑ j ∈ t, ξ j ω)) P :=
    hWint.mul_bdd ((measurable_steinSolution z).comp hWmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => steinSolution_norm_le z _))
  have hE : MeasurableSet {ω : Ω | ∑ j ∈ t, ξ j ω ≤ z} := by
    have hEq : {ω : Ω | ∑ j ∈ t, ξ j ω ≤ z}
        = (fun ω => ∑ j ∈ t, ξ j ω) ⁻¹' (Set.Iic z) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
    rw [hEq]
    exact measurableSet_Iic.preimage hWmeas
  have hbdd1 : ∀ᵐ ω ∂P, ‖({ω : Ω | ∑ j ∈ t, ξ j ω ≤ z}.indicator
      (1 : Ω → ℝ)) ω‖ ≤ (1 : ℝ) := by
    filter_upwards with ω
    by_cases h : ω ∈ {ω : Ω | ∑ j ∈ t, ξ j ω ≤ z}
    · rw [Set.indicator_of_mem h]
      simp
    · rw [Set.indicator_of_notMem h]
      simp
  have hind : Integrable ({ω : Ω | ∑ j ∈ t, ξ j ω ≤ z}.indicator
      (1 : Ω → ℝ)) P :=
    Integrable.of_bound
      (Measurable.indicator measurable_one hE).aestronglyMeasurable 1 hbdd1
  have e12 : (fun ω => steinSolutionDeriv z (∑ j ∈ t, ξ j ω)
        - (∑ j ∈ t, ξ j ω) * steinSolution z (∑ j ∈ t, ξ j ω))
        = (fun ω => ({ω : Ω | ∑ j ∈ t, ξ j ω ≤ z}.indicator
          (1 : Ω → ℝ)) ω - stdNormalCDF z) := by
    funext ω
    rw [steinSolutionDeriv_sub]
    by_cases hw : ω ∈ {ω : Ω | ∑ j ∈ t, ξ j ω ≤ z}
    · have hw' : ∑ j ∈ t, ξ j ω ≤ z := hw
      rw [Set.indicator_of_mem hw]
      simp [hw']
    · have hw' : ¬ ∑ j ∈ t, ξ j ω ≤ z := fun hle => hw hle
      rw [Set.indicator_of_notMem hw]
      simp [hw']
  have hDsub := integral_sub hD hWf
  rw [e12, integral_sub hind (integrable_const _),
    integral_indicator_one hE, integral_const, probReal_univ,
    one_smul] at hDsub
  exact hDsub

/-- N11: single-term Stein bound. -/
private lemma stein_term_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ξ V : Ω → ℝ}
    (hξmeas : Measurable ξ) (hVmeas : Measurable V)
    (hindep : ξ ⟂ᵢ[P] V) (hξmem : MemLp ξ 3 P)
    (hVint : Integrable V P)
    (hVabs : P[fun ω => |V ω|] ≤ 1)
    {z γ : ℝ} (hγ : 0 ≤ γ)
    (hwin : ∀ r : ℝ, 0 ≤ r →
      P.real {ω | |V ω - z| ≤ r} ≤ 4 * r + 8 * γ) :
    |P[fun ω => (ξ ω) ^ 2]
          * (P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
            - P[fun ω => steinSolutionDeriv z (V ω)])
        - P[fun ω => ξ ω * (steinSolution z (V ω + ξ ω)
            - steinSolution z (V ω)
            - ξ ω * steinSolutionDeriv z (V ω))]|
      ≤ 18 * P[fun ω => |ξ ω| ^ 3]
        + 24 * γ * P[fun ω => (ξ ω) ^ 2] := by
  have hξmem1 : MemLp ξ 1 P := hξmem.mono_exponent (by norm_num)
  have hξmem2 : MemLp ξ 2 P := hξmem.mono_exponent (by norm_num)
  have hξint1 : Integrable (fun ω => |ξ ω|) P := by
    have h := hξmem1.norm
    rw [memLp_one_iff_integrable] at h
    simpa [Real.norm_eq_abs] using h
  have hξint2 : Integrable (fun ω => (ξ ω) ^ 2) P := hξmem2.integrable_sq
  have hξint3 : Integrable (fun ω => |ξ ω| ^ 3) P := by
    have h3 := hξmem.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using h3
  have hVabsint : Integrable (fun ω => |V ω|) P := by
    simpa [Real.norm_eq_abs] using hVint.norm
  have hm1nn : 0 ≤ P[fun ω => |ξ ω|] :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hm2nn : 0 ≤ P[fun ω => (ξ ω) ^ 2] :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hm3nn : 0 ≤ P[fun ω => |ξ ω| ^ 3] :=
    integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) _)
  have hLyap : P[fun ω => (ξ ω) ^ 2] * P[fun ω => |ξ ω|]
      ≤ P[fun ω => |ξ ω| ^ 3] :=
    integral_sq_mul_integral_abs_le hξmem
  have hVξmeas : Measurable (fun ω => V ω + ξ ω) := hVmeas.add hξmeas
  have hgW : Integrable (fun ω => steinSolutionDeriv z (V ω + ξ ω)) P :=
    Integrable.of_bound
      ((measurable_steinSolutionDeriv z).comp hVξmeas).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => steinSolutionDeriv_norm_le z _))
  have hgV : Integrable (fun ω => steinSolutionDeriv z (V ω)) P :=
    Integrable.of_bound
      ((measurable_steinSolutionDeriv z).comp hVmeas).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => steinSolutionDeriv_norm_le z _))
  have hfade : Measurable (fun ω => |V ω - z|) :=
    continuous_abs.measurable.comp (hVmeas.sub_const z)
  have hgade : Measurable (fun ω => |ξ ω|) :=
    continuous_abs.measurable.comp hξmeas
  have hS : MeasurableSet {ω | |V ω - z| ≤ |ξ ω|} :=
    measurableSet_le hfade hgade
  have hind : AEStronglyMeasurable
      (fun ω => (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) P := by
    have h : Measurable ({ω | |V ω - z| ≤ |ξ ω|}.indicator
        (fun _ : Ω => (1 : ℝ))) :=
      Measurable.indicator measurable_const hS
    exact h.aestronglyMeasurable
  have hbddI : ∀ᵐ ω ∂P,
      ‖(fun ω => (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) ω‖ ≤ 1 := by
    filter_upwards with ω
    by_cases h : |V ω - z| ≤ |ξ ω| <;> simp [h]
  have hWind : Integrable
      (fun ω => (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) P :=
    Integrable.of_bound hind 1 hbddI
  have hprod_int : ∀ k : ℕ, Integrable (fun ω => |ξ ω| ^ k) P →
      Integrable (fun ω => |V ω| * |ξ ω| ^ k) P := fun k hk => by
    have hφ : Measurable (fun x : ℝ => |x| ^ k) :=
      continuous_abs.measurable.pow_const k
    have hψ : Measurable (fun x : ℝ => |x|) := continuous_abs.measurable
    have hcomp := (hindep.comp hφ hψ).symm
    have hX : Integrable ((fun x : ℝ => |x|) ∘ V) P := hVabsint
    have hY : Integrable ((fun x : ℝ => |x| ^ k) ∘ ξ) P := hk
    exact hcomp.integrable_mul hX hY
  have hprod_eq : ∀ k : ℕ, P[fun ω => |V ω| * |ξ ω| ^ k]
      = P[fun ω => |V ω|] * P[fun ω => |ξ ω| ^ k] := fun k => by
    have hφ : Measurable (fun x : ℝ => |x| ^ k) :=
      continuous_abs.measurable.pow_const k
    have hψ : Measurable (fun x : ℝ => |x|) := continuous_abs.measurable
    have hcomp := (hindep.comp hφ hψ).symm
    have hX : AEStronglyMeasurable (fun ω => |V ω|) P :=
      (hψ.comp hVmeas).aestronglyMeasurable
    have hY : AEStronglyMeasurable (fun ω => |ξ ω| ^ k) P :=
      (hφ.comp hξmeas).aestronglyMeasurable
    exact hcomp.integral_fun_mul_eq_mul_integral hX hY
  have hVξ1_int : Integrable (fun ω => |V ω| * |ξ ω|) P := by
    have hk1 : Integrable (fun ω => |ξ ω| ^ 1) P := by
      simpa using hξint1
    have h := hprod_int 1 hk1
    simpa using h
  have hVξ1_eq : P[fun ω => |V ω| * |ξ ω|]
      = P[fun ω => |V ω|] * P[fun ω => |ξ ω|] := by
    have h := hprod_eq 1
    simpa using h
  have hVξ3_int : Integrable (fun ω => |V ω| * |ξ ω| ^ 3) P :=
    hprod_int 3 hξint3
  have hVξ3_eq : P[fun ω => |V ω| * |ξ ω| ^ 3]
      = P[fun ω => |V ω|] * P[fun ω => |ξ ω| ^ 3] := hprod_eq 3
  have hk0 : Integrable (fun ω => |ξ ω| ^ 0) P := by
    simp
  have hk1 : Integrable (fun ω => |ξ ω| ^ (0 + 1)) P := by
    simpa using hξint1
  have hk2 : Integrable (fun ω => |ξ ω| ^ 2) P := by
    simpa using hξint2
  have hk3 : Integrable (fun ω => |ξ ω| ^ (2 + 1)) P := by
    simpa using hξint3
  have hBnn : 0 ≤ 8 * γ := mul_nonneg (by norm_num) hγ
  have hW0raw := integral_pow_mul_window_le (ξ := ξ) (V := V)
    (z := z) (A := 4) (B := 8 * γ) (k := 0) hξmeas hVmeas hindep
    (by norm_num) hBnn hwin hk0 hk1
  have hW2raw := integral_pow_mul_window_le (ξ := ξ) (V := V)
    (z := z) (A := 4) (B := 8 * γ) (k := 2) hξmeas hVmeas hindep
    (by norm_num) hBnn hwin hk2 hk3
  have hPow0 : P[fun ω => |ξ ω| ^ 0] = 1 := by
    have e : (fun ω => |ξ ω| ^ 0) = (fun _ => (1 : ℝ)) := by
      funext ω
      simp
    rw [e, integral_const, probReal_univ, one_smul]
  have hW0 : P[fun ω => (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)]
      ≤ 4 * P[fun ω => |ξ ω|] + 8 * γ := by
    have eL : (fun ω => |ξ ω| ^ 0
          * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0))
        = (fun ω => (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) := by
      funext ω
      simp
    have eR1 : (fun ω => |ξ ω| ^ (0 + 1)) = (fun ω => |ξ ω|) := by
      funext ω
      simp
    rw [eL, eR1, hPow0, mul_one] at hW0raw
    exact hW0raw
  have hW2 : P[fun ω => |ξ ω| ^ 2
        * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)]
      ≤ 4 * P[fun ω => |ξ ω| ^ 3]
        + 8 * γ * P[fun ω => (ξ ω) ^ 2] := by
    have eR1 : (fun ω => |ξ ω| ^ (2 + 1)) = (fun ω => |ξ ω| ^ 3) := rfl
    have eR2 : (fun ω => |ξ ω| ^ 2) = (fun ω => (ξ ω) ^ 2) := by
      funext ω
      exact sq_abs _
    rw [eR1, eR2] at hW2raw
    exact hW2raw
  have hpt1 : ∀ ω, |steinSolutionDeriv z (V ω + ξ ω)
        - steinSolutionDeriv z (V ω)|
      ≤ (|V ω| + 2) * |ξ ω| + steinWindow (V ω) (ξ ω) z :=
    fun ω => steinSolutionDeriv_sub_le z (V ω) (ξ ω)
  have heb1 : (fun ω => (|V ω| + 2) * |ξ ω| + steinWindow (V ω) (ξ ω) z)
      = (fun ω => (|V ω| * |ξ ω| + 2 * |ξ ω|)
        + (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) := by
    funext ω
    unfold steinWindow
    ring
  have h12 : Integrable (fun ω => |V ω| * |ξ ω| + 2 * |ξ ω|) P :=
    hVξ1_int.add (hξint1.const_mul 2)
  have hbound1_int : Integrable (fun ω => (|V ω| + 2) * |ξ ω|
      + steinWindow (V ω) (ξ ω) z) P := by
    rw [heb1]
    exact h12.add hWind
  have hdiff_int : Integrable (fun ω => steinSolutionDeriv z (V ω + ξ ω)
      - steinSolutionDeriv z (V ω)) P := hgW.sub hgV
  have hdiff_abs_int : Integrable (fun ω => |steinSolutionDeriv z (V ω + ξ ω)
      - steinSolutionDeriv z (V ω)|) P := by
    simpa [Real.norm_eq_abs] using hdiff_int.norm
  have h1mono : P[fun ω => |steinSolutionDeriv z (V ω + ξ ω)
        - steinSolutionDeriv z (V ω)|]
      ≤ P[fun ω => (|V ω| + 2) * |ξ ω| + steinWindow (V ω) (ξ ω) z] :=
    integral_mono hdiff_abs_int hbound1_int hpt1
  have hbound1_eq : P[fun ω => (|V ω| + 2) * |ξ ω|
        + steinWindow (V ω) (ξ ω) z]
      = P[fun ω => |V ω| * |ξ ω|] + 2 * P[fun ω => |ξ ω|]
        + P[fun ω => (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)] := by
    rw [heb1, integral_add h12 hWind,
      integral_add hVξ1_int (hξint1.const_mul 2), integral_const_mul]
  have hVξ1_le : P[fun ω => |V ω| * |ξ ω|]
      ≤ P[fun ω => |ξ ω|] := by
    rw [hVξ1_eq]
    have h := mul_le_mul_of_nonneg_right hVabs hm1nn
    rwa [one_mul] at h
  have hsub_eq : P[fun ω => steinSolutionDeriv z (V ω + ξ ω)
        - steinSolutionDeriv z (V ω)]
      = P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
        - P[fun ω => steinSolutionDeriv z (V ω)] :=
    integral_sub hgW hgV
  have h1abs : |P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
        - P[fun ω => steinSolutionDeriv z (V ω)]|
      ≤ P[fun ω => |steinSolutionDeriv z (V ω + ξ ω)
        - steinSolutionDeriv z (V ω)|] := by
    rw [← hsub_eq]
    have h := norm_integral_le_integral_norm
      (fun ω => steinSolutionDeriv z (V ω + ξ ω)
        - steinSolutionDeriv z (V ω)) (μ := P)
    simpa [Real.norm_eq_abs] using h
  have h1main : |P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
        - P[fun ω => steinSolutionDeriv z (V ω)]|
      ≤ 7 * P[fun ω => |ξ ω|] + 8 * γ := by
    have h1 := h1abs
    have h2 := h1mono
    have h3 := hbound1_eq
    have h4 := hVξ1_le
    have h5 := hW0
    linarith
  have hA : |P[fun ω => (ξ ω) ^ 2]
        * (P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
          - P[fun ω => steinSolutionDeriv z (V ω)])|
      ≤ 7 * P[fun ω => |ξ ω| ^ 3]
        + 8 * γ * P[fun ω => (ξ ω) ^ 2] := by
    have e : |P[fun ω => (ξ ω) ^ 2]
          * (P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
            - P[fun ω => steinSolutionDeriv z (V ω)])|
        = P[fun ω => (ξ ω) ^ 2]
          * |P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
            - P[fun ω => steinSolutionDeriv z (V ω)]| := by
      rw [abs_mul, abs_of_nonneg hm2nn]
    rw [e]
    have hle : P[fun ω => (ξ ω) ^ 2]
          * |P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
            - P[fun ω => steinSolutionDeriv z (V ω)]|
        ≤ P[fun ω => (ξ ω) ^ 2] * (7 * P[fun ω => |ξ ω|] + 8 * γ) :=
      mul_le_mul_of_nonneg_left h1main hm2nn
    have hLy : P[fun ω => (ξ ω) ^ 2] * (7 * P[fun ω => |ξ ω|] + 8 * γ)
        ≤ 7 * P[fun ω => |ξ ω| ^ 3]
          + 8 * γ * P[fun ω => (ξ ω) ^ 2] := by
      calc P[fun ω => (ξ ω) ^ 2] * (7 * P[fun ω => |ξ ω|] + 8 * γ)
          = 7 * (P[fun ω => (ξ ω) ^ 2] * P[fun ω => |ξ ω|])
            + 8 * γ * P[fun ω => (ξ ω) ^ 2] := by ring
        _ ≤ 7 * P[fun ω => |ξ ω| ^ 3]
            + 8 * γ * P[fun ω => (ξ ω) ^ 2] := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hLyap (by norm_num)) (le_refl _)
    exact le_trans hle hLy
  have hξ2W_int : Integrable (fun ω => |ξ ω| ^ 2
      * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) P :=
    hk2.mul_bdd hind hbddI
  have hpt2 : ∀ ω, |ξ ω * (steinSolution z (V ω + ξ ω)
          - steinSolution z (V ω)
          - ξ ω * steinSolutionDeriv z (V ω))|
      ≤ |V ω| * |ξ ω| ^ 3 + 2 * |ξ ω| ^ 3
        + 2 * (|ξ ω| ^ 2
          * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) := fun ω => by
    have hT := steinSolution_taylor_le z (V ω) (ξ ω)
    have eW : steinWindow (V ω) (ξ ω) z
        = (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0) := rfl
    rw [abs_mul]
    have hle : |ξ ω|
          * |steinSolution z (V ω + ξ ω) - steinSolution z (V ω)
            - ξ ω * steinSolutionDeriv z (V ω)|
          ≤ |ξ ω| * (((|V ω| + 2) * (ξ ω) ^ 2
            + 2 * |ξ ω| * steinWindow (V ω) (ξ ω) z)) :=
      mul_le_mul_of_nonneg_left hT (abs_nonneg _)
    rw [eW] at hle
    have hsq : (ξ ω) ^ 2 = |ξ ω| ^ 2 := (sq_abs _).symm
    have eEq : |ξ ω| * (((|V ω| + 2) * (ξ ω) ^ 2
          + 2 * |ξ ω| * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)))
        = |V ω| * |ξ ω| ^ 3 + 2 * |ξ ω| ^ 3
          + 2 * (|ξ ω| ^ 2
            * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)) := by
      rw [hsq]
      ring
    rw [eEq] at hle
    exact hle
  have hbound2_int : Integrable (fun ω => |V ω| * |ξ ω| ^ 3 + 2 * |ξ ω| ^ 3
      + 2 * (|ξ ω| ^ 2
        * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0))) P := by
    have h1 : Integrable
        (fun ω => |V ω| * |ξ ω| ^ 3 + 2 * |ξ ω| ^ 3) P :=
      hVξ3_int.add (hξint3.const_mul 2)
    have h2 : Integrable (fun ω => 2 * (|ξ ω| ^ 2
        * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0))) P :=
      hξ2W_int.const_mul 2
    exact h1.add h2
  have hξD_meas : Measurable (fun ω => ξ ω * (steinSolution z (V ω + ξ ω)
      - steinSolution z (V ω) - ξ ω * steinSolutionDeriv z (V ω))) := by
    have hfW : Measurable (fun ω => steinSolution z (V ω + ξ ω)) :=
      (measurable_steinSolution z).comp hVξmeas
    have hfV : Measurable (fun ω => steinSolution z (V ω)) :=
      (measurable_steinSolution z).comp hVmeas
    have hgV : Measurable (fun ω => steinSolutionDeriv z (V ω)) :=
      (measurable_steinSolutionDeriv z).comp hVmeas
    have hξg : Measurable
        (fun ω => ξ ω * steinSolutionDeriv z (V ω)) :=
      hξmeas.mul hgV
    have hD : Measurable (fun ω => steinSolution z (V ω + ξ ω)
        - steinSolution z (V ω) - ξ ω * steinSolutionDeriv z (V ω)) :=
      (hfW.sub hfV).sub hξg
    exact hξmeas.mul hD
  have hξD_abs_aesm : AEStronglyMeasurable (fun ω => |ξ ω *
      (steinSolution z (V ω + ξ ω) - steinSolution z (V ω)
        - ξ ω * steinSolutionDeriv z (V ω))|) P :=
    (continuous_abs.measurable.comp hξD_meas).aestronglyMeasurable
  have hξD_abs_int : Integrable (fun ω => |ξ ω *
      (steinSolution z (V ω + ξ ω) - steinSolution z (V ω)
        - ξ ω * steinSolutionDeriv z (V ω))|) P :=
    hbound2_int.mono_nonneg hξD_abs_aesm
      (Filter.Eventually.of_forall (fun ω => abs_nonneg _))
      (Filter.Eventually.of_forall (fun ω => hpt2 ω))
  have h2mono : P[fun ω => |ξ ω * (steinSolution z (V ω + ξ ω)
          - steinSolution z (V ω)
          - ξ ω * steinSolutionDeriv z (V ω))|]
      ≤ P[fun ω => |V ω| * |ξ ω| ^ 3 + 2 * |ξ ω| ^ 3
        + 2 * (|ξ ω| ^ 2
          * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0))] :=
    integral_mono hξD_abs_int hbound2_int hpt2
  have hbound2_eq : P[fun ω => |V ω| * |ξ ω| ^ 3 + 2 * |ξ ω| ^ 3
        + 2 * (|ξ ω| ^ 2
          * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0))]
      = P[fun ω => |V ω| * |ξ ω| ^ 3] + 2 * P[fun ω => |ξ ω| ^ 3]
        + 2 * P[fun ω => |ξ ω| ^ 2
          * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0)] := by
    have h1 : Integrable
        (fun ω => |V ω| * |ξ ω| ^ 3 + 2 * |ξ ω| ^ 3) P :=
      hVξ3_int.add (hξint3.const_mul 2)
    have h2 : Integrable (fun ω => 2 * (|ξ ω| ^ 2
        * (if |V ω - z| ≤ |ξ ω| then (1 : ℝ) else 0))) P :=
      hξ2W_int.const_mul 2
    rw [integral_add h1 h2,
      integral_add hVξ3_int (hξint3.const_mul 2),
      integral_const_mul, integral_const_mul]
  have hVξ3_le : P[fun ω => |V ω| * |ξ ω| ^ 3]
      ≤ P[fun ω => |ξ ω| ^ 3] := by
    rw [hVξ3_eq]
    have h := mul_le_mul_of_nonneg_right hVabs hm3nn
    rwa [one_mul] at h
  have h2abs : |P[fun ω => ξ ω * (steinSolution z (V ω + ξ ω)
          - steinSolution z (V ω)
          - ξ ω * steinSolutionDeriv z (V ω))]|
      ≤ P[fun ω => |ξ ω * (steinSolution z (V ω + ξ ω)
        - steinSolution z (V ω)
        - ξ ω * steinSolutionDeriv z (V ω))|] := by
    have h := norm_integral_le_integral_norm
      (fun ω => ξ ω * (steinSolution z (V ω + ξ ω)
        - steinSolution z (V ω)
        - ξ ω * steinSolutionDeriv z (V ω))) (μ := P)
    simpa [Real.norm_eq_abs] using h
  have hB : |P[fun ω => ξ ω * (steinSolution z (V ω + ξ ω)
          - steinSolution z (V ω)
          - ξ ω * steinSolutionDeriv z (V ω))]|
      ≤ 11 * P[fun ω => |ξ ω| ^ 3]
        + 16 * γ * P[fun ω => (ξ ω) ^ 2] := by
    have h1 := h2abs
    have h2 := h2mono
    have h3 := hbound2_eq
    have h4 := hVξ3_le
    have h5 := hW2
    linarith
  have htri : |P[fun ω => (ξ ω) ^ 2]
        * (P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
          - P[fun ω => steinSolutionDeriv z (V ω)])
        - P[fun ω => ξ ω * (steinSolution z (V ω + ξ ω)
          - steinSolution z (V ω)
          - ξ ω * steinSolutionDeriv z (V ω))]|
      ≤ |P[fun ω => (ξ ω) ^ 2]
          * (P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
            - P[fun ω => steinSolutionDeriv z (V ω)])|
        + |P[fun ω => ξ ω * (steinSolution z (V ω + ξ ω)
          - steinSolution z (V ω)
          - ξ ω * steinSolutionDeriv z (V ω))]| := by
    have h := abs_add_le
      (P[fun ω => (ξ ω) ^ 2]
        * (P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
          - P[fun ω => steinSolutionDeriv z (V ω)]))
      (-P[fun ω => ξ ω * (steinSolution z (V ω + ξ ω)
        - steinSolution z (V ω) - ξ ω * steinSolutionDeriv z (V ω))])
    rwa [← sub_eq_add_neg, abs_neg] at h
  calc |P[fun ω => (ξ ω) ^ 2]
        * (P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
          - P[fun ω => steinSolutionDeriv z (V ω)])
        - P[fun ω => ξ ω * (steinSolution z (V ω + ξ ω)
          - steinSolution z (V ω)
          - ξ ω * steinSolutionDeriv z (V ω))]|
      ≤ |P[fun ω => (ξ ω) ^ 2]
          * (P[fun ω => steinSolutionDeriv z (V ω + ξ ω)]
            - P[fun ω => steinSolutionDeriv z (V ω)])|
        + |P[fun ω => ξ ω * (steinSolution z (V ω + ξ ω)
          - steinSolution z (V ω)
          - ξ ω * steinSolutionDeriv z (V ω))]| := htri
    _ ≤ (7 * P[fun ω => |ξ ω| ^ 3] + 8 * γ * P[fun ω => (ξ ω) ^ 2])
        + (11 * P[fun ω => |ξ ω| ^ 3]
          + 16 * γ * P[fun ω => (ξ ω) ^ 2]) :=
        add_le_add hA hB
    _ = 18 * P[fun ω => |ξ ω| ^ 3]
        + 24 * γ * P[fun ω => (ξ ω) ^ 2] := by ring

/-- Single-term Stein identity for leave-one-out. -/
private lemma stein_leaveOneOut_term_eq {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hmeas : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) {s : Finset ℕ}
    (hmem : ∀ j ∈ s, MemLp (ξ j) 3 P)
    {i : ℕ} (hi : i ∈ s) (z : ℝ) :
    P[fun ω => (ξ i ω) ^ 2]
        * (P[fun ω => steinSolutionDeriv z
          ((∑ j ∈ s.erase i, ξ j ω) + ξ i ω)]
          - P[fun ω => steinSolutionDeriv z
            (∑ j ∈ s.erase i, ξ j ω)])
        - P[fun ω => ξ i ω * (steinSolution z
          ((∑ j ∈ s.erase i, ξ j ω) + ξ i ω)
          - steinSolution z (∑ j ∈ s.erase i, ξ j ω)
          - ξ i ω * steinSolutionDeriv z
            (∑ j ∈ s.erase i, ξ j ω))]
      = P[fun ω => (ξ i ω) ^ 2]
        * P[fun ω => steinSolutionDeriv z (∑ j ∈ s, ξ j ω)]
        - P[fun ω => ξ i ω * (steinSolution z (∑ j ∈ s, ξ j ω)
          - steinSolution z (∑ j ∈ s.erase i, ξ j ω))] := by
  have hWmeas : Measurable (fun ω => ∑ j ∈ s, ξ j ω) :=
    Finset.measurable_sum s (fun j _ => hmeas j)
  have hVmeas : Measurable
      (fun ω => ∑ j ∈ s.erase i, ξ j ω) :=
    Finset.measurable_sum _ (fun j _ => hmeas j)
  have hW : ∀ ω, (∑ j ∈ s.erase i, ξ j ω) + ξ i ω
      = ∑ j ∈ s, ξ j ω := by
    intro ω
    have h := Finset.add_sum_erase s (fun j => ξ j ω) hi
    calc (∑ j ∈ s.erase i, ξ j ω) + ξ i ω
        = ξ i ω + (∑ j ∈ s.erase i, ξ j ω) := by ring
      _ = ∑ j ∈ s, ξ j ω := h
  have hξmem1 : MemLp (ξ i) 1 P :=
    (hmem i hi).mono_exponent (by norm_num)
  have hξint : Integrable (ξ i) P :=
    memLp_one_iff_integrable.mp hξmem1
  have hfWae : AEStronglyMeasurable
      (fun ω => steinSolution z (∑ j ∈ s, ξ j ω)) P :=
    ((measurable_steinSolution z).comp hWmeas).aestronglyMeasurable
  have hfWbd : ∀ᵐ ω ∂P,
      ‖(fun ω => steinSolution z (∑ j ∈ s, ξ j ω)) ω‖ ≤ 2 :=
    Filter.Eventually.of_forall
      (fun ω => steinSolution_norm_le z _)
  have hξfW : Integrable
      (fun ω => ξ i ω * steinSolution z (∑ j ∈ s, ξ j ω)) P :=
    hξint.mul_bdd hfWae hfWbd
  have hfVae : AEStronglyMeasurable
      (fun ω => steinSolution z
        (∑ j ∈ s.erase i, ξ j ω)) P :=
    ((measurable_steinSolution z).comp hVmeas).aestronglyMeasurable
  have hfVbd : ∀ᵐ ω ∂P,
      ‖(fun ω => steinSolution z
        (∑ j ∈ s.erase i, ξ j ω)) ω‖ ≤ 2 :=
    Filter.Eventually.of_forall
      (fun ω => steinSolution_norm_le z _)
  have hξfV : Integrable
      (fun ω => ξ i ω * steinSolution z
        (∑ j ∈ s.erase i, ξ j ω)) P :=
    hξint.mul_bdd hfVae hfVbd
  have hA : Integrable (fun ω => ξ i ω * (steinSolution z
      (∑ j ∈ s, ξ j ω)
      - steinSolution z (∑ j ∈ s.erase i, ξ j ω))) P := by
    have e : (fun ω => ξ i ω * (steinSolution z (∑ j ∈ s, ξ j ω)
        - steinSolution z (∑ j ∈ s.erase i, ξ j ω)))
        = (fun ω => ξ i ω * steinSolution z (∑ j ∈ s, ξ j ω)
          - ξ i ω * steinSolution z
            (∑ j ∈ s.erase i, ξ j ω)) := by
      funext ω
      rw [mul_sub]
    rw [e]
    exact hξfW.sub hξfV
  have hξmem2 : MemLp (ξ i) 2 P :=
    (hmem i hi).mono_exponent (by norm_num)
  have hξsq : Integrable (fun ω => (ξ i ω) ^ 2) P :=
    hξmem2.integrable_sq
  have hgVae : AEStronglyMeasurable
      (fun ω => steinSolutionDeriv z
        (∑ j ∈ s.erase i, ξ j ω)) P :=
    ((measurable_steinSolutionDeriv z).comp
      hVmeas).aestronglyMeasurable
  have hgVbd : ∀ᵐ ω ∂P,
      ‖(fun ω => steinSolutionDeriv z
        (∑ j ∈ s.erase i, ξ j ω)) ω‖ ≤ 1 :=
    Filter.Eventually.of_forall
      (fun ω => steinSolutionDeriv_norm_le z _)
  have hB : Integrable (fun ω => (ξ i ω) ^ 2
      * steinSolutionDeriv z (∑ j ∈ s.erase i, ξ j ω)) P :=
    hξsq.mul_bdd hgVae hgVbd
  have hindep_fun : (∑ j ∈ s.erase i, ξ j) ⟂ᵢ[P] (ξ i) :=
    hindep.indepFun_finsetSum_of_notMem hmeas
      (Finset.notMem_erase i s)
  have heq_fun : (∑ j ∈ s.erase i, ξ j)
      = (fun ω => ∑ j ∈ s.erase i, ξ j ω) := by
    funext ω
    exact Finset.sum_apply _ _ _
  have hindep_iV : (ξ i) ⟂ᵢ[P]
      (fun ω => ∑ j ∈ s.erase i, ξ j ω) := by
    have h := hindep_fun.symm
    rwa [heq_fun] at h
  have hφ : Measurable (fun x : ℝ => x ^ 2) :=
    measurable_id.pow_const 2
  have hψ : Measurable (steinSolutionDeriv z) :=
    measurable_steinSolutionDeriv z
  have hcomp := hindep_iV.comp hφ hψ
  have hX : AEStronglyMeasurable
      ((fun x : ℝ => x ^ 2) ∘ ξ i) P :=
    (hφ.comp (hmeas i)).aestronglyMeasurable
  have hY : AEStronglyMeasurable
      (steinSolutionDeriv z ∘
        (fun ω => ∑ j ∈ s.erase i, ξ j ω)) P :=
    (hψ.comp hVmeas).aestronglyMeasurable
  have hfact := IndepFun.integral_fun_mul_eq_mul_integral
    hcomp hX hY
  have hBeq : P[fun ω => (ξ i ω) ^ 2
      * steinSolutionDeriv z (∑ j ∈ s.erase i, ξ j ω)]
      = P[fun ω => (ξ i ω) ^ 2]
        * P[fun ω => steinSolutionDeriv z
          (∑ j ∈ s.erase i, ξ j ω)] := by
    have e1 : (fun ω => ((fun x : ℝ => x ^ 2) ∘ ξ i) ω
        * (steinSolutionDeriv z ∘
          (fun ω => ∑ j ∈ s.erase i, ξ j ω)) ω)
        = (fun ω => (ξ i ω) ^ 2
          * steinSolutionDeriv z
            (∑ j ∈ s.erase i, ξ j ω)) := by
      funext ω
      simp only [Function.comp_def]
    have e2 : ((fun x : ℝ => x ^ 2) ∘ ξ i)
        = (fun ω => (ξ i ω) ^ 2) := by
      funext ω
      simp only [Function.comp_def]
    have e3 : (steinSolutionDeriv z ∘
        (fun ω => ∑ j ∈ s.erase i, ξ j ω))
        = (fun ω => steinSolutionDeriv z
          (∑ j ∈ s.erase i, ξ j ω)) := rfl
    rw [e1, e2, e3] at hfact
    exact hfact
  have hCeq : P[fun ω => ξ i ω * (steinSolution z
      ((∑ j ∈ s.erase i, ξ j ω) + ξ i ω)
      - steinSolution z (∑ j ∈ s.erase i, ξ j ω)
      - ξ i ω * steinSolutionDeriv z
        (∑ j ∈ s.erase i, ξ j ω))]
      = P[fun ω => ξ i ω * (steinSolution z (∑ j ∈ s, ξ j ω)
        - steinSolution z (∑ j ∈ s.erase i, ξ j ω))]
        - P[fun ω => (ξ i ω) ^ 2
          * steinSolutionDeriv z
            (∑ j ∈ s.erase i, ξ j ω)] := by
    have eC : (fun ω => ξ i ω * (steinSolution z
        ((∑ j ∈ s.erase i, ξ j ω) + ξ i ω)
        - steinSolution z (∑ j ∈ s.erase i, ξ j ω)
        - ξ i ω * steinSolutionDeriv z
          (∑ j ∈ s.erase i, ξ j ω)))
        = (fun ω => (ξ i ω * (steinSolution z (∑ j ∈ s, ξ j ω)
          - steinSolution z (∑ j ∈ s.erase i, ξ j ω)))
          - ((ξ i ω) ^ 2 * steinSolutionDeriv z
            (∑ j ∈ s.erase i, ξ j ω))) := by
      funext ω
      rw [hW ω]
      ring
    rw [eC, integral_sub hA hB]
  have eDf : (fun ω => steinSolutionDeriv z
      ((∑ j ∈ s.erase i, ξ j ω) + ξ i ω))
      = (fun ω => steinSolutionDeriv z
        (∑ j ∈ s, ξ j ω)) := by
    funext ω
    rw [hW ω]
  rw [eDf, hCeq, hBeq]
  ring

/-- Inner Berry–Esseen bound for `0 < γ ≤ 1/8`. -/
private lemma berry_esseen_finsetSum_pos {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hmeas : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) {s : Finset ℕ}
    (hmem : ∀ j ∈ s, MemLp (ξ j) 3 P)
    (hmean : ∀ j ∈ s, P[ξ j] = 0)
    (hvar : ∑ j ∈ s, P[fun ω => (ξ j ω) ^ 2] = 1)
    {γ : ℝ} (hγpos : 0 < γ) (hγle : γ ≤ 1 / 8)
    (hγ3 : ∑ j ∈ s, P[fun ω => |ξ j ω| ^ 3] ≤ γ)
    (z : ℝ) :
    |P.real {ω | ∑ j ∈ s, ξ j ω ≤ z} - stdNormalCDF z|
      ≤ 42 * γ := by
  set T : ℕ → ℝ := fun i => P[fun ω => (ξ i ω) ^ 2]
    * (P[fun ω => steinSolutionDeriv z
      ((∑ j ∈ s.erase i, ξ j ω) + ξ i ω)]
      - P[fun ω => steinSolutionDeriv z
        (∑ j ∈ s.erase i, ξ j ω)])
    - P[fun ω => ξ i ω * (steinSolution z
      ((∑ j ∈ s.erase i, ξ j ω) + ξ i ω)
      - steinSolution z (∑ j ∈ s.erase i, ξ j ω)
      - ξ i ω * steinSolutionDeriv z
        (∑ j ∈ s.erase i, ξ j ω))]
  have hTi : ∀ i ∈ s, |T i|
      ≤ 18 * P[fun ω => |ξ i ω| ^ 3]
        + 24 * γ * P[fun ω => (ξ i ω) ^ 2] := by
    intro i hi
    have h3nn : ∀ j ∈ s,
        0 ≤ P[fun ω => |ξ j ω| ^ 3] := by
      intro j _
      exact integral_nonneg
        (fun ω => pow_nonneg (abs_nonneg _) _)
    have h3i : P[fun ω => |ξ i ω| ^ 3] ≤ γ := by
      have h := Finset.single_le_sum (s := s)
        (f := fun j => P[fun ω => |ξ j ω| ^ 3]) h3nn hi
      exact le_trans h hγ3
    have hsq_bound : P[fun ω => (ξ i ω) ^ 2]
        ≤ 1 / 4 + 2 * P[fun ω => |ξ i ω| ^ 3] :=
      integral_sq_le_quarter_add (hmem i hi)
    have hsq_half : P[fun ω => (ξ i ω) ^ 2] ≤ 1 / 2 := by
      linarith [hsq_bound, h3i, hγle]
    have h2nn : ∀ j ∈ s,
        0 ≤ P[fun ω => (ξ j ω) ^ 2] := by
      intro j _
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hsum_erase : ∑ j ∈ s.erase i,
        P[fun ω => (ξ j ω) ^ 2]
        = 1 - P[fun ω => (ξ i ω) ^ 2] := by
      have h := Finset.sum_erase_eq_sub (s := s)
        (f := fun j => P[fun ω => (ξ j ω) ^ 2]) hi
      rw [hvar] at h
      exact h
    have hvar_lo : 1 / 2
        ≤ ∑ j ∈ s.erase i, P[fun ω => (ξ j ω) ^ 2] := by
      rw [hsum_erase]
      linarith [hsq_half]
    have hvar_hi : ∑ j ∈ s.erase i,
        P[fun ω => (ξ j ω) ^ 2] ≤ 1 := by
      rw [hsum_erase]
      have hnn := h2nn i hi
      linarith
    have hγ3_erase : ∑ j ∈ s.erase i,
        P[fun ω => |ξ j ω| ^ 3] ≤ γ := by
      have hsub : s.erase i ⊆ s :=
        Finset.erase_subset i s
      have hle : ∑ j ∈ s.erase i,
          P[fun ω => |ξ j ω| ^ 3]
          ≤ ∑ j ∈ s, P[fun ω => |ξ j ω| ^ 3] :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro j _ _
          exact integral_nonneg
            (fun ω => pow_nonneg (abs_nonneg _) _))
      exact le_trans hle hγ3
    have hmem_erase : ∀ j ∈ s.erase i,
        MemLp (ξ j) 3 P :=
      fun j hj => hmem j (Finset.mem_of_mem_erase hj)
    have hmean_erase : ∀ j ∈ s.erase i, P[ξ j] = 0 :=
      fun j hj => hmean j (Finset.mem_of_mem_erase hj)
    have hwin : ∀ r : ℝ, 0 ≤ r →
        P.real {ω | |(∑ j ∈ s.erase i, ξ j ω) - z| ≤ r}
          ≤ 4 * r + 8 * γ :=
      fun r hr => measureReal_window_finsetSum_le hmeas
        hindep hmem_erase hmean_erase hvar_lo hvar_hi
        hγpos hγ3_erase z r hr
    have hmem2_erase : ∀ j ∈ s.erase i,
        MemLp (ξ j) 2 P := by
      intro j hj
      exact (hmem j (Finset.mem_of_mem_erase hj)).mono_exponent
        (by norm_num)
    have hVmem2 : MemLp
        (fun ω => ∑ j ∈ s.erase i, ξ j ω) 2 P :=
      memLp_finsetSum _ hmem2_erase
    have hVabs1 : P[fun ω => |∑ j ∈ s.erase i, ξ j ω|]
        ≤ Real.sqrt
          (P[fun ω => (∑ j ∈ s.erase i, ξ j ω) ^ 2]) :=
      integral_abs_le_sqrt_integral_sq hVmem2
    have hN7 : P[fun ω => (∑ j ∈ s.erase i, ξ j ω) ^ 2]
        = ∑ j ∈ s.erase i, P[fun ω => (ξ j ω) ^ 2] :=
      integral_sq_finsetSum_of_iIndepFun hindep
        hmem2_erase hmean_erase
    have hVsq_le : P[fun ω =>
        (∑ j ∈ s.erase i, ξ j ω) ^ 2] ≤ 1 := by
      rw [hN7]
      exact hvar_hi
    have hVabs : P[fun ω =>
        |∑ j ∈ s.erase i, ξ j ω|] ≤ 1 := by
      have hsqrt : Real.sqrt
          (P[fun ω => (∑ j ∈ s.erase i, ξ j ω) ^ 2])
          ≤ 1 :=
        Real.sqrt_le_one.mpr hVsq_le
      exact le_trans hVabs1 hsqrt
    have hVmeas : Measurable
        (fun ω => ∑ j ∈ s.erase i, ξ j ω) :=
      Finset.measurable_sum _ (fun j _ => hmeas j)
    have hint1 : ∀ j ∈ s.erase i,
        Integrable (ξ j) P := by
      intro j hj
      have h1 : MemLp (ξ j) 1 P :=
        (hmem j (Finset.mem_of_mem_erase hj)).mono_exponent
          (by norm_num)
      exact memLp_one_iff_integrable.mp h1
    have hVint : Integrable
        (fun ω => ∑ j ∈ s.erase i, ξ j ω) P :=
      integrable_finsetSum _ hint1
    have hindep_fun : (∑ j ∈ s.erase i, ξ j) ⟂ᵢ[P]
        (ξ i) :=
      hindep.indepFun_finsetSum_of_notMem hmeas
        (Finset.notMem_erase i s)
    have heq_fun : (∑ j ∈ s.erase i, ξ j)
        = (fun ω => ∑ j ∈ s.erase i, ξ j ω) := by
      funext ω
      exact Finset.sum_apply _ _ _
    have hindep_iV : (ξ i) ⟂ᵢ[P]
        (fun ω => ∑ j ∈ s.erase i, ξ j ω) := by
      have h := hindep_fun.symm
      rwa [heq_fun] at h
    exact stein_term_bound (hmeas i) hVmeas hindep_iV
      (hmem i hi) hVint hVabs hγpos.le hwin
  have hint : ∀ i ∈ s, Integrable (ξ i) P := by
    intro i hi
    have h1 : MemLp (ξ i) 1 P :=
      (hmem i hi).mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp h1
  have hN8 := integral_sum_mul_eq_sum_leaveOneOut hmeas
    hindep hint hmean (measurable_steinSolution z)
    (steinSolution_norm_le z)
  have hN8pt : P[fun ω => (∑ i ∈ s, ξ i ω)
      * steinSolution z (∑ i ∈ s, ξ i ω)]
      = ∑ i ∈ s, P[fun ω => ξ i ω * (steinSolution z
        (∑ j ∈ s, ξ j ω)
        - steinSolution z (∑ j ∈ s.erase i, ξ j ω))] := by
    have h := hN8
    simpa only [Finset.sum_apply] using h
  have hED : P[fun ω => steinSolutionDeriv z
      (∑ j ∈ s, ξ j ω)]
      = ∑ i ∈ s, P[fun ω => (ξ i ω) ^ 2]
        * P[fun ω => steinSolutionDeriv z
          (∑ j ∈ s, ξ j ω)] := by
    calc (P[fun ω => steinSolutionDeriv z
        (∑ j ∈ s, ξ j ω)] : ℝ)
        = 1 * P[fun ω => steinSolutionDeriv z
          (∑ j ∈ s, ξ j ω)] := by rw [one_mul]
      _ = (∑ i ∈ s, P[fun ω => (ξ i ω) ^ 2])
          * P[fun ω => steinSolutionDeriv z
            (∑ j ∈ s, ξ j ω)] := by rw [hvar]
      _ = ∑ i ∈ s, P[fun ω => (ξ i ω) ^ 2]
          * P[fun ω => steinSolutionDeriv z
            (∑ j ∈ s, ξ j ω)] := by rw [Finset.sum_mul]
  have hdecomp : P.real {ω | ∑ j ∈ s, ξ j ω ≤ z}
      - stdNormalCDF z
      = ∑ i ∈ s, T i := by
    have hstein := stein_identity hmeas hmem z
    have hsum : ∑ i ∈ s, T i
        = (∑ i ∈ s, P[fun ω => (ξ i ω) ^ 2]
          * P[fun ω => steinSolutionDeriv z
            (∑ j ∈ s, ξ j ω)])
          - (∑ i ∈ s, P[fun ω => ξ i ω * (steinSolution z
            (∑ j ∈ s, ξ j ω)
            - steinSolution z
              (∑ j ∈ s.erase i, ξ j ω))]) := by
      have hcongr : ∀ i ∈ s, T i
          = P[fun ω => (ξ i ω) ^ 2]
            * P[fun ω => steinSolutionDeriv z
              (∑ j ∈ s, ξ j ω)]
            - P[fun ω => ξ i ω * (steinSolution z
              (∑ j ∈ s, ξ j ω)
              - steinSolution z
                (∑ j ∈ s.erase i, ξ j ω))] :=
        fun i hi => stein_leaveOneOut_term_eq hmeas
          hindep hmem hi z
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl hcongr
    rw [hsum, ← hED, ← hN8pt]
    exact hstein
  calc |P.real {ω | ∑ j ∈ s, ξ j ω ≤ z} - stdNormalCDF z|
      = |∑ i ∈ s, T i| := by rw [hdecomp]
    _ ≤ ∑ i ∈ s, |T i| :=
        Finset.abs_sum_le_sum_abs T s
    _ ≤ ∑ i ∈ s, (18 * P[fun ω => |ξ i ω| ^ 3]
        + 24 * γ * P[fun ω => (ξ i ω) ^ 2]) :=
        Finset.sum_le_sum (fun i hi => hTi i hi)
    _ = 18 * (∑ i ∈ s, P[fun ω => |ξ i ω| ^ 3])
        + 24 * γ * (∑ i ∈ s,
          P[fun ω => (ξ i ω) ^ 2]) := by
        rw [Finset.sum_add_distrib]
        have h1 : ∑ i ∈ s, 18 * P[fun ω => |ξ i ω| ^ 3]
            = 18 * ∑ i ∈ s, P[fun ω => |ξ i ω| ^ 3] :=
          (Finset.mul_sum _ _ _).symm
        have h2 : ∑ i ∈ s, 24 * γ * P[fun ω => (ξ i ω) ^ 2]
            = 24 * γ * ∑ i ∈ s,
              P[fun ω => (ξ i ω) ^ 2] :=
          (Finset.mul_sum _ _ _).symm
        rw [h1, h2]
    _ ≤ 18 * γ + 24 * γ * 1 := by
        have h1 : 18 * (∑ i ∈ s, P[fun ω => |ξ i ω| ^ 3])
            ≤ 18 * γ :=
          mul_le_mul_of_nonneg_left hγ3 (by norm_num)
        have h2 : 24 * γ * (∑ i ∈ s,
            P[fun ω => (ξ i ω) ^ 2])
            = 24 * γ * 1 := by
          rw [hvar]
        rw [h2]
        exact add_le_add h1 (le_refl _)
    _ = 42 * γ := by ring

/-- N12: Berry–Esseen bound for normalized independent sums. -/
private lemma berry_esseen_finsetSum {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hmeas : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) {s : Finset ℕ}
    (hmem : ∀ j ∈ s, MemLp (ξ j) 3 P)
    (hmean : ∀ j ∈ s, P[ξ j] = 0)
    (hvar : ∑ j ∈ s, P[fun ω => (ξ j ω) ^ 2] = 1)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hγ3 : ∑ j ∈ s, P[fun ω => |ξ j ω| ^ 3] ≤ γ)
    (z : ℝ) :
    |P.real {ω | ∑ j ∈ s, ξ j ω ≤ z} - stdNormalCDF z|
      ≤ 42 * γ := by
  by_cases hbig : 1 / 8 < γ
  · have hP0 : 0 ≤ P.real {ω | ∑ j ∈ s, ξ j ω ≤ z} := measureReal_nonneg
    have hP1 : P.real {ω | ∑ j ∈ s, ξ j ω ≤ z} ≤ 1 := measureReal_le_one
    have hΦ0 : 0 ≤ stdNormalCDF z := stdNormalCDF_nonneg z
    have hΦ1 : stdNormalCDF z ≤ 1 := stdNormalCDF_le_one z
    rw [abs_sub_le_iff]
    constructor <;> linarith
  · push Not at hbig
    by_cases hpos : 0 < γ
    · exact berry_esseen_finsetSum_pos hmeas hindep hmem hmean hvar
        hpos hbig hγ3 z
    · push Not at hpos
      have hγ0 : γ = 0 := le_antisymm hpos hγ
      subst hγ0
      apply le_of_forall_pos_le_add
      intro ε hε
      set γ' : ℝ := min (ε / 42) (1 / 8) with hγ'def
      have hγ'pos : 0 < γ' := by
        rw [hγ'def]
        exact lt_min (by linarith) (by norm_num)
      have hγ'le : γ' ≤ 1 / 8 := by
        rw [hγ'def]
        exact min_le_right _ _
      have hγ'sum : ∑ j ∈ s, P[fun ω => |ξ j ω| ^ 3] ≤ γ' := by
        have hle : (0 : ℝ) ≤ γ' := le_of_lt hγ'pos
        exact le_trans hγ3 hle
      have hbound := berry_esseen_finsetSum_pos hmeas hindep
        hmem hmean hvar hγ'pos hγ'le hγ'sum z
      have h42 : 42 * γ' ≤ ε := by
        have hle : γ' ≤ ε / 42 := by
          rw [hγ'def]
          exact min_le_left _ _
        linarith
      calc |P.real {ω | ∑ j ∈ s, ξ j ω ≤ z} - stdNormalCDF z|
          ≤ 42 * γ' := hbound
        _ ≤ ε := h42
        _ = 42 * 0 + ε := by ring

/-- **Berry–Esseen bound for finite sums.** Let $(\xi_j)_{j \in \mathbb{N}}$ be measurable, mutually
independent real random variables on a probability space, and let $s$ be a finite set of indices
such that for each $j \in s$ the variable $\xi_j$ has a finite third moment and mean
$\mathbb{E}[\xi_j] = 0$, and such that $\sum_{j \in s} \mathbb{E}[\xi_j^2] = 1$. Write $\Phi$
for the distribution function of the standard normal distribution. If $\gamma \ge 0$ is a real
number with $\sum_{j \in s} \mathbb{E}|\xi_j|^3 \le \gamma$, then for every real $z$,
$$\left|\mathbb{P}\left(\sum_{j \in s} \xi_j \le z\right) - \Phi(z)\right| \le 42\gamma.$$ -/
theorem berry_esseen_finsetSum_gaussian {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hmeas : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) {s : Finset ℕ}
    (hmem : ∀ j ∈ s, MemLp (ξ j) 3 P)
    (hmean : ∀ j ∈ s, P[ξ j] = 0)
    (hvar : ∑ j ∈ s, P[fun ω => (ξ j ω) ^ 2] = 1)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hγ3 : ∑ j ∈ s, P[fun ω => |ξ j ω| ^ 3] ≤ γ)
    (z : ℝ) :
    |P.real {ω | ∑ j ∈ s, ξ j ω ≤ z} - (gaussianReal 0 1).real (Iic z)|
      ≤ 42 * γ := by
  have h := berry_esseen_finsetSum hmeas hindep hmem hmean hvar hγ hγ3 z
  rwa [show stdNormalCDF z = (gaussianReal 0 1).real (Iic z) from rfl] at h

/-- **Berry–Esseen theorem with constant 42.** Let $X_0, X_1, X_2, \dots$ be measurable, mutually
independent real random variables on a probability space, each with the same distribution as
$X_0$, where $X_0$ has a finite third moment, mean $\mathbb{E}[X_0] = 0$ and variance
$\sigma^2 = \operatorname{Var}(X_0) > 0$ with $\sigma > 0$. Write $\rho = \mathbb{E}|X_0|^3$,
$S_n = X_0 + \dots + X_{n-1}$, and $\Phi$ for the distribution function of the standard normal
distribution. Then for every $n \ge 1$ and every real $x$,
$$\left|\mathbb{P}\left(\frac{S_n}{\sqrt{n\sigma^2}} \le x\right) - \Phi(x)\right| \le
\frac{42\rho}{\sigma^3\sqrt{n}}.$$

Integrability of $X_0$ is not assumed separately, since on a probability space it follows from
the finite third moment. -/
theorem berry_esseen_explicit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hXmeas : ∀ n, Measurable (X n))
    (hXindep : iIndepFun X P)
    (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hXmem : MemLp (X 0) 3 P)
    (hXmean : P[X 0] = 0)
    (hXvar : 0 < Var[X 0; P])
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    |((P.map (fun ω => (∑ i ∈ range n, X i ω) / Real.sqrt (n * Var[X 0; P]))).real (Iic x)
      - (gaussianReal 0 1).real (Iic x))|
      ≤ 42 * (P[fun ω => |X 0 ω| ^ 3])
        / (Real.sqrt (Var[X 0; P]) ^ 3 * Real.sqrt (n : ℝ)) := by
  have _hXint : Integrable (X 0) P := hXmem.integrable (by norm_num)
  set σ2 : ℝ := Var[X 0; P] with hσ2def
  set ρ : ℝ := P[fun ω => |X 0 ω| ^ 3] with hρdef
  set c : ℝ := Real.sqrt ((n : ℝ) * σ2) with hcdef
  set γ : ℝ := ρ / (Real.sqrt σ2 ^ 3 * Real.sqrt (n : ℝ)) with hγdef
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hσ2pos : 0 < σ2 := hXvar
  have hnσ2pos : (0 : ℝ) < (n : ℝ) * σ2 := mul_pos hnR hσ2pos
  have hcpos : 0 < c := Real.sqrt_pos.mpr hnσ2pos
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcsq : c ^ 2 = (n : ℝ) * σ2 := Real.sq_sqrt (le_of_lt hnσ2pos)
  have hX0mem2 : MemLp (X 0) 2 P := hXmem.mono_exponent (by norm_num)
  have hX0sq : P[fun ω => (X 0 ω) ^ 2] = σ2 := by
    have hsub := variance_eq_sub hX0mem2
    rw [hXmean] at hsub
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero] at hsub
    have e : ((X 0) ^ 2) = (fun ω => (X 0 ω) ^ 2) := by
      funext ω
      simp only [Pi.pow_apply]
    rw [e] at hsub
    exact hsub.symm.trans hσ2def.symm
  have hXjmem3 : ∀ j, MemLp (X j) 3 P :=
    fun j => (hXid j).memLp_iff.mpr hXmem
  have hXjmean : ∀ j, P[X j] = 0 := fun j => by
    have heq : P[X j] = P[X 0] := (hXid j).integral_eq
    rw [hXmean] at heq
    exact heq
  have hXjsq : ∀ j, P[fun ω => (X j ω) ^ 2] = σ2 := fun j => by
    have heq : P[fun ω => (X j ω) ^ 2] = P[fun ω => (X 0 ω) ^ 2] :=
      (hXid j).sq.integral_eq
    rw [heq]
    exact hX0sq
  have hXjabs3 : ∀ j, P[fun ω => |X j ω| ^ 3] = ρ := fun j => by
    have hu : Measurable (fun x : ℝ => |x| ^ 3) :=
      continuous_abs.measurable.pow_const 3
    have heq : P[fun ω => |X j ω| ^ 3] = P[fun ω => |X 0 ω| ^ 3] :=
      ((hXid j).comp hu).integral_eq
    rw [heq]
  have hξmeas : ∀ j, Measurable ((fun i ω => X i ω / c) j) := fun j =>
    (hXmeas j).div_const c
  have hξindep : iIndepFun (fun i ω => X i ω / c) P :=
    hXindep.comp (fun _ x => x / c)
      (fun _ => measurable_id.div_const c)
  have hξmem : ∀ j ∈ Finset.range n,
      MemLp ((fun i ω => X i ω / c) j) 3 P := fun j _ => by
    have h := hXjmem3 j
    have e : (fun ω => X j ω / c) = (fun ω => c⁻¹ * X j ω) := by
      funext ω
      rw [div_eq_inv_mul]
    have h2 : MemLp (fun ω => X j ω / c) 3 P := by
      rw [e]
      exact h.const_mul _
    exact h2
  have hξmean : ∀ j ∈ Finset.range n,
      P[(fun i ω => X i ω / c) j] = 0 := fun j _ => by
    have h1 : MemLp (X j) 1 P := (hXjmem3 j).mono_exponent (by norm_num)
    have e : (fun ω => X j ω / c) = (fun ω => c⁻¹ * X j ω) := by
      funext ω
      rw [div_eq_inv_mul]
    have h2 : P[fun ω => X j ω / c] = 0 := by
      rw [e, integral_const_mul, hXjmean j, mul_zero]
    exact h2
  have hξsq : ∀ j, P[fun ω => (X j ω / c) ^ 2] = σ2 / c ^ 2 := fun j => by
    have hXjint2 : Integrable (fun ω => (X j ω) ^ 2) P :=
      ((hXjmem3 j).mono_exponent (by norm_num)).integrable_sq
    have e : (fun ω => (X j ω / c) ^ 2)
        = (fun ω => (c ^ 2)⁻¹ * (X j ω) ^ 2) := by
      funext ω
      rw [div_pow, div_eq_inv_mul]
    rw [e, integral_const_mul, hXjsq j, div_eq_inv_mul]
  have hξabs3 : ∀ j, P[fun ω => |X j ω / c| ^ 3] = ρ / c ^ 3 := fun j => by
    have hXjint3 : Integrable (fun ω => |X j ω| ^ 3) P := by
      have h3 := (hXjmem3 j).integrable_norm_rpow (by norm_num) (by norm_num)
      simpa using h3
    have e : (fun ω => |X j ω / c| ^ 3)
        = (fun ω => (c ^ 3)⁻¹ * |X j ω| ^ 3) := by
      funext ω
      rw [abs_div, abs_of_pos hcpos, div_pow, div_eq_inv_mul]
    rw [e, integral_const_mul, hXjabs3 j, div_eq_inv_mul]
  have hvar_sum : ∑ j ∈ Finset.range n,
      P[fun ω => ((fun i ω => X i ω / c) j ω) ^ 2] = 1 := by
    have heach : ∀ j ∈ Finset.range n,
        P[fun ω => ((fun i ω => X i ω / c) j ω) ^ 2] = σ2 / c ^ 2 :=
      fun j _ => hξsq j
    rw [Finset.sum_congr rfl heach, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, hcsq]
    have hne : (n : ℝ) * σ2 ≠ 0 := ne_of_gt hnσ2pos
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hσ2ne : σ2 ≠ 0 := ne_of_gt hσ2pos
    field_simp
  have hγnonneg : 0 ≤ γ := by
    have hρnn : 0 ≤ ρ := by
      have h : 0 ≤ P[fun ω => |X 0 ω| ^ 3] :=
        integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) _)
      exact hρdef ▸ h
    have hDpos : 0 < Real.sqrt σ2 ^ 3 * Real.sqrt (n : ℝ) :=
      mul_pos (pow_pos (Real.sqrt_pos.mpr hσ2pos) 3)
        (Real.sqrt_pos.mpr hnR)
    rw [hγdef]
    exact div_nonneg hρnn (le_of_lt hDpos)
  have hγ3_sum : ∑ j ∈ Finset.range n,
      P[fun ω => |((fun i ω => X i ω / c) j ω)| ^ 3] ≤ γ := by
    have heach : ∀ j ∈ Finset.range n,
        P[fun ω => |((fun i ω => X i ω / c) j ω)| ^ 3] = ρ / c ^ 3 :=
      fun j _ => hξabs3 j
    have hsum_eq : ∑ j ∈ Finset.range n,
          P[fun ω => |((fun i ω => X i ω / c) j ω)| ^ 3]
        = (n : ℝ) * (ρ / c ^ 3) := by
      rw [Finset.sum_congr rfl heach, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
    have hc_eq : c = Real.sqrt (n : ℝ) * Real.sqrt σ2 := by
      rw [hcdef]
      exact Real.sqrt_mul (Nat.cast_nonneg n) σ2
    have hnsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    have hnsq3 : (Real.sqrt (n : ℝ)) ^ 3
        = (n : ℝ) * Real.sqrt (n : ℝ) := by
      have e : (Real.sqrt (n : ℝ)) ^ 3
          = (Real.sqrt (n : ℝ)) ^ 2 * Real.sqrt (n : ℝ) := by ring
      rw [e, hnsq]
    have hc3 : c ^ 3
        = (n : ℝ) * Real.sqrt (n : ℝ) * (Real.sqrt σ2 ^ 3) := by
      rw [hc_eq, mul_pow, hnsq3]
    have hmain_eq : (n : ℝ) * (ρ / c ^ 3) = γ := by
      rw [hγdef, hc3]
      have h1 : Real.sqrt (n : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr hnR)
      have h2 : Real.sqrt σ2 ^ 3 ≠ 0 :=
        pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr hσ2pos))
      have h3 : (n : ℝ) ≠ 0 := ne_of_gt hnR
      field_simp
    exact le_of_eq (hsum_eq.trans hmain_eq)
  have hSeq : (fun ω => (∑ i ∈ Finset.range n, X i ω) / c)
      = (fun ω => ∑ j ∈ Finset.range n, X j ω / c) := by
    funext ω
    exact Finset.sum_div _ _ _
  have hWmeas : Measurable (fun ω => ∑ j ∈ Finset.range n, X j ω / c) :=
    Finset.measurable_sum _ (fun j _ => (hXmeas j).div_const c)
  have hmap : (P.map (fun ω => (∑ i ∈ Finset.range n, X i ω) / c)).real
        (Iic x)
      = P.real {ω | ∑ j ∈ Finset.range n, X j ω / c ≤ x} := by
    rw [hSeq, map_measureReal_apply hWmeas measurableSet_Iic]
    congr 1
  have hmain := berry_esseen_finsetSum_gaussian (ξ := fun i ω => X i ω / c)
    (s := Finset.range n) (γ := γ) hξmeas hξindep hξmem hξmean hvar_sum
    hγnonneg hγ3_sum x
  rw [hmap]
  rw [hγdef, ← mul_div_assoc] at hmain
  exact hmain

/-- **Berry–Esseen theorem.** There is a constant $C > 0$ with the following property. Let
$X_0, X_1, X_2, \dots$ be measurable, mutually independent real random variables on a probability
space, each with the same distribution as $X_0$, where $X_0$ is integrable and has a finite third
moment, mean $\mathbb{E}[X_0] = 0$ and variance $\sigma^2 = \operatorname{Var}(X_0) > 0$ with
$\sigma > 0$. Write $\rho = \mathbb{E}|X_0|^3$, $S_n = X_0 + \dots + X_{n-1}$, and $\Phi$ for the
distribution function of the standard normal distribution. Then for every $n \ge 1$ and every
real $x$,
$$\left|\mathbb{P}\left(\frac{S_n}{\sqrt{n\sigma^2}} \le x\right) - \Phi(x)\right| \le
\frac{C\rho}{\sigma^3\sqrt{n}}.$$

Source: A. C. Berry, Trans. AMS 49 (1941), 122-136, DOI 10.2307/1990053; and C.-G. Esseen, Arkiv för
Matematik, Astronomi och Fysik 28A no. 9 (1942), 1-19.
-/
theorem berry_esseen
    : ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (X : ℕ → Ω → ℝ),
        (∀ n, Measurable (X n)) →
        iIndepFun X P →
        (∀ i, IdentDistrib (X i) (X 0) P P) →
        Integrable (X 0) P →
        MemLp (X 0) 3 P →
        P[X 0] = 0 →
        0 < Var[X 0; P] →
        ∀ (n : ℕ), 0 < n →
          ∀ x : ℝ,
            |((P.map (fun ω => (∑ i ∈ range n, X i ω) / Real.sqrt (n * Var[X 0; P]))).real (Iic x)
              - (gaussianReal 0 1).real (Iic x))|
            ≤ C * (P[fun ω => |X 0 ω| ^ 3]) / (Real.sqrt (Var[X 0; P]) ^ 3 * Real.sqrt (n : ℝ))
    := by
  refine ⟨42, by norm_num, ?_⟩
  intro Ω _ P _ X hXmeas hXindep hXid _ hXmem hXmean hXvar n hn x
  exact berry_esseen_explicit X hXmeas hXindep hXid hXmem hXmean hXvar n hn x

end MathlibExt.Probability.BerryEsseenWanted
end
