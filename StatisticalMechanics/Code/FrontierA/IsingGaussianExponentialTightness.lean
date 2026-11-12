/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianMomentDeterminacy
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.ContinuousMap.Bounded.Normed










open Filter MeasureTheory Set Topology

namespace StatMech.FrontierA

open ProbabilityTheory


noncomputable def truncatedExpAbs (a : Real) (n : Nat) :
    BoundedContinuousFunction Real Real where
  toFun x := min (Real.exp (a * |x|)) n
  continuous_toFun := by fun_prop
  map_bounded' := by
    refine ⟨2 * n, ?_⟩
    intro x y
    rw [Real.dist_eq]
    have hx : 0 <= min (Real.exp (a * |x|)) n :=
      le_min (Real.exp_pos _).le (Nat.cast_nonneg n)
    have hy : 0 <= min (Real.exp (a * |y|)) n :=
      le_min (Real.exp_pos _).le (Nat.cast_nonneg n)
    have hxn : min (Real.exp (a * |x|)) n <= n := min_le_right _ _
    have hyn : min (Real.exp (a * |y|)) n <= n := min_le_right _ _
    rw [abs_le]
    constructor <;> linarith

theorem truncatedExpAbs_nonneg (a : Real) (n : Nat) (x : Real) :
    0 <= truncatedExpAbs a n x := by
  exact le_min (Real.exp_pos _).le (Nat.cast_nonneg n)

theorem truncatedExpAbs_le_exp (a : Real) (n : Nat) (x : Real) :
    truncatedExpAbs a n x <= Real.exp (a * |x|) :=
  min_le_left _ _

theorem truncatedExpAbs_mono (a : Real) :
    Monotone (fun n : Nat => (truncatedExpAbs a n : Real -> Real)) := by
  intro m n hmn x
  exact min_le_min_left _ (Nat.cast_le.mpr hmn)

theorem iSup_ofReal_truncatedExpAbs (a x : Real) :
    (⨆ n : Nat, ENNReal.ofReal (truncatedExpAbs a n x)) =
      ENNReal.ofReal (Real.exp (a * |x|)) := by
  apply le_antisymm
  · exact iSup_le fun n => ENNReal.ofReal_le_ofReal
      (truncatedExpAbs_le_exp a n x)
  · obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (a * |x|))
    apply le_iSup_of_le n
    change ENNReal.ofReal (min (Real.exp (a * |x|)) n) >= _
    rw [min_eq_left hn.le]


theorem integrable_exp_abs_of_weakLimit_uniform
    (muN : Nat -> ProbabilityMeasure Real) (mu : ProbabilityMeasure Real)
    (hlim : Tendsto muN atTop (nhds mu))
    (a C : Real)
    (hint : forall n, Integrable (fun x : Real => Real.exp (a * |x|))
      (muN n : Measure Real))
    (hbound : forall n,
      (∫ x, Real.exp (a * |x|) ∂(muN n : Measure Real)) <= C) :
    Integrable (fun x : Real => Real.exp (a * |x|))
      (mu : Measure Real) := by
  have htruncBound (n : Nat) :
      (∫ x, truncatedExpAbs a n x ∂(mu : Measure Real)) <= C := by
    have hconv :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim)
        (truncatedExpAbs a n)
    apply le_of_tendsto hconv
    filter_upwards with k
    exact (integral_mono (BoundedContinuousFunction.integrable _ _)
      (hint k) (truncatedExpAbs_le_exp a n)).trans (hbound k)
  have htruncLIntegral (n : Nat) :
      (∫⁻ x, ENNReal.ofReal (truncatedExpAbs a n x)
          ∂(mu : Measure Real)) <= ENNReal.ofReal C := by
    have hintTrunc : Integrable (truncatedExpAbs a n) (mu : Measure Real) :=
      BoundedContinuousFunction.integrable _ _
    have htop :
        (∫⁻ x, ENNReal.ofReal (truncatedExpAbs a n x)
            ∂(mu : Measure Real)) ≠ ⊤ := by
      have hfinite := hintTrunc.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_norm] at hfinite
      apply ne_of_lt
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (truncatedExpAbs_nonneg a n _)] using hfinite
    have heq := integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (truncatedExpAbs_nonneg a n))
      hintTrunc.aestronglyMeasurable
    calc
      (∫⁻ x, ENNReal.ofReal (truncatedExpAbs a n x)
          ∂(mu : Measure Real)) =
          ENNReal.ofReal
            ((∫⁻ x, ENNReal.ofReal (truncatedExpAbs a n x)
              ∂(mu : Measure Real)).toReal) :=
        (ENNReal.ofReal_toReal htop).symm
      _ = ENNReal.ofReal
          (∫ x, truncatedExpAbs a n x ∂(mu : Measure Real)) := by
        rw [heq]
      _ <= ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (htruncBound n)
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hlintegral :
      (∫⁻ x, ENNReal.ofReal (Real.exp (a * |x|))
          ∂(mu : Measure Real)) <= ENNReal.ofReal C := by
    calc
      (∫⁻ x, ENNReal.ofReal (Real.exp (a * |x|))
          ∂(mu : Measure Real)) =
          ∫⁻ x, ⨆ n : Nat, ENNReal.ofReal (truncatedExpAbs a n x)
            ∂(mu : Measure Real) := by
        apply lintegral_congr
        intro x
        exact (iSup_ofReal_truncatedExpAbs a x).symm
      _ = ⨆ n : Nat,
          ∫⁻ x, ENNReal.ofReal (truncatedExpAbs a n x)
            ∂(mu : Measure Real) := by
        apply lintegral_iSup
        · intro n
          exact (truncatedExpAbs a n).continuous.measurable.ennreal_ofReal
        · intro m n hmn x
          exact ENNReal.ofReal_le_ofReal
            (truncatedExpAbs_mono a hmn x)
      _ <= ENNReal.ofReal C := iSup_le htruncLIntegral
  have hnorm :
      (∫⁻ x, ENNReal.ofReal ‖Real.exp (a * |x|)‖
          ∂(mu : Measure Real)) <= ENNReal.ofReal C := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hlintegral
  exact hnorm.trans_lt ENNReal.ofReal_lt_top


theorem zero_mem_interior_integrableExpSet_of_weakLimit_uniform
    (muN : Nat -> ProbabilityMeasure Real) (mu : ProbabilityMeasure Real)
    (hlim : Tendsto muN atTop (nhds mu))
    (a C : Real) (ha : 0 < a)
    (hint : forall n, Integrable (fun x : Real => Real.exp (a * |x|))
      (muN n : Measure Real))
    (hbound : forall n,
      (∫ x, Real.exp (a * |x|) ∂(muN n : Measure Real)) <= C) :
    (0 : Real) ∈ interior (integrableExpSet id (mu : Measure Real)) := by
  have habs := integrable_exp_abs_of_weakLimit_uniform
    muN mu hlim a C hint hbound
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
  exact habs.mono (by fun_prop)
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hdom x)

end StatMech.FrontierA
