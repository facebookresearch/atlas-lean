/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianContinuousModification
import Code.SLE.Defs
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure









open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace StatMech.SLE




theorem brownianCoordinateProcess_tendstoInMeasure
    {s : Nat -> Real} {t : Real} (hs : Tendsto s atTop (nhds t)) :
    TendstoInMeasure brownianProductLaw
      (fun n omega => brownianCoordinateProcess (s n) omega) atTop
      (brownianCoordinateProcess t) := by
  apply tendstoInMeasure_of_ne_top
  intro epsilon hepsilon hepsilonTop
  have hed : Tendsto (fun n => edist (s n) t) atTop (nhds 0) := by
    have hp := hs.prodMk_nhds (tendsto_const_nhds :
      Tendsto (fun _ : Nat => t) atTop (nhds t))
    simpa using (continuous_edist.tendsto (t, t)).comp hp
  have hrpow : Tendsto (fun n => edist (s n) t ^ (2 : Real))
      atTop (nhds 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (2 : Real))).tendsto 0
    simpa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : Real) < 2)] using h.comp hed
  have hupper : Tendsto (fun n =>
      ((3 : ENNReal) * edist (s n) t ^ (2 : Real)) /
        epsilon ^ (4 : Nat)) atTop (nhds 0) := by
    have hmul := ENNReal.Tendsto.const_mul hrpow
      (Or.inr (by norm_num : (3 : ENNReal) ≠ ⊤))
    have hinv : (epsilon ^ (4 : Nat))⁻¹ ≠ (⊤ : ENNReal) :=
      ENNReal.inv_ne_top.mpr (pow_ne_zero _ hepsilon.ne')
    have h := ENNReal.Tendsto.mul_const hmul (Or.inr hinv)
    simpa [div_eq_mul_inv] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun _ => bot_le)
    (fun n => brownianCoordinateProcess_measure_edist_ge_le
      (s n) t epsilon hepsilon.ne' hepsilonTop)


theorem tendsto_brownianDyadicApproxPoint (N : Nat) {t : Real}
    (htLower : -(N : Real) <= t) :
    Tendsto (fun n => brownianDyadicApproxPoint N n t) atTop (nhds t) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hpow : Tendsto (fun n => (1 / 256 : Real) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hevent : ∀ᶠ n in atTop, (1 / 256 : Real) ^ n < epsilon :=
    (tendsto_order.1 hpow).2 epsilon hepsilon
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨n0, hn0⟩ := hevent
  refine ⟨n0, fun n hn => ?_⟩
  calc
    dist (brownianDyadicApproxPoint N n t) t <
        ((brownianDyadicDenominator n : Nat) : Real)⁻¹ :=
      dist_brownianDyadicApproxPoint_lt_mesh N n htLower
    _ = (1 / 256 : Real) ^ n := by
      simp [brownianDyadicDenominator, inv_pow]
    _ < epsilon := hn0 n hn



theorem brownianContinuousModification_ae_eq (t : Real) :
    brownianContinuousModification t =ᵐ[brownianProductLaw]
      brownianCoordinateProcess t := by
  let N := brownianCompactRadius t
  let f : Nat -> (Real -> Real) -> Real := fun n omega =>
    brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega
  have htLower : -(N : Real) <= t := neg_brownianCompactRadius_le t
  have htUpper : t <= N := le_brownianCompactRadius t
  have htime : Tendsto (fun n => brownianDyadicApproxPoint N n t)
      atTop (nhds t) := tendsto_brownianDyadicApproxPoint N htLower
  have hcoord : TendstoInMeasure brownianProductLaw f atTop
      (brownianCoordinateProcess t) := by
    exact brownianCoordinateProcess_tendstoInMeasure htime
  have haeLimit : ∀ᵐ omega ∂brownianProductLaw,
      Tendsto (fun n => f n omega) atTop
        (nhds (brownianDyadicLimit N t omega)) := by
    filter_upwards [brownianCoordinateProcess_ae_eventually_dyadicEdge_lt N]
      with omega homega
    exact tendsto_brownianCoordinateProcess_brownianDyadicApproxPoint
      omega N htLower htUpper homega
  have hlimit : TendstoInMeasure brownianProductLaw f atTop
      (brownianDyadicLimit N t) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (brownianCoordinateProcess_measurable
        (brownianDyadicApproxPoint N n t)).aestronglyMeasurable
    · exact haeLimit
  have heq : brownianCoordinateProcess t =ᵐ[brownianProductLaw]
      brownianDyadicLimit N t := tendstoInMeasure_ae_unique hcoord hlimit
  change brownianDyadicLimit N t =ᵐ[brownianProductLaw]
    brownianCoordinateProcess t
  exact heq.symm

theorem brownianContinuousModification_measurable (t : Real) :
    Measurable (brownianContinuousModification t) := by
  unfold brownianContinuousModification brownianDyadicLimit
  apply StronglyMeasurable.measurable
  exact StronglyMeasurable.limUnder (fun n =>
    (brownianCoordinateProcess_measurable
      (brownianDyadicApproxPoint (brownianCompactRadius t) n t)).stronglyMeasurable)

theorem brownianContinuousModification_start :
    ∀ᵐ omega ∂brownianProductLaw,
      brownianContinuousModification 0 omega = 0 := by
  filter_upwards [brownianContinuousModification_ae_eq 0,
    brownianCoordinateProcess_start] with omega heq hzero
  exact heq.trans hzero

theorem brownianContinuousModification_continuous_paths :
    ∀ᵐ omega ∂brownianProductLaw,
      Continuous (fun t => brownianContinuousModification t omega) := by
  filter_upwards [brownianCoordinateProcess_ae_forall_eventually_dyadicEdge_lt]
    with omega hgood
  exact continuous_brownianContinuousModification omega hgood

theorem brownianContinuousModification_isGaussianProcess :
    IsGaussianProcess brownianContinuousModification brownianProductLaw := by
  apply brownianCoordinateProcess_isGaussianProcess.congr
  intro t
  exact (brownianContinuousModification_ae_eq t).symm

theorem brownianContinuousModification_increment_law
    (s t : Real) (hst : s <= t) :
    HasLaw (fun omega =>
      brownianContinuousModification t omega -
        brownianContinuousModification s omega)
      (gaussianReal 0 (t - s).toNNReal) brownianProductLaw := by
  have h := (brownianCoordinateProcess_increment_law s t).congr
    ((brownianContinuousModification_ae_eq t).sub
      (brownianContinuousModification_ae_eq s))
  simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using h

theorem brownianContinuousModification_indep_increments
    (s t u v : Real) (hst : s <= t) (htu : t <= u) (huv : u <= v) :
    IndepFun (fun omega =>
        brownianContinuousModification t omega -
          brownianContinuousModification s omega)
      (fun omega =>
        brownianContinuousModification v omega -
          brownianContinuousModification u omega)
      brownianProductLaw := by
  apply (brownianCoordinateProcess_indep_increments
    s t u v hst htu huv).congr
  · exact ((brownianContinuousModification_ae_eq t).sub
      (brownianContinuousModification_ae_eq s)).symm
  · exact ((brownianContinuousModification_ae_eq v).sub
      (brownianContinuousModification_ae_eq u)).symm



theorem brownianContinuousModification_isStandardBrownianMotion :
    IsStandardBrownianMotion brownianContinuousModification brownianProductLaw where
  start := brownianContinuousModification_start
  continuous_paths := brownianContinuousModification_continuous_paths
  measurable := brownianContinuousModification_measurable
  gaussian := brownianContinuousModification_isGaussianProcess
  increment_law := brownianContinuousModification_increment_law
  indep_increments := brownianContinuousModification_indep_increments

end StatMech.SLE
