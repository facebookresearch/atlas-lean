/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.Defs
import Code.SLE.BrownianFiniteDimensional
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.SpecificCodomains.WithLp











open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatMech.SLE

variable {Omega : Type*} [MeasurableSpace Omega]
  {B : Real -> Omega -> Real} {P : Measure Omega}


theorem IsStandardBrownianMotion.memLp_two
    (hB : IsStandardBrownianMotion B P) (t : Real) :
    MemLp (B t) 2 P :=
  hB.gaussian.hasGaussianLaw_eval t |>.memLp_two


theorem IsStandardBrownianMotion.integral_increment_eq_zero
    (hB : IsStandardBrownianMotion B P) {s t : Real} (hst : s <= t) :
    (integral P fun omega => B t omega - B s omega) = 0 := by
  rw [(hB.increment_law s t hst).integral_eq, integral_id_gaussianReal]


theorem IsStandardBrownianMotion.integral_eq_zero
    (hB : IsStandardBrownianMotion B P) (t : Real) :
    (integral P fun omega => B t omega) = 0 := by
  rcases le_total 0 t with ht | ht
  · calc
      (integral P fun omega => B t omega) =
          (integral P fun omega => B t omega - B 0 omega) := by
            apply integral_congr_ae
            filter_upwards [hB.start] with omega homega
            simp [homega]
      _ = 0 := hB.integral_increment_eq_zero ht
  · have hneg : (integral P fun omega => -B t omega) = 0 := by
      calc
        (integral P fun omega => -B t omega) =
            (integral P fun omega => B 0 omega - B t omega) := by
              apply integral_congr_ae
              filter_upwards [hB.start] with omega homega
              simp [homega]
        _ = 0 := hB.integral_increment_eq_zero ht
    simpa only [integral_neg, neg_eq_zero] using hneg


theorem IsStandardBrownianMotion.variance_increment
    (hB : IsStandardBrownianMotion B P) {s t : Real} (hst : s <= t) :
    Var[fun omega => B t omega - B s omega; P] = t - s := by
  rw [(hB.increment_law s t hst).variance_eq, variance_id_gaussianReal]
  simp [Real.toNNReal_of_nonneg (sub_nonneg.mpr hst)]


theorem IsStandardBrownianMotion.variance_eq_abs
    (hB : IsStandardBrownianMotion B P) (t : Real) :
    Var[B t; P] = |t| := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    calc
      Var[B t; P] = Var[fun omega => B t omega - B 0 omega; P] := by
        apply variance_congr
        filter_upwards [hB.start] with omega homega
        simp [homega]
      _ = t := by simpa using hB.variance_increment ht
  · rw [abs_of_nonpos ht]
    calc
      Var[B t; P] = Var[fun omega => -B t omega; P] := variance_fun_neg.symm
      _ = Var[fun omega => B 0 omega - B t omega; P] := by
        apply variance_congr
        filter_upwards [hB.start] with omega homega
        simp [homega]
      _ = -t := by simpa using hB.variance_increment ht


theorem IsStandardBrownianMotion.covariance_eq
    (hB : IsStandardBrownianMotion B P) (s t : Real) :
    cov[B s, B t; P] = (|s| + |t| - |t - s|) / 2 := by
  letI : IsProbabilityMeasure P := hB.gaussian.isProbabilityMeasure
  rcases le_total s t with hst | hts
  · have hvar := variance_fun_sub (hB.memLp_two t) (hB.memLp_two s)
    rw [hB.variance_increment hst, hB.variance_eq_abs, hB.variance_eq_abs] at hvar
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    rw [covariance_comm (B s) (B t)]
    linarith
  · have hvar := variance_fun_sub (hB.memLp_two s) (hB.memLp_two t)
    rw [hB.variance_increment hts, hB.variance_eq_abs, hB.variance_eq_abs] at hvar
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
    linarith


theorem standardBrownian_restrict_law_eq
    {Omega1 Omega2 : Type*} [MeasurableSpace Omega1] [MeasurableSpace Omega2]
    {B1 : Real -> Omega1 -> Real} {B2 : Real -> Omega2 -> Real}
    {P1 : Measure Omega1} {P2 : Measure Omega2}
    (hB1 : IsStandardBrownianMotion B1 P1)
    (hB2 : IsStandardBrownianMotion B2 P2) (I : Finset Real) :
    P1.map (fun omega => I.restrict (B1 · omega)) =
      P2.map (fun omega => I.restrict (B2 · omega)) := by
  letI : IsProbabilityMeasure P1 := hB1.gaussian.isProbabilityMeasure
  letI : IsProbabilityMeasure P2 := hB2.gaussian.isProbabilityMeasure
  let X1 : Omega1 -> EuclideanSpace Real I :=
    fun omega => WithLp.toLp 2 (I.restrict (B1 · omega))
  let X2 : Omega2 -> EuclideanSpace Real I :=
    fun omega => WithLp.toLp 2 (I.restrict (B2 · omega))
  have hG1 : HasGaussianLaw X1 P1 := by
    simpa only [X1] using (hB1.gaussian.hasGaussianLaw I).toLp_pi 2
  have hG2 : HasGaussianLaw X2 P2 := by
    simpa only [X2] using (hB2.gaussian.hasGaussianLaw I).toLp_pi 2
  haveI : IsGaussian (P1.map X1) := hG1.isGaussian_map
  haveI : IsGaussian (P2.map X2) := hG2.isGaussian_map
  have hmean1 : (integral (P1.map X1) id) = 0 := by
    rw [integral_map hG1.aemeasurable (by fun_prop)]
    ext i
    rw [MeasureTheory.eval_integral_piLp]
    · exact hB1.integral_eq_zero i
    · intro j
      exact hB1.gaussian.hasGaussianLaw_eval j |>.integrable
  have hmean2 : (integral (P2.map X2) id) = 0 := by
    rw [integral_map hG2.aemeasurable (by fun_prop)]
    ext i
    rw [MeasureTheory.eval_integral_piLp]
    · exact hB2.integral_eq_zero i
    · intro j
      exact hB2.gaussian.hasGaussianLaw_eval j |>.integrable
  have hcov : covarianceBilin (P1.map X1) = covarianceBilin (P2.map X2) := by
    ext x y
    change covarianceBilin
        (P1.map (fun omega => WithLp.toLp 2 (fun i : I => B1 i omega))) x y =
      covarianceBilin
        (P2.map (fun omega => WithLp.toLp 2 (fun i : I => B2 i omega))) x y
    rw [covarianceBilin_apply_pi (X := fun i : I => B1 i)
        (fun i => hB1.memLp_two i),
      covarianceBilin_apply_pi (X := fun i : I => B2 i)
        (fun i => hB2.memLp_two i)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hB1.covariance_eq i j, hB2.covariance_eq i j]
  have hEuclidean : P1.map X1 = P2.map X2 := by
    apply IsGaussian.ext
    · rw [hmean1, hmean2]
    · exact hcov
  apply (MeasurableEquiv.toLp 2 (I -> Real)).measurableEmbedding.map_injective
  have hmap1 :
      (P1.map (fun omega => I.restrict (B1 · omega))).map
          (MeasurableEquiv.toLp 2 (I -> Real)) = P1.map X1 := by
    rw [Measure.map_map (μ := P1)
      (g := (MeasurableEquiv.toLp 2 (I -> Real)))
      (f := fun omega => I.restrict (B1 · omega))
      (MeasurableEquiv.toLp 2 (I -> Real)).measurable
      (measurable_pi_lambda _ fun i => hB1.measurable i)]
    rfl
  have hmap2 :
      (P2.map (fun omega => I.restrict (B2 · omega))).map
          (MeasurableEquiv.toLp 2 (I -> Real)) = P2.map X2 := by
    rw [Measure.map_map (μ := P2)
      (g := (MeasurableEquiv.toLp 2 (I -> Real)))
      (f := fun omega => I.restrict (B2 · omega))
      (MeasurableEquiv.toLp 2 (I -> Real)).measurable
      (measurable_pi_lambda _ fun i => hB2.measurable i)]
    rfl
  rw [hmap1, hmap2, hEuclidean]



theorem standardBrownian_restrict_law
    (hB : IsStandardBrownianMotion B P) (I : Finset Real) :
    HasLaw (fun omega => I.restrict (B · omega))
      (brownianFiniteDimensionalPiLaw I) P := by
  letI : IsProbabilityMeasure P := hB.gaussian.isProbabilityMeasure
  let X : Omega -> EuclideanSpace Real I :=
    fun omega => WithLp.toLp 2 (I.restrict (B · omega))
  have hG : HasGaussianLaw X P := by
    simpa only [X] using (hB.gaussian.hasGaussianLaw I).toLp_pi 2
  haveI : IsGaussian (P.map X) := hG.isGaussian_map
  have hmean : (integral (P.map X) id) = 0 := by
    rw [integral_map hG.aemeasurable (by fun_prop)]
    ext i
    rw [MeasureTheory.eval_integral_piLp]
    · exact hB.integral_eq_zero i
    · intro j
      exact hB.gaussian.hasGaussianLaw_eval j |>.integrable
  have hcov : covarianceBilin (P.map X) =
      covarianceBilin (brownianFiniteDimensionalLaw I) := by
    ext x y
    change covarianceBilin
        (P.map (fun omega => WithLp.toLp 2 (fun i : I => B i omega))) x y = _
    rw [covarianceBilin_apply_pi (X := fun i : I => B i)
        (fun i => hB.memLp_two i),
      brownianFiniteDimensionalLaw,
      ProbabilityTheory.covarianceBilin_multivariateGaussian
        (brownianCovarianceMatrix_posSemidef I)]
    simp only [dotProduct, Matrix.mulVec, brownianCovarianceMatrix, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hB.covariance_eq, brownianCovariance_eq]
    ring
  have hEuclidean : P.map X = brownianFiniteDimensionalLaw I := by
    apply IsGaussian.ext
    · rw [hmean]
      simp [brownianFiniteDimensionalLaw]
    · exact hcov
  let Y : Omega -> (I -> Real) := fun omega => I.restrict (B · omega)
  have hY : Measurable Y := measurable_pi_lambda _ fun i => hB.measurable i
  refine { aemeasurable := hY.aemeasurable, map_eq := ?_ }
  change P.map Y = brownianFiniteDimensionalPiLaw I
  apply (MeasurableEquiv.toLp 2 (I -> Real)).measurableEmbedding.map_injective
  have hleft :
      (P.map Y).map
          (MeasurableEquiv.toLp 2 (I -> Real)) = P.map X := by
    rw [Measure.map_map (MeasurableEquiv.toLp 2 (I -> Real)).measurable hY]
    rfl
  have hright :
      (brownianFiniteDimensionalPiLaw I).map
          (MeasurableEquiv.toLp 2 (I -> Real)) =
        brownianFiniteDimensionalLaw I := by
    rw [brownianFiniteDimensionalPiLaw, Measure.map_map
      (MeasurableEquiv.toLp 2 (I -> Real)).measurable
      (WithLp.measurable_ofLp 2 (I -> Real))]
    simpa only [Function.comp_apply, WithLp.toLp_ofLp] using
      (Measure.map_id (μ := brownianFiniteDimensionalLaw I))
  rw [hleft, hright, hEuclidean]



theorem standardBrownian_processLaw_eq
    {Omega1 Omega2 : Type*} [MeasurableSpace Omega1] [MeasurableSpace Omega2]
    {B1 : Real -> Omega1 -> Real} {B2 : Real -> Omega2 -> Real}
    {P1 : Measure Omega1} {P2 : Measure Omega2}
    (hB1 : IsStandardBrownianMotion B1 P1)
    (hB2 : IsStandardBrownianMotion B2 P2) :
    P1.map (fun omega t => B1 t omega) = P2.map (fun omega t => B2 t omega) := by
  haveI : IsProbabilityMeasure P1 := hB1.gaussian.isProbabilityMeasure
  haveI : IsProbabilityMeasure P2 := hB2.gaussian.isProbabilityMeasure
  let Q : (I : Finset Real) -> Measure (I -> Real) :=
    fun I => P1.map (fun omega => I.restrict (B1 · omega))
  have hproj1 : IsProjectiveLimit
      (P1.map (fun omega t => B1 t omega)) Q := by
    apply ProbabilityTheory.isProjectiveLimit_map
    exact (measurable_pi_lambda _ hB1.measurable).aemeasurable
  have hproj2 : IsProjectiveLimit
      (P2.map (fun omega t => B2 t omega)) Q := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I)
      (measurable_pi_lambda _ hB2.measurable)]
    simpa only [Q, Function.comp_apply] using
      standardBrownian_restrict_law_eq hB2 hB1 I
  exact hproj1.unique hproj2



theorem measurable_sleDrivingPath (kappa : Real) :
    Measurable (fun b : Real -> Real => fun t => Real.sqrt kappa * b t) := by
  exact measurable_pi_lambda _ fun t => measurable_const.mul (measurable_pi_apply t)





theorem standardBrownian_sleDriving_processLaw_eq
    {Omega1 Omega2 : Type*} [MeasurableSpace Omega1] [MeasurableSpace Omega2]
    {B1 : Real -> Omega1 -> Real} {B2 : Real -> Omega2 -> Real}
    {P1 : Measure Omega1} {P2 : Measure Omega2}
    (hB1 : IsStandardBrownianMotion B1 P1)
    (hB2 : IsStandardBrownianMotion B2 P2) (kappa : Real) :
    P1.map (fun omega => sleDriving kappa B1 omega) =
      P2.map (fun omega => sleDriving kappa B2 omega) := by
  have hpaths1 : Measurable (fun omega t => B1 t omega) :=
    measurable_pi_lambda _ hB1.measurable
  have hpaths2 : Measurable (fun omega t => B2 t omega) :=
    measurable_pi_lambda _ hB2.measurable
  calc
    P1.map (fun omega => sleDriving kappa B1 omega) =
        (P1.map (fun omega t => B1 t omega)).map
          (fun b : Real -> Real => fun t => Real.sqrt kappa * b t) := by
            rw [Measure.map_map (measurable_sleDrivingPath kappa) hpaths1]
            rfl
    _ = (P2.map (fun omega t => B2 t omega)).map
          (fun b : Real -> Real => fun t => Real.sqrt kappa * b t) := by
            rw [standardBrownian_processLaw_eq hB1 hB2]
    _ = P2.map (fun omega => sleDriving kappa B2 omega) := by
            rw [Measure.map_map (measurable_sleDrivingPath kappa) hpaths2]
            rfl

end StatMech.SLE
