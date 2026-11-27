/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Complex.Loewner.Defs
public import MathlibExt.Probability.BrownianMotion.BrownianFiniteDimensional
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Laws of standard Brownian motion

Basic consequences of `IsStandardBrownianMotion` (two-sided, time in `ℝ`): integrability, means,
variances and the covariance `(|s| + |t| - |t - s|) / 2`. The finite-dimensional laws are
`brownianFiniteDimensionalPiLaw`, so the law of the path on `ℝ → ℝ` (product σ-algebra) is the
same for any two standard Brownian motions, and so is the law of the SLE driving function
`√κ B`. The restriction of a standard Brownian motion to times `t ≥ 0` is a Brownian motion in
Mathlib's sense, `ProbabilityTheory.IsBrownianReal`, and so has independent increments in the
strong sense of Mathlib's `HasIndepIncrements`.

## Main results

* `StatMech.SLE.IsStandardBrownianMotion.covariance_eq`.
* `StatMech.SLE.standardBrownian_restrict_law`: the finite-dimensional laws.
* `StatMech.SLE.standardBrownian_processLaw_eq`: uniqueness of the path law.
* `StatMech.SLE.IsStandardBrownianMotion.isBrownianReal`: bridge to Mathlib's `IsBrownianReal`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatMech.SLE

variable {Omega : Type*} [MeasurableSpace Omega]
  {B : Real → Omega → Real} {P : Measure Omega}

theorem IsStandardBrownianMotion.memLp_two
    (hB : IsStandardBrownianMotion B P) (t : Real) :
    MemLp (B t) 2 P :=
  hB.gaussian.hasGaussianLaw_eval t |>.memLp_two

/-- Increments are centered. -/
theorem IsStandardBrownianMotion.integral_increment_eq_zero
    (hB : IsStandardBrownianMotion B P) {s t : Real} (hst : s ≤ t) :
    (integral P fun omega => B t omega - B s omega) = 0 := by
  rw [(hB.increment_law s t hst).integral_eq, integral_id_gaussianReal]

/-- `E B_t = 0`. -/
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

/-- `Var (B_t - B_s) = t - s` for `s ≤ t`. -/
theorem IsStandardBrownianMotion.variance_increment
    (hB : IsStandardBrownianMotion B P) {s t : Real} (hst : s ≤ t) :
    Var[fun omega => B t omega - B s omega; P] = t - s := by
  rw [(hB.increment_law s t hst).variance_eq, variance_id_gaussianReal]
  simp [Real.toNNReal_of_nonneg (sub_nonneg.mpr hst)]

/-- `Var B_t = |t|`. -/
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

/-- `Cov(B_s, B_t) = (|s| + |t| - |t - s|) / 2`. -/
theorem IsStandardBrownianMotion.covariance_eq
    (hB : IsStandardBrownianMotion B P) (s t : Real) :
    cov[B s, B t; P] = (|s| + |t| - |t - s|) / 2 := by
  let : IsProbabilityMeasure P := hB.gaussian.isProbabilityMeasure
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

/-- The finite-dimensional laws of a standard Brownian motion are
`brownianFiniteDimensionalPiLaw`. -/
theorem standardBrownian_restrict_law
    (hB : IsStandardBrownianMotion B P) (I : Finset Real) :
    HasLaw (fun omega => I.restrict (B · omega))
      (brownianFiniteDimensionalPiLaw I) P := by
  let : IsProbabilityMeasure P := hB.gaussian.isProbabilityMeasure
  let X : Omega → EuclideanSpace Real I :=
    fun omega => WithLp.toLp 2 (I.restrict (B · omega))
  have hG : HasGaussianLaw X P := by
    simpa only [X] using (hB.gaussian.hasGaussianLaw I).toLp_pi 2
  have : IsGaussian (P.map X) := hG.isGaussian_map
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
  let Y : Omega → (I → Real) := fun omega => I.restrict (B · omega)
  have hY : Measurable Y := Measurable.of_eval fun i => hB.measurable i
  refine { aemeasurable := hY.aemeasurable, map_eq := ?_ }
  change P.map Y = brownianFiniteDimensionalPiLaw I
  apply (MeasurableEquiv.toLp 2 (I → Real)).measurableEmbedding.map_injective
  have hleft :
      (P.map Y).map
          (MeasurableEquiv.toLp 2 (I → Real)) = P.map X := by
    rw [Measure.map_map (MeasurableEquiv.toLp 2 (I → Real)).measurable hY]
    rfl
  have hright :
      (brownianFiniteDimensionalPiLaw I).map
          (MeasurableEquiv.toLp 2 (I → Real)) =
        brownianFiniteDimensionalLaw I := by
    rw [brownianFiniteDimensionalPiLaw, Measure.map_map
      (MeasurableEquiv.toLp 2 (I → Real)).measurable
      (WithLp.measurable_ofLp 2 (I → Real))]
    have hid : (⇑(MeasurableEquiv.toLp 2 (I → Real)) ∘ WithLp.ofLp) =
        (id : EuclideanSpace ℝ I → EuclideanSpace ℝ I) := by
      funext x; rfl
    rw [hid, Measure.map_id]
  rw [hleft, hright, hEuclidean]

/-- The restriction of a standard Brownian motion to times `t ≥ 0` is a Brownian motion in the sense
of Mathlib's `ProbabilityTheory.IsBrownianReal`. -/
theorem IsStandardBrownianMotion.isBrownianReal (hB : IsStandardBrownianMotion B P) :
    IsBrownianReal (fun (t : ℝ≥0) ω => B t ω) P where
  toIsPreBrownianReal :=
    (hB.gaussian.comp_right (fun t : ℝ≥0 => (t : ℝ))).isPreBrownianReal_of_covariance
      (fun t => hB.integral_eq_zero t)
      (fun s t hst => by
        change cov[B s, B t; P] = s
        rw [hB.covariance_eq, NNReal.abs_eq, NNReal.abs_eq,
          abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))]
        ring)
  cont := by
    filter_upwards [hB.continuous_paths] with ω h
    exact h.comp NNReal.continuous_coe

/-- On times `t ≥ 0`, a standard Brownian motion has independent increments in the sense of
Mathlib's `HasIndepIncrements` (mutual independence of the increments over any finite chain of
times), not only the pairwise independence in `IsStandardBrownianMotion.indep_increments`. -/
theorem IsStandardBrownianMotion.hasIndepIncrements_nnreal (hB : IsStandardBrownianMotion B P) :
    HasIndepIncrements (fun (t : ℝ≥0) ω => B t ω) P :=
  hB.isBrownianReal.hasIndepIncrements

/-- Two standard Brownian motions have the same finite-dimensional laws. -/
theorem standardBrownian_restrict_law_eq
    {Omega1 Omega2 : Type*} [MeasurableSpace Omega1] [MeasurableSpace Omega2]
    {B1 : Real → Omega1 → Real} {B2 : Real → Omega2 → Real}
    {P1 : Measure Omega1} {P2 : Measure Omega2}
    (hB1 : IsStandardBrownianMotion B1 P1)
    (hB2 : IsStandardBrownianMotion B2 P2) (I : Finset Real) :
    P1.map (fun omega => I.restrict (B1 · omega)) =
      P2.map (fun omega => I.restrict (B2 · omega)) := by
  rw [(standardBrownian_restrict_law hB1 I).map_eq, (standardBrownian_restrict_law hB2 I).map_eq]

/-- Two standard Brownian motions have the same law on `ℝ → ℝ` (product σ-algebra). -/
theorem standardBrownian_processLaw_eq
    {Omega1 Omega2 : Type*} [MeasurableSpace Omega1] [MeasurableSpace Omega2]
    {B1 : Real → Omega1 → Real} {B2 : Real → Omega2 → Real}
    {P1 : Measure Omega1} {P2 : Measure Omega2}
    (hB1 : IsStandardBrownianMotion B1 P1)
    (hB2 : IsStandardBrownianMotion B2 P2) :
    P1.map (fun omega t => B1 t omega) = P2.map (fun omega t => B2 t omega) := by
  have : IsProbabilityMeasure P1 := hB1.gaussian.isProbabilityMeasure
  have : IsProbabilityMeasure P2 := hB2.gaussian.isProbabilityMeasure
  let Q : (I : Finset Real) → Measure (I → Real) :=
    fun I => P1.map (fun omega => I.restrict (B1 · omega))
  have hproj1 : IsProjectiveLimit
      (P1.map (fun omega t => B1 t omega)) Q := by
    apply ProbabilityTheory.isProjectiveLimit_map
    exact (Measurable.of_eval hB1.measurable).aemeasurable
  have hproj2 : IsProjectiveLimit
      (P2.map (fun omega t => B2 t omega)) Q := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I)
      (Measurable.of_eval hB2.measurable)]
    exact
      standardBrownian_restrict_law_eq hB2 hB1 I
  exact hproj1.unique hproj2

/-- Scaling a path by `√κ` is measurable on `ℝ → ℝ`. -/
theorem measurable_sleDrivingPath (kappa : Real) :
    Measurable (fun b : Real → Real => fun t => Real.sqrt kappa * b t) := by
  exact Measurable.of_eval fun t => measurable_const.mul (measurable_pi_apply t)

/-- The law of the SLE driving function `√κ B` on `ℝ → ℝ` does not depend on the standard Brownian
motion `B`. -/
theorem standardBrownian_sleDriving_processLaw_eq
    {Omega1 Omega2 : Type*} [MeasurableSpace Omega1] [MeasurableSpace Omega2]
    {B1 : Real → Omega1 → Real} {B2 : Real → Omega2 → Real}
    {P1 : Measure Omega1} {P2 : Measure Omega2}
    (hB1 : IsStandardBrownianMotion B1 P1)
    (hB2 : IsStandardBrownianMotion B2 P2) (kappa : Real) :
    P1.map (fun omega => sleDriving kappa B1 omega) =
      P2.map (fun omega => sleDriving kappa B2 omega) := by
  have hpaths1 : Measurable (fun omega t => B1 t omega) :=
    Measurable.of_eval hB1.measurable
  have hpaths2 : Measurable (fun omega t => B2 t omega) :=
    Measurable.of_eval hB2.measurable
  calc
    P1.map (fun omega => sleDriving kappa B1 omega) =
        (P1.map (fun omega t => B1 t omega)).map
          (fun b : Real → Real => fun t => Real.sqrt kappa * b t) := by
            rw [Measure.map_map (measurable_sleDrivingPath kappa) hpaths1]
            rfl
    _ = (P2.map (fun omega t => B2 t omega)).map
          (fun b : Real → Real => fun t => Real.sqrt kappa * b t) := by
            rw [standardBrownian_processLaw_eq hB1 hB2]
    _ = P2.map (fun omega => sleDriving kappa B2 omega) := by
            rw [Measure.map_map (measurable_sleDrivingPath kappa) hpaths2]
            rfl

end StatMech.SLE
