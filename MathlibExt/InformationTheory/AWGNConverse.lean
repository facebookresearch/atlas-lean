/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.LinearGaussianAllLawConverse
public import MathlibExt.InformationTheory.ScalarGaussianCoordinates
public import Mathlib.Probability.Moments.Variance

/-!
# Scalar AWGN variational capacity bound

For the scalar additive white Gaussian noise channel `Y = X + Z`, with noise `Z ~ N(0, N)`,
`N > 0`, independent of the input `X`, and an input under the scalar total-power model
`P ≥ 0`, `E X² ≤ P` (a lower integral, so no integrability is assumed), the mutual information,
in bits and as an extended nonnegative real, satisfies

`I(X; X + Z) ≤ ofReal (log (1 + P / N) / (2 log 2))`.

The input law is arbitrary: it need not be Gaussian and need not be centered. The proof
specializes the all-law log-det converse `measureMutualInformation_linearGaussianChannel_le` of
`MathlibExt.InformationTheory.LinearGaussianAllLawConverse` through the scalar coordinate
embedding of `MathlibExt.InformationTheory.ScalarGaussianCoordinates` at gain `[1]` and noise
covariance `[N]`, then uses `variance X ≤ E X² ≤ P` and monotonicity of the logarithm. The
reference-kernel divergence computation is not repeated.

Main results:
* `measureMutualInformation_scalarAWGN_le_variance`: the bound with `variance X` in place of `P`,
  together with `variance X ≤ P`.
* `measureMutualInformation_scalarAWGN_le`: the bound at the power budget `P`.
* `measureMutualInformation_scalarAWGN_eq_zero_of_power_zero`,
  `measureMutualInformation_scalarAWGN_const`: zero power, and a constant input of any value,
  carry zero information.
* `not_scalarPowerBound_const_of_lt`: the total-moment model rejects a constant input whose
  square exceeds the budget although its variance is `0`, so a variance-only budget is not the
  model.

This is a variational upper bound on mutual information. It is not an operational coding theorem
and not a statement about bandlimited continuous-time channels (Shannon-Hartley in bits per
second).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal NNReal

namespace MathlibExt.InformationTheory.AWGNConverse

open _root_.InformationTheory
open MathlibExt.InformationTheory.ScalarGaussianCoordinates

/-- **Scalar AWGN converse, variance form.** For an arbitrary measurable input `X` under the
scalar total-power model at budget `P`, and noise `Z ~ N(0, N)`, `N > 0`, independent of `X`: the
variance of `X` is at most `P`, and the mutual information `I(X; X + Z)`, in bits, is at most
`ofReal (log (1 + variance X / N) / (2 log 2))`. The mean of `X` does not enter the bound. -/
theorem measureMutualInformation_scalarAWGN_le_variance {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Z : Ω → ℝ} (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun X Z μ) {N : ℝ} (hN : 0 < N)
    (hZlaw : μ.map Z = gaussianReal 0 ⟨N, hN.le⟩) {P : ℝ} (hpow : scalarPowerBound μ X P) :
    variance X μ ≤ P ∧
      measureMutualInformation
          (⟨μ.map (fun ω => (X ω, X ω + Z ω)), inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) ≤
        ENNReal.ofReal (Real.log (1 + variance X μ / N) / (2 * Real.log 2)) := by
  have hsc : Measurable scalarCoord :=
    MathlibExt.Analysis.InnerProductSpace.LineIsometry.lineIsometry.continuous.measurable
  have h0 : scalarCoord 0 = 0 :=
    map_zero MathlibExt.Analysis.InnerProductSpace.LineIsometry.lineIsometry
  have hXv : Measurable (fun ω => scalarCoord (X ω)) := hsc.comp hX
  have hZv : Measurable (fun ω => scalarCoord (Z ω)) := hsc.comp hZ
  have hindv : IndepFun (fun ω => scalarCoord (X ω)) (fun ω => scalarCoord (Z ω)) μ :=
    hind.comp hsc hsc
  have hZlawv : μ.map (fun ω => scalarCoord (Z ω)) =
      multivariateGaussian 0 (!![N] : Matrix (Fin 1) (Fin 1) ℝ) := by
    have hc : (fun ω => scalarCoord (Z ω)) = scalarCoord ∘ Z := rfl
    rw [hc, ← Measure.map_map hsc hZ, hZlaw, map_scalarCoord_gaussianReal 0 N hN.le, h0]
  have hpowv := (scalarPowerBound_iff_powerConstraint μ X P).mpr hpow
  have hK : ∀ a b : Fin 1, cov[fun ω => scalarCoord (X ω) a, fun ω => scalarCoord (X ω) b; μ] =
      (!![variance X μ] : Matrix (Fin 1) (Fin 1) ℝ) a b := by
    intro a b
    rw [Fin.eq_zero a, Fin.eq_zero b]
    simp only [MathlibExt.Analysis.InnerProductSpace.LineIsometry.lineIsometry_apply]
    exact covariance_self hX.aemeasurable
  have hR : (!![N] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
    have hdiag : (!![N] : Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal (fun _ : Fin 1 => N) := by
      ext i j
      rw [Fin.eq_zero i, Fin.eq_zero j]
      rfl
    rw [hdiag]
    exact Matrix.PosDef.diagonal (fun _ => hN)
  obtain ⟨-, htr, hMI⟩ :=
    LinearGaussianAllLawConverse.measureMutualInformation_linearGaussianChannel_le
      (!![1] : Matrix (Fin 1) (Fin 1) ℝ) hR hXv hZv hindv hZlawv hpowv hK
  rw [Matrix.trace_fin_one_of] at htr
  refine ⟨htr, ?_⟩
  have hjoint : (⟨μ.map (fun ω => (scalarCoord (X ω),
        toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ) (scalarCoord (X ω)) +
          scalarCoord (Z ω))), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) =
      ProbabilityMeasure.map
        (⟨μ.map (fun ω => (X ω, X ω + Z ω)), inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ))
        (Prod.map scalarCoord scalarCoord) := by
    apply Subtype.ext
    change μ.map _ = (μ.map (fun ω => (X ω, X ω + Z ω))).map (Prod.map scalarCoord scalarCoord)
    rw [Measure.map_map (hsc.prodMap hsc)
      (show Measurable (fun ω => (X ω, X ω + Z ω)) from hX.prodMk (hX.add hZ))]
    congr 1
    funext ω
    simp only [Function.comp_apply, Prod.map_apply]
    rw [scalarCoord_add]
  rw [hjoint] at hMI
  have hMI := (measureMutualInformation_map_scalarCoordPair
    (⟨μ.map (fun ω => (X ω, X ω + Z ω)), inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ))).symm.trans_le
    hMI
  have hdet : ((!![N] : Matrix (Fin 1) (Fin 1) ℝ) + !![1] * !![variance X μ] *
      (!![1] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).det / (!![N] : Matrix (Fin 1) (Fin 1) ℝ).det =
      1 + variance X μ / N := by
    have hm : (!![N] : Matrix (Fin 1) (Fin 1) ℝ) + !![1] * !![variance X μ] *
        (!![1] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ = !![N + variance X μ] := by
      ext i j
      rw [Fin.eq_zero i, Fin.eq_zero j]
      simp [Matrix.vecMul, dotProduct, -Matrix.transpose_of]
    rw [hm, Matrix.det_fin_one_of, Matrix.det_fin_one_of]
    field_simp
  rw [hdet] at hMI
  exact hMI

/-- **Scalar AWGN variational capacity bound** (headline). For an arbitrary measurable input `X`
(any law, any mean) under the scalar total-power model `P ≥ 0`, `E X² ≤ P`, and noise
`Z ~ N(0, N)`, `N > 0`, independent of `X`, the mutual information `I(X; X + Z)`, in bits and as
an extended nonnegative real, is at most `ofReal (log (1 + P / N) / (2 log 2))`. -/
theorem measureMutualInformation_scalarAWGN_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Z : Ω → ℝ} (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun X Z μ) {N : ℝ} (hN : 0 < N)
    (hZlaw : μ.map Z = gaussianReal 0 ⟨N, hN.le⟩) {P : ℝ} (hpow : scalarPowerBound μ X P) :
    measureMutualInformation
        (⟨μ.map (fun ω => (X ω, X ω + Z ω)), inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) ≤
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)) := by
  obtain ⟨hvar, hMI⟩ := measureMutualInformation_scalarAWGN_le_variance hX hZ hind hN hZlaw hpow
  refine hMI.trans (ENNReal.ofReal_le_ofReal ?_)
  have hlog2 : 0 < 2 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  apply div_le_div_of_nonneg_right _ hlog2.le
  have hv0 : 0 ≤ variance X μ := variance_nonneg X μ
  apply Real.log_le_log (by positivity)
  have := div_le_div_of_nonneg_right hvar hN.le
  linarith

/-! ### Validation statements -/

/-- Validation, zero power: an input meeting the scalar power bound at `P = 0` carries zero
mutual information through the channel. -/
theorem measureMutualInformation_scalarAWGN_eq_zero_of_power_zero {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X Z : Ω → ℝ}
    (hX : Measurable X) (hZ : Measurable Z) (hind : IndepFun X Z μ) {N : ℝ} (hN : 0 < N)
    (hZlaw : μ.map Z = gaussianReal 0 ⟨N, hN.le⟩) (hpow : scalarPowerBound μ X 0) :
    measureMutualInformation
        (⟨μ.map (fun ω => (X ω, X ω + Z ω)), inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) = 0 := by
  have h := measureMutualInformation_scalarAWGN_le hX hZ hind hN hZlaw hpow
  simp only [zero_div, add_zero, Real.log_one, ENNReal.ofReal_zero] at h
  exact le_antisymm h bot_le

private theorem variance_const' {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ) : variance (fun _ : Ω => c) μ = 0 := by
  have h := variance_add_const (μ := μ) (X := (0 : Ω → ℝ)) aestronglyMeasurable_const c
  simp only [Pi.zero_apply, zero_add, variance_zero] at h
  exact h

/-- Validation, constant input: a constant input `c`, possibly nonzero, meets the scalar power
bound at `P = c²` and carries zero mutual information, although that budget is positive when
`c ≠ 0`. -/
theorem measureMutualInformation_scalarAWGN_const {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} (hZ : Measurable Z) {N : ℝ}
    (hN : 0 < N) (hZlaw : μ.map Z = gaussianReal 0 ⟨N, hN.le⟩) (c : ℝ) :
    scalarPowerBound μ (fun _ => c) (c ^ 2) ∧
      measureMutualInformation
          (⟨μ.map (fun ω => (c, c + Z ω)), inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) = 0 := by
  have hpow : scalarPowerBound μ (fun _ => c) (c ^ 2) := by
    refine ⟨sq_nonneg c, ?_⟩
    rw [lintegral_const, measure_univ, mul_one]
  refine ⟨hpow, ?_⟩
  obtain ⟨-, h⟩ := measureMutualInformation_scalarAWGN_le_variance (X := fun _ => c)
    measurable_const hZ (indepFun_const_left c Z) hN hZlaw hpow
  rw [variance_const' μ c] at h
  simp only [zero_div, add_zero, Real.log_one, ENNReal.ofReal_zero] at h
  exact le_antisymm h bot_le

/-- Validation, variance-only counterexample with a large mean: for `0 ≤ P < c²` the constant
input `c` has variance `0 ≤ P`, yet the total-moment model rejects it at budget `P`. -/
theorem not_scalarPowerBound_const_of_lt {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {c P : ℝ} (hP : 0 ≤ P) (hc : P < c ^ 2) :
    variance (fun _ : Ω => c) μ ≤ P ∧ ¬ scalarPowerBound μ (fun _ => c) P := by
  refine ⟨by rw [variance_const' μ c]; exact hP, ?_⟩
  rintro ⟨-, h⟩
  rw [lintegral_const, measure_univ, mul_one] at h
  have := (ENNReal.ofReal_le_ofReal_iff hP).mp h
  linarith

end MathlibExt.InformationTheory.AWGNConverse
