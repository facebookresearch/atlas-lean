/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Statistics.UncertaintyPropagation
public import PhyslibExt.Units.EngineeringQuantities
public import PhyslibExt.Units.ElectricalDimensions

/-!
# Strain-gauge affine calibration with covariance and units

A strain gauge reports a voltage `V = g ε + b` for the strain `ε`, with a calibrated gain
`g ≠ 0` and offset `b`. The calibration binds the strain `ε = (V - b) / g` as a dimensionless
output of voltage inputs, and its mean, covariance and identifiability are instances of the
existing finite-scenario uncertainty-propagation API. With several gauges the calibration is the
diagonal affine map `ε = diag(g)⁻¹ (V - b)`, and the covariance of the strains keeps every
cross-channel term.

## i. Overview

* Units (A). The gauge voltage, the offset and the gain (volts per unit strain) all have the
  electric-potential dimension `M L² T⁻³ I⁻¹`, the ISQ image of the voltage dimension of
  `PhyslibExt.Units.ElectricalDimensions`, so `(V - b) / g` has dimension one. The typed form
  `gaugeStrainQty` takes `WithDim` voltage inputs and restores the output to `dimensionlessDim`
  by a proved dimension identity; its coordinate is the real formula, which is unchanged by every
  change of positive unit scales.
* Calibration map and identifiability (B). The strain vector of `n` gauges with nonzero gains is
  the affine image `diag(g)⁻¹ V - diag(g)⁻¹ b` of the voltage vector, and `V = g ε + b` inverts it
  channel by channel. The forward map `ε ↦ diag(g) ε` is identifiable in the linear-algebraic
  sense of `Identifiable` exactly when no gain vanishes; a zero gain loses identifiability.
* Finite-scenario statistics (C). On a finite scenario space with weights summing to one, the
  mean strain is the calibrated mean voltage and the strain covariance matrix is
  `diag(g)⁻¹ C_V diag(g)⁻¹`, entrywise `C_V i j / (g i g j)`. For two gauges combined as
  `a₁ ε₁ + a₂ ε₂` the variance keeps the cross term `2 a₁ a₂ C_V 0 1 / (g 0 g 1)`. Nonnegative
  weights make every strain variance nonnegative; the signed weights `(2, -1)` also sum to one
  and give a negative value, so they are not a probability model.
* Measure bridge (D). For a probability mass function `q` on the scenarios, Mathlib's covariance
  of two strain channels under `q.toMeasure` is the propagated finite covariance with the weights
  `(q ω).toReal`, which are nonnegative and sum to one.

Model inputs (hypotheses):

* finite scenario weights are nonnegative and sum to one. Each lemma assumes only the condition
  it uses: the propagation identities need total mass one only and therefore also hold for
  signed normalised weights, which are not a physical probability model; nonnegativity enters
  the variance sign, and a probability mass function supplies both conditions;
* every gain is nonzero: `gaugeStrain`, `gaugeStrainQty` and `gaugeStrainVec` take a
  nonzero-gain proof, so no statement describes a zero-gain "calibration" (with Lean's totalized
  division the bare formula would be `0` for every voltage at `g = 0`); only identifiability is
  characterized for every gain. The input and output dimensions are the declared ones (voltage
  in, dimension one out).

Non-goals: no nonlinear calibration, no bridge-circuit model, no estimator of `g` or `b`, no
temperature compensation, no empirical adequacy or system safety claim.

## ii. Key results

- `voltageDim_exponent`, `gaugeStrain_coord_dimScale`, `gaugeStrainQty_val` : the voltage
  dimension, unit invariance of the strain coordinate, and the restored dimensionless output.
- `gaugeStrainVec_eq_affine`, `gaugeVoltage_gaugeStrain`, `gaugeStrain_gaugeVoltage` : the
  calibration as an affine map and its inverse.
- `identifiable_diagonal_iff` : identifiability of the gain matrix.
- `meanVec_gaugeStrainVec`, `covMatrix_gaugeStrainVec`, `covMatrix_gaugeStrainVec_apply`,
  `covMatrix_two_gauges` : mean and covariance propagation with cross-channel terms.
- `covMatrix_gaugeStrainVec_self_nonneg` : nonnegative weights give nonnegative strain
  variances.
- `toReal_weights_isDistribution`, `covariance_gaugeStrain_toMeasure` : a probability mass
  function gives a finite distribution, and the bridge to measure-theoretic covariance.

## iii. Table of contents

- A. Units of the calibration
- B. The calibration map and identifiability
- C. Finite-scenario mean and covariance
- D. Bridge to measure-theoretic covariance

## iv. References

- JCGM 100:2008, *Evaluation of measurement data — Guide to the expression of uncertainty in
  measurement* (GUM), Section 5.2 (correlated input quantities).
- ISO 80000-6, *Quantities and units — Part 6: Electromagnetism* (electric potential).
- `PhyslibExt.Units.ElectricalDimensions` (the voltage dimension and its ISQ exponents).
- K. Hoffmann, *An Introduction to Stress Analysis and Transducer Design using Strain Gauges*,
  HBM (2012), Chapter 7 (strain-gauge bridge output and calibration).
-/

@[expose] public section

open Matrix Dimension Units.QuantityDimensions Units.EngineeringQuantities
  MathlibExt.Probability.FiniteProbability Statistics.UncertaintyPropagation

namespace Statistics.CalibrationPorts

/-! ## A. Units of the calibration -/

/-- The electric-potential dimension `M L² T⁻³ I⁻¹` over the seven-base ISQ: the ISQ image
`toISQHom Units.ElectricalDimensions.voltageDim` of the charge-based voltage dimension. It is the
dimension of the gauge voltage, the offset and the gain (volts per unit strain). -/
def voltageDim : Dimension ISQDimensionBase := toISQHom Units.ElectricalDimensions.voltageDim

/-- The strain `ε = (V - b) / g` bound by the affine calibration `V = g ε + b`, on real
coordinates, for a nonzero gain `g`. The proof of `g ≠ 0` is part of the definition, so a
zero-gain calibration cannot be formed. -/
noncomputable def gaugeStrain (g b V : ℝ) (_hg : g ≠ 0) : ℝ := (V - b) / g

/-- The strain of `WithDim` voltage inputs: the quotient `(V - b) / g`, restored to
`dimensionlessDim` by the dimension identity `voltageDim * voltageDim⁻¹ = 1`. A nonzero gain is
part of the definition. -/
noncomputable def gaugeStrainQty (g b V : WithDim voltageDim ℝ) (_hg : g.val ≠ 0) :
    WithDim dimensionlessDim ℝ :=
  WithDim.cast ((V - b) / g) (mul_inv_cancel voltageDim)

/-- The exponents of `voltageDim` at the seven ISQ base quantities. -/
lemma voltageDim_exponent (b : ISQDimensionBase) :
    voltageDim.exponent b =
      match b with
      | .length => 2
      | .mass => 1
      | .time => -3
      | .current => -1
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  exact Units.ElectricalDimensions.toISQHom_voltageDim_exponent b

/-- The strain coordinate does not change under a change of unit scales: converting the voltage,
the offset and the gain by the voltage factor leaves `(V - b) / g` unchanged. -/
lemma gaugeStrain_coord_dimScale (u1 u2 : UnitScale ISQDimensionBase) (g b V : ℝ)
    (hg : g ≠ 0) :
    gaugeStrain ((u1.dimScale u2 voltageDim : ℝ) * g) ((u1.dimScale u2 voltageDim : ℝ) * b)
        ((u1.dimScale u2 voltageDim : ℝ) * V)
        (mul_ne_zero (NNReal.coe_pos.mpr (dimScale_pos u1 u2 voltageDim)).ne' hg) =
      gaugeStrain g b V hg := by
  have hs : (u1.dimScale u2 voltageDim : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (dimScale_pos u1 u2 _)).ne'
  unfold gaugeStrain
  rw [← mul_sub, mul_div_mul_left _ _ hs]

/-- The coordinate of the restored strain is the real formula on the input coordinates. -/
lemma gaugeStrainQty_val (g b V : WithDim voltageDim ℝ) (hg : g.val ≠ 0) :
    (gaugeStrainQty g b V hg).val = gaugeStrain g.val b.val V.val hg := by
  rfl

/-! ## B. The calibration map and identifiability -/

/-- The strain vector of `n` gauges with nonzero gains `g` and offsets `b`. -/
noncomputable def gaugeStrainVec {n : ℕ} (g b V : Fin n → ℝ) (hg : ∀ i, g i ≠ 0) : Fin n → ℝ :=
  fun i => gaugeStrain (g i) (b i) (V i) (hg i)

/-- The calibration is the affine map `V ↦ diag(g)⁻¹ V - diag(g)⁻¹ b` of the voltage vector. -/
lemma gaugeStrainVec_eq_affine {n : ℕ} (g b V : Fin n → ℝ) (hg : ∀ i, g i ≠ 0) :
    gaugeStrainVec g b V hg = diagonal (fun i => (g i)⁻¹) *ᵥ V + fun i => -(b i / g i) := by
  ext i
  simp only [gaugeStrainVec, gaugeStrain, Pi.add_apply, mulVec_diagonal]
  ring

/-- A nonzero gain restores the voltage from the strain: `g ε + b = V`. -/
lemma gaugeVoltage_gaugeStrain {g : ℝ} (hg : g ≠ 0) (b V : ℝ) :
    g * gaugeStrain g b V hg + b = V := by
  unfold gaugeStrain
  field_simp
  ring

/-- A nonzero gain recovers the strain from the voltage `V = g ε + b`. -/
lemma gaugeStrain_gaugeVoltage {g : ℝ} (hg : g ≠ 0) (b ε : ℝ) :
    gaugeStrain g b (g * ε + b) hg = ε := by
  unfold gaugeStrain
  field_simp
  ring

/-- **Identifiability of the gains.** The forward calibration `ε ↦ diag(g) ε` of `n` gauges is
identifiable exactly when every gain is nonzero. -/
lemma identifiable_diagonal_iff {n : ℕ} (g : Fin n → ℝ) :
    Identifiable (diagonal g) ↔ ∀ i, g i ≠ 0 := by
  rw [identifiable_iff_trivial_ker]
  constructor
  · intro h i hi
    have h0 := h (Pi.single i 1) (by
      ext j
      by_cases hj : j = i
      · subst hj
        simp [mulVec_diagonal, hi]
      · simp [mulVec_diagonal, hj])
    have h1 := congrFun h0 i
    simp at h1
  · intro h θ hθ
    ext j
    have hj := congrFun hθ j
    simp only [mulVec_diagonal, Pi.zero_apply] at hj
    simpa [h j] using hj

/-! ## C. Finite-scenario mean and covariance -/

/-- **Mean strain**: for weights of total mass one, the mean strain vector is the calibrated
mean voltage vector. -/
lemma meanVec_gaugeStrainVec {Ω : Type*} [Fintype Ω] {n : ℕ} {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) (g b : Fin n → ℝ) (hg : ∀ i, g i ≠ 0) (V : Ω → Fin n → ℝ) :
    meanVec p (fun ω => gaugeStrainVec g b (V ω) hg) = gaugeStrainVec g b (meanVec p V) hg := by
  have h : (fun ω => gaugeStrainVec g b (V ω) hg) =
      fun ω => diagonal (fun i => (g i)⁻¹) *ᵥ V ω + fun i => -(b i / g i) :=
    funext fun ω => gaugeStrainVec_eq_affine g b (V ω) hg
  rw [h, meanVec_affine p V _ _ hp1, gaugeStrainVec_eq_affine]

/-- **Strain covariance**: for weights of total mass one, the strain covariance matrix is
`diag(g)⁻¹ C_V diag(g)⁻¹ᵀ`, an instance of the exact affine covariance law. -/
lemma covMatrix_gaugeStrainVec {Ω : Type*} [Fintype Ω] {n : ℕ} {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) (g b : Fin n → ℝ) (hg : ∀ i, g i ≠ 0) (V : Ω → Fin n → ℝ) :
    covMatrix p (fun ω => gaugeStrainVec g b (V ω) hg) =
      diagonal (fun i => (g i)⁻¹) * covMatrix p V * (diagonal (fun i => (g i)⁻¹))ᵀ := by
  have h : (fun ω => gaugeStrainVec g b (V ω) hg) =
      fun ω => diagonal (fun i => (g i)⁻¹) *ᵥ V ω + fun i => -(b i / g i) :=
    funext fun ω => gaugeStrainVec_eq_affine g b (V ω) hg
  rw [h, covMatrix_affine p V _ _ hp1]

/-- **Cross-channel covariance is kept**: entrywise,
`Cov(ε i, ε j) = Cov(V i, V j) / (g i g j)`, including `i ≠ j`. -/
lemma covMatrix_gaugeStrainVec_apply {Ω : Type*} [Fintype Ω] {n : ℕ} {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) (g b : Fin n → ℝ) (hg : ∀ i, g i ≠ 0) (V : Ω → Fin n → ℝ) (i j : Fin n) :
    covMatrix p (fun ω => gaugeStrainVec g b (V ω) hg) i j = covMatrix p V i j / (g i * g j) := by
  rw [covMatrix_gaugeStrainVec hp1, diagonal_transpose]
  simp only [mul_diagonal, diagonal_mul]
  rw [div_eq_mul_inv, mul_inv]
  ring

/-- **Two correlated gauges**: the variance of the combination `a₁ ε₁ + a₂ ε₂` of two calibrated
strains keeps the cross term `2 a₁ a₂ Cov(V₁, V₂) / (g₁ g₂)`. -/
lemma covMatrix_two_gauges {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1)
    (g b : Fin 2 → ℝ) (hg : ∀ i, g i ≠ 0) (V : Ω → Fin 2 → ℝ) (a₁ a₂ : ℝ) :
    covMatrix p (fun ω => Matrix.of ![![a₁, a₂]] *ᵥ gaugeStrainVec g b (V ω) hg) 0 0 =
      a₁ ^ 2 * covMatrix p V 0 0 / g 0 ^ 2 + a₂ ^ 2 * covMatrix p V 1 1 / g 1 ^ 2 +
        2 * a₁ * a₂ * covMatrix p V 0 1 / (g 0 * g 1) := by
  rw [covMatrix_two_linear p (fun ω => gaugeStrainVec g b (V ω) hg) a₁ a₂,
    covMatrix_gaugeStrainVec_apply hp1 g b hg, covMatrix_gaugeStrainVec_apply hp1 g b hg,
    covMatrix_gaugeStrainVec_apply hp1 g b hg]
  ring

/-- **Physical weights give nonnegative strain variances**: with nonnegative weights, each
diagonal entry of the strain covariance matrix is nonnegative. -/
lemma covMatrix_gaugeStrainVec_self_nonneg {Ω : Type*} [Fintype Ω] {n : ℕ} {p : Ω → ℝ}
    (hp0 : ∀ ω, 0 ≤ p ω) (g b : Fin n → ℝ) (hg : ∀ i, g i ≠ 0) (V : Ω → Fin n → ℝ) (i : Fin n) :
    0 ≤ covMatrix p (fun ω => gaugeStrainVec g b (V ω) hg) i i := by
  rw [covMatrix_apply_self]
  exact variance_nonneg hp0 _

/-! ## D. Bridge to measure-theoretic covariance -/

/-- The weights `(q ω).toReal` of a probability mass function on a finite scenario space are a
finite distribution: nonnegative with total mass one. -/
lemma toReal_weights_isDistribution {Ω : Type*} [Fintype Ω] (q : PMF Ω) :
    (∀ ω, 0 ≤ (q ω).toReal) ∧ ∑ ω, (q ω).toReal = 1 := by
  exact ⟨fun ω => ENNReal.toReal_nonneg, sum_toReal_eq_one q⟩

/-- **Measure bridge**: for a probability mass function `q` on a finite scenario space, Mathlib's
covariance of two strain channels under `q.toMeasure` is the propagated finite covariance with the
nonnegative weights `(q ω).toReal`. -/
lemma covariance_gaugeStrain_toMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {n : ℕ} (q : PMF Ω) (g b : Fin n → ℝ) (hg : ∀ i, g i ≠ 0)
    (V : Ω → Fin n → ℝ) (i j : Fin n) :
    ProbabilityTheory.covariance (fun ω => gaugeStrainVec g b (V ω) hg i)
        (fun ω => gaugeStrainVec g b (V ω) hg j) q.toMeasure =
      covMatrix (fun ω => (q ω).toReal) V i j / (g i * g j) := by
  rw [covariance_toMeasure_eq q]
  exact covMatrix_gaugeStrainVec_apply (sum_toReal_eq_one q) g b hg V i j

end Statistics.CalibrationPorts
