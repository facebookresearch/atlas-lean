/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Statistics.UncertaintyPropagation
public import PhyslibExt.Units.QuantityDimensions
public import PhyslibExt.Units.ElectricalDimensions

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strain-gauge affine and quadratic calibration with covariance and units

A strain gauge reports a voltage `V = g ε + b` for the strain `ε`, with a calibrated gain
`g ≠ 0` and offset `b`. The calibration binds the strain `ε = (V - b) / g` as a dimensionless
output of voltage inputs, and its mean, covariance and identifiability are instances of the
existing finite-scenario uncertainty-propagation API. With several gauges the calibration is the
diagonal affine map `ε = diag(g)⁻¹ (V - b)`, and the covariance of the strains keeps every
cross-channel term. A quadratic calibration `f v = c0 + c1 v + c2 v ^ 2` of a voltage keeps its
exact Taylor remainder, and its output variance keeps the remainder variance and the
linear/remainder cross term.

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
* Quadratic calibration (E). On a voltage interval `[a, b]` with Taylor base `v₀ ∈ [a, b]`, the
  calibration `f v = c0 + c1 v + c2 v ^ 2` is exactly its first-order part
  `f v₀ + f' v₀ (v - v₀)`, with the actual derivative `f' v₀ = c1 + 2 c2 v₀`, plus the remainder
  `c2 (v - v₀) ^ 2`. With output dimension `d` the coefficients have dimensions `d`,
  `d / voltageDim` and `d / voltageDim ^ 2`. The output variance is the variance of the
  first-order part plus the variance of the remainder plus twice their covariance; with total
  mass one these are `f' v₀ ^ 2 Var V`, `c2 ^ 2 Var (V - v₀) ^ 2` and
  `f' v₀ c2 Cov(V, (V - v₀) ^ 2)`. The existing Hessian theorem gives only the pointwise bound
  `|c2| (v - v₀) ^ 2` on the box, from which no moment conclusion follows, and the raw quadratic
  is not globally Lipschitz.

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
* for the quadratic calibration the coefficients and the Taylor base are supplied, and a
  scenario law in `[a, b]` (`ScenarioLawIn`) is a finite distribution, nonnegative weights of
  total mass one, so zero-probability scenarios are allowed, with every scenario voltage in
  `[a, b]`; each lemma assumes only the conditions it uses.

Non-goals: no nonlinear calibration beyond the quadratic map of section E, no Gaussian or
unbounded input law for it and no moment bound from its pointwise Taylor bound, no bridge-circuit
model, no estimator of `g`, `b` or the quadratic coefficients, no temperature compensation, no
empirical adequacy or system safety claim.

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
- `quadCalibration_hasDerivAt`, `quadCalibration_eq_linear_add_remainder` : the actual derivative
  and the exact Taylor remainder of the quadratic calibration.
- `quadCalibrationQty_val`, `quadCalibration_coord_dimScale` : the typed quadratic calibration and
  its change of units.
- `quadCalibrationVec_hessian_le`, `quadCalibrationVec_jacobianRemainder`,
  `quadCalibrationVec_remainder_le` : the Hessian bound, the exact remainder in the Jacobian
  carrier and the pointwise bound of the Hessian theorem.
- `quadCalibration_not_lipschitzWith` : the raw quadratic is not globally Lipschitz.
- `variance_quadCalibration_expansion`, `variance_quadLinearPart`,
  `covariance_quadLinearPart_quadRemainder`, `variance_quadCalibration_of_scenarioLaw` : the
  output variance with the remainder variance and the cross term.
- `variance_quadCalibration_toMeasure` : the same split for Mathlib's variance.

## iii. Table of contents

- A. Units of the calibration
- B. The calibration map and identifiability
- C. Finite-scenario mean and covariance
- D. Bridge to measure-theoretic covariance
- E. Quadratic calibration with nonlinear and cross terms
  - E.1. The quadratic map, its derivative and the exact remainder
  - E.2. The Hessian theorem: a pointwise bound only
  - E.3. Output covariance under a finite scenario law in the box

## iv. References

- JCGM 100:2008, *Evaluation of measurement data — Guide to the expression of uncertainty in
  measurement* (GUM), Section 5.1.2 (higher-order terms of the Taylor series) and Section 5.2
  (correlated input quantities).
- JCGM 101:2008, *Evaluation of measurement data — Supplement 1 to the GUM: Propagation of
  distributions using a Monte Carlo method* (nonlinear models where the first-order law fails).
- ISO 80000-6, *Quantities and units — Part 6: Electromagnetism* (electric potential).
- `PhyslibExt.Units.ElectricalDimensions` (the voltage dimension and its ISQ exponents).
- K. Hoffmann, *An Introduction to Stress Analysis and Transducer Design using Strain Gauges*,
  HBM (2012), Chapter 7 (strain-gauge bridge output and calibration).
-/

@[expose] public section

open Matrix Dimension Units.QuantityDimensions MathlibExt.Probability.FiniteProbability
  Statistics.UncertaintyPropagation

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

/-! ## E. Quadratic calibration with nonlinear and cross terms -/

/-! ### E.1. The quadratic map, its derivative and the exact remainder -/

/-- The quadratic calibration `f v = c0 + c1 v + c2 v ^ 2` on real coordinates: the voltage `v`
in, the output in the unit of `c0` out; `c1` is in output units per volt and `c2` in output
units per volt squared. -/
noncomputable def quadCalibration (c0 c1 c2 v : ℝ) : ℝ :=
  c0 + c1 * v + c2 * v ^ 2

/-- The first-order Taylor part of the calibration at the base voltage `v₀`:
`f v₀ + f' v₀ (v - v₀)`, with the actual derivative `f' v₀ = c1 + 2 c2 v₀`. -/
noncomputable def quadLinearPart (c0 c1 c2 v₀ v : ℝ) : ℝ :=
  quadCalibration c0 c1 c2 v₀ + (c1 + 2 * c2 * v₀) * (v - v₀)

/-- The exact Taylor remainder of the calibration at the base voltage `v₀`: `c2 (v - v₀) ^ 2`,
in output units. -/
noncomputable def quadRemainder (c2 v₀ v : ℝ) : ℝ :=
  c2 * (v - v₀) ^ 2

/-- The actual derivative of the calibration: `f' v = c1 + 2 c2 v`. -/
lemma quadCalibration_hasDerivAt (c0 c1 c2 v : ℝ) :
    HasDerivAt (quadCalibration c0 c1 c2) (c1 + 2 * c2 * v) v := by
  unfold quadCalibration
  have h := (((hasDerivAt_id' v).const_mul c1).const_add c0).add
    ((hasDerivAt_pow 2 v).const_mul c2)
  convert h using 1
  norm_num
  ring

/-- Exact Taylor expansion at every base voltage `v₀`: the calibration is its first-order part
plus the quadratic remainder, with no term dropped. -/
lemma quadCalibration_eq_linear_add_remainder (c0 c1 c2 v₀ v : ℝ) :
    quadCalibration c0 c1 c2 v = quadLinearPart c0 c1 c2 v₀ v + quadRemainder c2 v₀ v := by
  simp only [quadLinearPart, quadRemainder, quadCalibration]
  ring

/-- The calibration on `WithDim` quantities: the voltage in, an output of dimension `d` out, with
coefficients of dimensions `d`, `d / voltageDim` and `d / voltageDim ^ 2`. The two
voltage-dependent terms are restored to dimension `d` by proved dimension identities. -/
noncomputable def quadCalibrationQty {d : Dimension ISQDimensionBase} (c0 : WithDim d ℝ)
    (c1 : WithDim (d * voltageDim⁻¹) ℝ) (c2 : WithDim (d * (voltageDim⁻¹ * voltageDim⁻¹)) ℝ)
    (v : WithDim voltageDim ℝ) : WithDim d ℝ :=
  c0 + WithDim.cast (c1 * v) (inv_mul_cancel_right d voltageDim) +
    WithDim.cast (c2 * (v * v)) (by group)

/-- The coordinate of the typed calibration is the real formula on the coordinates. -/
lemma quadCalibrationQty_val {d : Dimension ISQDimensionBase} (c0 : WithDim d ℝ)
    (c1 : WithDim (d * voltageDim⁻¹) ℝ) (c2 : WithDim (d * (voltageDim⁻¹ * voltageDim⁻¹)) ℝ)
    (v : WithDim voltageDim ℝ) :
    (quadCalibrationQty c0 c1 c2 v).val = quadCalibration c0.val c1.val c2.val v.val := by
  simp only [quadCalibrationQty, quadCalibration, WithDim.val_add, WithDim.cast,
    WithDim.withDim_hMul_val]
  ring

/-- Change of units: converting the voltage by the voltage factor and each coefficient by the
factor of its dimension converts the output coordinate by the output factor. -/
lemma quadCalibration_coord_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (d : Dimension ISQDimensionBase) (c0 c1 c2 v : ℝ) :
    quadCalibration ((u1.dimScale u2 d : ℝ) * c0)
        ((u1.dimScale u2 (d * voltageDim⁻¹) : ℝ) * c1)
        ((u1.dimScale u2 (d * (voltageDim⁻¹ * voltageDim⁻¹)) : ℝ) * c2)
        ((u1.dimScale u2 voltageDim : ℝ) * v) =
      (u1.dimScale u2 d : ℝ) * quadCalibration c0 c1 c2 v := by
  have hV : (0 : ℝ) < (u1.dimScale u2 voltageDim : ℝ) :=
    NNReal.coe_pos.mpr (dimScale_pos u1 u2 voltageDim)
  simp only [dimScale_mul, dimScale_inv]
  unfold quadCalibration
  field_simp

/-! ### E.2. The Hessian theorem: a pointwise bound only -/

/-- The calibration as a map `(Fin 1 → ℝ) → (Fin 1 → ℝ)`, the carrier of the componentwise
Jacobian remainder bounds. -/
noncomputable def quadCalibrationVec (c0 c1 c2 : ℝ) : (Fin 1 → ℝ) → (Fin 1 → ℝ) :=
  fun y _ => quadCalibration c0 c1 c2 (y 0)

/-- Explicit Hessian bound: everywhere, the second Fréchet derivative of the calibration has
operator norm at most `2 |c2|` for the sup norm on `Fin 1 → ℝ`. -/
lemma quadCalibrationVec_hessian_le (c0 c1 c2 : ℝ) (y : Fin 1 → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (fun y => quadCalibrationVec c0 c1 c2 y 0)) y‖ ≤ 2 * |c2| := by
  set π := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0 with hπdef
  have hg : ∀ y : Fin 1 → ℝ, HasFDerivAt (fun y : Fin 1 → ℝ => quadCalibrationVec c0 c1 c2 y 0)
      ((c1 + 2 * c2 * y 0) • π) y := fun y =>
    (quadCalibration_hasDerivAt c0 c1 c2 (y 0)).comp_hasFDerivAt y π.hasFDerivAt
  have hD : fderiv ℝ (fun y : Fin 1 → ℝ => quadCalibrationVec c0 c1 c2 y 0) =
      fun y => (c1 + 2 * c2 * y 0) • π := by
    funext y
    exact (hg y).fderiv
  rw [hD]
  have hs : HasFDerivAt (fun y : Fin 1 → ℝ => c1 + 2 * c2 * y 0) ((2 * c2) • π) y := by
    have h1 := (π.hasFDerivAt (x := y)).const_mul (2 * c2)
    have h2 := h1.const_add c1
    simpa [hπdef] using h2
  rw [(hs.smul_const π).fderiv]
  have hπ1 : ‖π‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun k => ?_
    simpa [hπdef] using norm_le_pi_norm k 0
  have hc : ‖(2 * c2)‖ = 2 * |c2| := by
    rw [Real.norm_eq_abs, abs_mul]
    norm_num
  calc ‖((2 * c2) • π).smulRight π‖ = ‖(2 * c2) • π‖ * ‖π‖ :=
        ContinuousLinearMap.norm_smulRight_apply _ _
    _ = 2 * |c2| * ‖π‖ * ‖π‖ := by rw [norm_smul, hc]
    _ ≤ 2 * |c2| * 1 * 1 := by gcongr
    _ = 2 * |c2| := by ring

/-- In the Jacobian carrier the first-order remainder of the calibration at `x` is exactly the
quadratic remainder at the base `x 0`. -/
lemma quadCalibrationVec_jacobianRemainder (c0 c1 c2 : ℝ) (x δ : Fin 1 → ℝ) :
    jacobianRemainder (quadCalibrationVec c0 c1 c2) x δ 0 =
      quadRemainder c2 (x 0) (x 0 + δ 0) := by
  set π := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0 with hπdef
  have hg : HasFDerivAt (fun y : Fin 1 → ℝ => quadCalibrationVec c0 c1 c2 y 0)
      ((c1 + 2 * c2 * x 0) • π) x :=
    (quadCalibration_hasDerivAt c0 c1 c2 (x 0)).comp_hasFDerivAt x π.hasFDerivAt
  have hdiff : DifferentiableAt ℝ (quadCalibrationVec c0 c1 c2) x := by
    rw [differentiableAt_pi]
    intro i
    exact hg.differentiableAt
  have h2 : HasFDerivAt (fun y => quadCalibrationVec c0 c1 c2 y 0)
      ((ContinuousLinearMap.proj 0).comp (fderiv ℝ (quadCalibrationVec c0 c1 c2) x)) x :=
    (hasFDerivAt_apply (𝕜 := ℝ) 0 (quadCalibrationVec c0 c1 c2 x)).comp x hdiff.hasFDerivAt
  have h3 := h2.unique hg
  have hconn : fderiv ℝ (quadCalibrationVec c0 c1 c2) x δ 0 = (c1 + 2 * c2 * x 0) * δ 0 := by
    have := congrArg (fun L => L δ) h3
    simpa [hπdef] using this
  unfold jacobianRemainder
  simp only [Pi.sub_apply, hconn]
  simp only [quadCalibrationVec, quadRemainder, quadCalibration, Pi.add_apply]
  ring

/-- The Hessian theorem `jacobianRemainder_component_le_of_hessian` with the Hessian bound
`2 |c2|` on the voltage box `[a, b]`, both points in the box: the pointwise remainder bound. It
bounds the remainder at one point and says nothing about its moments under a law. -/
lemma quadCalibrationVec_remainder_le {a b c0 c1 c2 : ℝ} {x δ : Fin 1 → ℝ}
    (hx : x ∈ Set.Icc (fun _ => a) (fun _ => b))
    (hxδ : x + δ ∈ Set.Icc (fun _ => a) (fun _ => b)) :
    |jacobianRemainder (quadCalibrationVec c0 c1 c2) x δ 0| ≤ 2 * |c2| / 2 * ‖δ‖ ^ 2 := by
  set π := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0 with hπdef
  have hg : HasFDerivAt (fun y : Fin 1 → ℝ => quadCalibrationVec c0 c1 c2 y 0)
      ((c1 + 2 * c2 * x 0) • π) x :=
    (quadCalibration_hasDerivAt c0 c1 c2 (x 0)).comp_hasFDerivAt x π.hasFDerivAt
  have hdiff : DifferentiableAt ℝ (quadCalibrationVec c0 c1 c2) x := by
    rw [differentiableAt_pi]
    intro i
    exact hg.differentiableAt
  have hcd : ContDiffOn ℝ 2 (fun y : Fin 1 → ℝ => quadCalibrationVec c0 c1 c2 y 0) Set.univ := by
    apply ContDiff.contDiffOn
    unfold quadCalibrationVec quadCalibration
    fun_prop
  have h := jacobianRemainder_component_le_of_hessian (quadCalibrationVec c0 c1 c2) x δ 0
    (fun _ => 2 * |c2|) isOpen_univ (Set.subset_univ _) hdiff hcd
    (fun y _ => quadCalibrationVec_hessian_le c0 c1 c2 y) hx hxδ
  simpa using h

/-- The global Lipschitz error budget does not apply to the raw quadratic: for `c2 ≠ 0` the
calibration is not Lipschitz on `ℝ` with any constant. -/
lemma quadCalibration_not_lipschitzWith {c0 c1 c2 : ℝ} (hc2 : c2 ≠ 0) (K : NNReal) :
    ¬ LipschitzWith K (quadCalibration c0 c1 c2) := by
  intro hL
  have hc2pos : 0 < |c2| := abs_pos.mpr hc2
  set x : ℝ := ((K : ℝ) + |c1| + 1) / |c2| with hx
  have hxpos : 0 < x := by positivity
  have h := hL.dist_le_mul x 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hxpos] at h
  have hdiff : quadCalibration c0 c1 c2 x - quadCalibration c0 c1 c2 0 = x * (c1 + c2 * x) := by
    unfold quadCalibration
    ring
  rw [hdiff, abs_mul, abs_of_pos hxpos] at h
  have h2 : |c1 + c2 * x| ≤ K := by
    have h' : x * |c1 + c2 * x| ≤ x * K := by linarith
    exact le_of_mul_le_mul_left h' hxpos
  have h3 : |c2 * x| = (K : ℝ) + |c1| + 1 := by
    rw [abs_mul, abs_of_pos hxpos, hx]
    field_simp
  have h4 : |c2 * x| ≤ |c1 + c2 * x| + |c1| := by
    have := abs_sub (c1 + c2 * x) c1
    simpa using this
  linarith

/-! ### E.3. Output covariance under a finite scenario law in the box -/

/-- A finite scenario law entirely in the voltage interval `[a, b]`: nonnegative weights `p` of
total mass one, a finite distribution, so zero-probability scenarios are allowed (the weights of
a probability mass function qualify, `toReal_weights_isDistribution`), and scenario voltages
`V ω ∈ [a, b]` for every scenario. -/
def ScenarioLawIn {Ω : Type*} [Fintype Ω] (a b : ℝ) (p V : Ω → ℝ) : Prop :=
  (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1 ∧ ∀ ω, V ω ∈ Set.Icc a b

/-- The output variance with the cross term kept: for every weight it is the variance of the
first-order part plus the variance of the remainder plus twice their covariance. -/
lemma variance_quadCalibration_expansion {Ω : Type*} [Fintype Ω] (p V : Ω → ℝ)
    (c0 c1 c2 v₀ : ℝ) :
    variance p (fun ω => quadCalibration c0 c1 c2 (V ω)) =
      variance p (fun ω => quadLinearPart c0 c1 c2 v₀ (V ω)) +
        variance p (fun ω => quadRemainder c2 v₀ (V ω)) +
        2 * covariance p (fun ω => quadLinearPart c0 c1 c2 v₀ (V ω))
          (fun ω => quadRemainder c2 v₀ (V ω)) := by
  have hf : (fun ω => quadCalibration c0 c1 c2 (V ω)) =
      fun ω => 1 * quadLinearPart c0 c1 c2 v₀ (V ω) + 1 * quadRemainder c2 v₀ (V ω) := by
    funext ω
    rw [quadCalibration_eq_linear_add_remainder c0 c1 c2 v₀ (V ω)]
    ring
  rw [hf, ← covariance_self, covariance_linear_left, covariance_linear_right,
    covariance_linear_right, covariance_self, covariance_self,
    covariance_comm p (fun ω => quadRemainder c2 v₀ (V ω))]
  ring

/-- The first-order part is affine in the voltage, so by the exact affine covariance law its
variance is `f' v₀ ^ 2 Var V` for weights of total mass one. -/
lemma variance_quadLinearPart {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1)
    (V : Ω → ℝ) (c0 c1 c2 v₀ : ℝ) :
    variance p (fun ω => quadLinearPart c0 c1 c2 v₀ (V ω)) =
      (c1 + 2 * c2 * v₀) ^ 2 * variance p V := by
  have h : (fun ω => quadLinearPart c0 c1 c2 v₀ (V ω)) =
      fun ω => (c1 + 2 * c2 * v₀) * V ω +
        (quadCalibration c0 c1 c2 v₀ - (c1 + 2 * c2 * v₀) * v₀) := by
    funext ω
    unfold quadLinearPart
    ring
  rw [h, variance_affine hp1]

/-- The cross covariance of the first-order part and the remainder is
`f' v₀ c2 Cov(V, (V - v₀) ^ 2)` for weights of total mass one; it is not zero in general. -/
lemma covariance_quadLinearPart_quadRemainder {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) (V : Ω → ℝ) (c0 c1 c2 v₀ : ℝ) :
    covariance p (fun ω => quadLinearPart c0 c1 c2 v₀ (V ω))
        (fun ω => quadRemainder c2 v₀ (V ω)) =
      (c1 + 2 * c2 * v₀) * c2 * covariance p V (fun ω => (V ω - v₀) ^ 2) := by
  have hL : (fun ω => quadLinearPart c0 c1 c2 v₀ (V ω)) =
      fun ω => (c1 + 2 * c2 * v₀) * V ω +
        (quadCalibration c0 c1 c2 v₀ - (c1 + 2 * c2 * v₀) * v₀) * (fun _ => (1 : ℝ)) ω := by
    funext ω
    unfold quadLinearPart
    ring
  have hR : (fun ω => quadRemainder c2 v₀ (V ω)) =
      fun ω => c2 * (fun ω => (V ω - v₀) ^ 2) ω + 0 * (fun _ => (1 : ℝ)) ω := by
    funext ω
    unfold quadRemainder
    ring
  have h1 : ∀ Y : Ω → ℝ, covariance p (fun _ => (1 : ℝ)) Y = 0 := by
    intro Y
    rw [covariance_eq_sub hp1, expectation_const hp1]
    simp
  rw [hL, covariance_linear_left, hR, covariance_linear_right, h1]
  ring

/-- Output covariance under a finite scenario law entirely in `[a, b]` (nonnegative weights of
total mass one), with Taylor base `v₀ ∈ [a, b]`: the output variance keeps the remainder
variance and the linear/remainder cross term,
`Var f(V) = f' v₀ ^ 2 Var V + c2 ^ 2 Var (V - v₀) ^ 2 + 2 f' v₀ c2 Cov(V, (V - v₀) ^ 2)`,
while the Hessian theorem bounds the remainder only pointwise, scenario by scenario. -/
lemma variance_quadCalibration_of_scenarioLaw {Ω : Type*} [Fintype Ω] {a b : ℝ} {p V : Ω → ℝ}
    (hlaw : ScenarioLawIn a b p V) {v₀ : ℝ} (hv₀ : v₀ ∈ Set.Icc a b) (c0 c1 c2 : ℝ) :
    variance p (fun ω => quadCalibration c0 c1 c2 (V ω)) =
        (c1 + 2 * c2 * v₀) ^ 2 * variance p V + c2 ^ 2 * variance p (fun ω => (V ω - v₀) ^ 2) +
          2 * ((c1 + 2 * c2 * v₀) * c2) * covariance p V (fun ω => (V ω - v₀) ^ 2) ∧
      ∀ ω, |quadRemainder c2 v₀ (V ω)| ≤ 2 * |c2| / 2 * (V ω - v₀) ^ 2 := by
  obtain ⟨-, hp1, hV⟩ := hlaw
  refine ⟨?_, fun ω => ?_⟩
  · rw [variance_quadCalibration_expansion p V c0 c1 c2 v₀, variance_quadLinearPart hp1,
      covariance_quadLinearPart_quadRemainder hp1]
    have hR : (fun ω => quadRemainder c2 v₀ (V ω)) = fun ω => c2 * (V ω - v₀) ^ 2 + 0 := by
      funext ω
      unfold quadRemainder
      ring
    rw [hR, variance_affine hp1]
    ring
  · have hx : (fun _ : Fin 1 => v₀) ∈ Set.Icc (fun _ => a) (fun _ => b) :=
      ⟨fun _ => hv₀.1, fun _ => hv₀.2⟩
    have hxδ : (fun _ : Fin 1 => v₀) + (fun _ => V ω - v₀) ∈ Set.Icc (fun _ => a) (fun _ => b) := by
      refine ⟨fun _ => ?_, fun _ => ?_⟩
      · simp [(hV ω).1]
      · simp [(hV ω).2]
    have h := quadCalibrationVec_remainder_le (c0 := c0) (c1 := c1) (c2 := c2) hx hxδ
    rw [quadCalibrationVec_jacobianRemainder] at h
    have hn : ‖(fun _ : Fin 1 => V ω - v₀)‖ = |V ω - v₀| := by
      rw [pi_norm_const, Real.norm_eq_abs]
    rw [hn, sq_abs] at h
    simpa using h

set_option linter.unusedFintypeInType false in
/-- Bridge to measure-theoretic variance: for a probability mass function `q` on the scenarios,
`ProbabilityTheory.variance_add` splits Mathlib's variance of the output under `q.toMeasure`
into the variance of the first-order part, twice the cross covariance and the variance of the
remainder. -/
lemma variance_quadCalibration_toMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (q : PMF Ω) (V : Ω → ℝ) (c0 c1 c2 v₀ : ℝ) :
    ProbabilityTheory.variance (fun ω => quadCalibration c0 c1 c2 (V ω)) q.toMeasure =
      ProbabilityTheory.variance (fun ω => quadLinearPart c0 c1 c2 v₀ (V ω)) q.toMeasure +
        2 * ProbabilityTheory.covariance (fun ω => quadLinearPart c0 c1 c2 v₀ (V ω))
          (fun ω => quadRemainder c2 v₀ (V ω)) q.toMeasure +
        ProbabilityTheory.variance (fun ω => quadRemainder c2 v₀ (V ω)) q.toMeasure := by
  have hsplit : (fun ω => quadCalibration c0 c1 c2 (V ω)) =
      (fun ω => quadLinearPart c0 c1 c2 v₀ (V ω)) + (fun ω => quadRemainder c2 v₀ (V ω)) := by
    funext ω
    simp only [Pi.add_apply]
    exact quadCalibration_eq_linear_add_remainder c0 c1 c2 v₀ (V ω)
  rw [hsplit]
  exact ProbabilityTheory.variance_add MeasureTheory.MemLp.of_discrete
    MeasureTheory.MemLp.of_discrete

end Statistics.CalibrationPorts
