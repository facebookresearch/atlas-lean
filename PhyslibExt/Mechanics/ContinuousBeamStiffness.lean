/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.BeamStiffness
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Supported continuous-beam assembly

## i. Overview

Two prismatic Euler-Bernoulli beam elements assembled into a
continuous beam on three nodes, in global coordinates
`(v0, θ0, v1, θ1, v2, θ2)`. Span 1 (nodes 0-1) and span 2
(nodes 1-2) share the middle-node displacement and slope
through explicit gather matrices; the assembled stiffness is
the sum of the scattered element stiffnesses
(`Mechanics.EulerBernoulli.beamStiffness`). With simple
supports at all three nodes the free coordinates are the
rotations, the supported stiffness is positive definite for
positive rigidities and lengths, and the supported response is
unique. The unsupported assembly still kills rigid translation
and rigid rotation, so one support is insufficient. No
arbitrary released-frame rigidity characterization is
included.

## ii. Key results

- `Mechanics.EulerBernoulli.continuousBeamStiffness`: the
  assembled two-span stiffness.
- `Mechanics.EulerBernoulli.continuousBeamStiffness_quad_form_split`:
  the assembled energy splits over the two spans.
- `Mechanics.EulerBernoulli.supportedStiffness_quad_form_factor`
  and `supportedStiffness_posDef`: the supported energy in
  factored form and its positive definiteness.
- `Mechanics.EulerBernoulli.supportedStiffness_existsUnique`:
  unique supported response.
- `Mechanics.EulerBernoulli.continuousBeamStiffness_mulVec_translation`
  and `continuousBeamStiffness_mulVec_rotation`: the assembled
  rigid modes.

## iii. Table of contents

- A. Gather matrices, assembly, and support injection
- B. Transported element results
- C. Supported stiffness and rigid modes

## iv. References

- `PhyslibExt.Mechanics.BeamStiffness` for the element
  stiffness, its two-square energy factorization, symmetry,
  and rigid-mode kernel.
- Standard direct-stiffness assembly of continuous beams.
-/

@[expose] public section

open Matrix

namespace Mechanics.EulerBernoulli

/-! ## A. Gather matrices, assembly, and support injection -/

/-- Gather matrix selecting span 1 end coordinates
`(v0, θ0, v1, θ1)` from global coordinates
`(v0, θ0, v1, θ1, v2, θ2)`. -/
def spanOneGather : Matrix (Fin 4) (Fin 6) ℝ :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0]

/-- Gather matrix selecting span 2 end coordinates
`(v1, θ1, v2, θ2)`, sharing the middle-node coordinates with
span 1. -/
def spanTwoGather : Matrix (Fin 4) (Fin 6) ℝ :=
  !![0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

/-- Assembled two-span continuous-beam stiffness: the sum of
the two element stiffnesses scattered by their gather matrices,
so the middle-node displacement and slope are shared. Span `i`
has flexural rigidity `EIi` and length `Li`. -/
noncomputable def continuousBeamStiffness (EI1 L1 EI2 L2 : ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  spanOneGatherᵀ * beamStiffness EI1 L1 * spanOneGather
    + spanTwoGatherᵀ * beamStiffness EI2 L2 * spanTwoGather

/-- Support injection for simple supports at all three nodes:
free rotations `(θ0, θ1, θ2)` map to global coordinates with
zero deflections. -/
def supportInjection : Matrix (Fin 6) (Fin 3) ℝ :=
  !![0, 0, 0;
    1, 0, 0;
    0, 0, 0;
    0, 1, 0;
    0, 0, 0;
    0, 0, 1]

/-- Supported stiffness on the free rotations: the assembled
stiffness conjugated by the support injection. -/
noncomputable def supportedStiffness (EI1 L1 EI2 L2 : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  supportInjectionᵀ * continuousBeamStiffness EI1 L1 EI2 L2
    * supportInjection

/-- Span 1 gather picks the first four global coordinates. -/
theorem spanOneGather_mulVec (d : Fin 6 → ℝ) :
    spanOneGather *ᵥ d = ![d 0, d 1, d 2, d 3] := by
  ext i
  fin_cases i
  · simp only [spanOneGather, mulVec, dotProduct, Fin.sum_univ_six]
    change (1:ℝ) * d 0 + 0 * d 1 + 0 * d 2 + 0 * d 3 + 0 * d 4 + 0 * d 5 = d 0
    simp
  · simp only [spanOneGather, mulVec, dotProduct, Fin.sum_univ_six]
    change (0:ℝ) * d 0 + 1 * d 1 + 0 * d 2 + 0 * d 3 + 0 * d 4 + 0 * d 5 = d 1
    simp
  · simp only [spanOneGather, mulVec, dotProduct, Fin.sum_univ_six]
    change (0:ℝ) * d 0 + 0 * d 1 + 1 * d 2 + 0 * d 3 + 0 * d 4 + 0 * d 5 = d 2
    simp
  · simp only [spanOneGather, mulVec, dotProduct, Fin.sum_univ_six]
    change (0:ℝ) * d 0 + 0 * d 1 + 0 * d 2 + 1 * d 3 + 0 * d 4 + 0 * d 5 = d 3
    simp

/-- Span 2 gather picks the shared middle coordinates and the
last two. -/
theorem spanTwoGather_mulVec (d : Fin 6 → ℝ) :
    spanTwoGather *ᵥ d = ![d 2, d 3, d 4, d 5] := by
  ext i
  fin_cases i
  · simp only [spanTwoGather, mulVec, dotProduct, Fin.sum_univ_six]
    change (0:ℝ) * d 0 + 0 * d 1 + 1 * d 2 + 0 * d 3 + 0 * d 4 + 0 * d 5 = d 2
    simp
  · simp only [spanTwoGather, mulVec, dotProduct, Fin.sum_univ_six]
    change (0:ℝ) * d 0 + 0 * d 1 + 0 * d 2 + 1 * d 3 + 0 * d 4 + 0 * d 5 = d 3
    simp
  · simp only [spanTwoGather, mulVec, dotProduct, Fin.sum_univ_six]
    change (0:ℝ) * d 0 + 0 * d 1 + 0 * d 2 + 0 * d 3 + 1 * d 4 + 0 * d 5 = d 4
    simp
  · simp only [spanTwoGather, mulVec, dotProduct, Fin.sum_univ_six]
    change (0:ℝ) * d 0 + 0 * d 1 + 0 * d 2 + 0 * d 3 + 0 * d 4 + 1 * d 5 = d 5
    simp

/-- The support injection places the free rotations with zero
deflections. -/
theorem supportInjection_mulVec (w : Fin 3 → ℝ) :
    supportInjection *ᵥ w = ![0, w 0, 0, w 1, 0, w 2] := by
  ext i
  fin_cases i
  · simp only [supportInjection, mulVec, dotProduct, Fin.sum_univ_three]
    change (0:ℝ) * w 0 + 0 * w 1 + 0 * w 2 = (0:ℝ)
    simp
  · simp only [supportInjection, mulVec, dotProduct, Fin.sum_univ_three]
    change (1:ℝ) * w 0 + 0 * w 1 + 0 * w 2 = w 0
    simp
  · simp only [supportInjection, mulVec, dotProduct, Fin.sum_univ_three]
    change (0:ℝ) * w 0 + 0 * w 1 + 0 * w 2 = (0:ℝ)
    simp
  · simp only [supportInjection, mulVec, dotProduct, Fin.sum_univ_three]
    change (0:ℝ) * w 0 + 1 * w 1 + 0 * w 2 = w 1
    simp
  · simp only [supportInjection, mulVec, dotProduct, Fin.sum_univ_three]
    change (0:ℝ) * w 0 + 0 * w 1 + 0 * w 2 = (0:ℝ)
    simp
  · simp only [supportInjection, mulVec, dotProduct, Fin.sum_univ_three]
    change (0:ℝ) * w 0 + 0 * w 1 + 1 * w 2 = w 2
    simp

/-! ## B. Transported element results -/

/-- The assembled quadratic form splits into the two element
energies on their gathered end coordinates. -/
theorem continuousBeamStiffness_quad_form_split
    (EI1 L1 EI2 L2 : ℝ) (d : Fin 6 → ℝ) :
    d ⬝ᵥ (continuousBeamStiffness EI1 L1 EI2 L2 *ᵥ d)
      = (![d 0, d 1, d 2, d 3]
          ⬝ᵥ (beamStiffness EI1 L1 *ᵥ ![d 0, d 1, d 2, d 3]))
        + (![d 2, d 3, d 4, d 5]
          ⬝ᵥ (beamStiffness EI2 L2 *ᵥ ![d 2, d 3, d 4, d 5])) := by
  unfold continuousBeamStiffness
  rw [Matrix.add_mulVec, dotProduct_add]
  congr 1
  · have h1 : ((spanOneGatherᵀ * beamStiffness EI1 L1 * spanOneGather) *ᵥ d)
        = spanOneGatherᵀ *ᵥ (beamStiffness EI1 L1 *ᵥ (spanOneGather *ᵥ d)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [h1, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    rw [spanOneGather_mulVec]
  · have h2 : ((spanTwoGatherᵀ * beamStiffness EI2 L2 * spanTwoGather) *ᵥ d)
        = spanTwoGatherᵀ *ᵥ (beamStiffness EI2 L2 *ᵥ (spanTwoGather *ᵥ d)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [h2, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    rw [spanTwoGather_mulVec]

/-- The supported quadratic form in factored form, transported
from the canonical element two-square factorization supplied as
`hfactor`: only rotational squares survive the support
injection. -/
private theorem supportedStiffness_quad_form_factor_of
    (hfactor : ∀ (EI L : ℝ) (d : Fin 4 → ℝ),
      d ⬝ᵥ (beamStiffness EI L *ᵥ d)
        = (EI / L ^ 3) * (12 * ((d 0 - d 2) + (L / 2) * (d 1 + d 3)) ^ 2
          + L ^ 2 * (d 1 - d 3) ^ 2))
    (EI1 L1 EI2 L2 : ℝ) (w : Fin 3 → ℝ) :
    w ⬝ᵥ (supportedStiffness EI1 L1 EI2 L2 *ᵥ w)
      = (EI1 / L1 ^ 3) * (12 * ((L1 / 2) * (w 0 + w 1)) ^ 2
          + L1 ^ 2 * (w 0 - w 1) ^ 2)
        + (EI2 / L2 ^ 3) * (12 * ((L2 / 2) * (w 1 + w 2)) ^ 2
          + L2 ^ 2 * (w 1 - w 2) ^ 2) := by
  unfold supportedStiffness
  have hS : ((supportInjectionᵀ * continuousBeamStiffness EI1 L1 EI2 L2 * supportInjection) *ᵥ w)
      = supportInjectionᵀ
        *ᵥ (continuousBeamStiffness EI1 L1 EI2 L2
          *ᵥ (supportInjection *ᵥ w)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hS, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [supportInjection_mulVec]
  rw [continuousBeamStiffness_quad_form_split]
  have e1 : (![(![0, w 0, 0, w 1, 0, w 2] : Fin 6 → ℝ) 0,
      (![0, w 0, 0, w 1, 0, w 2] : Fin 6 → ℝ) 1,
      (![0, w 0, 0, w 1, 0, w 2] : Fin 6 → ℝ) 2,
      (![0, w 0, 0, w 1, 0, w 2] : Fin 6 → ℝ) 3] : Fin 4 → ℝ)
      = ![0, w 0, 0, w 1] := by
    ext i
    fin_cases i <;> rfl
  have e2 : (![(![0, w 0, 0, w 1, 0, w 2] : Fin 6 → ℝ) 2,
      (![0, w 0, 0, w 1, 0, w 2] : Fin 6 → ℝ) 3,
      (![0, w 0, 0, w 1, 0, w 2] : Fin 6 → ℝ) 4,
      (![0, w 0, 0, w 1, 0, w 2] : Fin 6 → ℝ) 5] : Fin 4 → ℝ)
      = ![0, w 1, 0, w 2] := by
    ext i
    fin_cases i <;> rfl
  rw [e1, e2]
  rw [hfactor, hfactor]
  have r1 : (![0, w 0, 0, w 1] : Fin 4 → ℝ) 0 = (0:ℝ) := rfl
  have r2 : (![0, w 0, 0, w 1] : Fin 4 → ℝ) 1 = w 0 := rfl
  have r3 : (![0, w 0, 0, w 1] : Fin 4 → ℝ) 2 = (0:ℝ) := rfl
  have r4 : (![0, w 0, 0, w 1] : Fin 4 → ℝ) 3 = w 1 := rfl
  have s1 : (![0, w 1, 0, w 2] : Fin 4 → ℝ) 0 = (0:ℝ) := rfl
  have s2 : (![0, w 1, 0, w 2] : Fin 4 → ℝ) 1 = w 1 := rfl
  have s3 : (![0, w 1, 0, w 2] : Fin 4 → ℝ) 2 = (0:ℝ) := rfl
  have s4 : (![0, w 1, 0, w 2] : Fin 4 → ℝ) 3 = w 2 := rfl
  simp only [r1, r2, r3, r4, s1, s2, s3, s4, sub_zero, zero_add]

/-- With positive flexural rigidities and span lengths, the
supported stiffness is positive definite: the three simple
supports exclude every assembled mechanism. Transported from
the element factorization and symmetry supplied as hypotheses. -/
private theorem supportedStiffness_posDef_of
    (hfactor : ∀ (EI L : ℝ) (d : Fin 4 → ℝ),
      d ⬝ᵥ (beamStiffness EI L *ᵥ d)
        = (EI / L ^ 3) * (12 * ((d 0 - d 2) + (L / 2) * (d 1 + d 3)) ^ 2
          + L ^ 2 * (d 1 - d 3) ^ 2))
    (htransp : ∀ EI L : ℝ,
      (beamStiffness EI L)ᵀ = beamStiffness EI L)
    {EI1 L1 EI2 L2 : ℝ} (hEI1 : 0 < EI1) (hL1 : 0 < L1)
    (hEI2 : 0 < EI2) (hL2 : 0 < L2) :
    (supportedStiffness EI1 L1 EI2 L2).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · unfold supportedStiffness continuousBeamStiffness Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      htransp, Matrix.mul_assoc]
  · intro w hw
    have hstar : star w = w := by
      ext i
      simp [Pi.star_apply, star_trivial]
    rw [hstar]
    have hfact := supportedStiffness_quad_form_factor_of hfactor EI1 L1 EI2 L2 w
    rw [hfact]
    have hc1 : 0 < EI1 / L1 ^ 3 := div_pos hEI1 (pow_pos hL1 3)
    have hc2 : 0 < EI2 / L2 ^ 3 := div_pos hEI2 (pow_pos hL2 3)
    have h12nn : (0:ℝ) ≤ 12 := by norm_num
    have hL1sq : (0:ℝ) ≤ L1 ^ 2 := sq_nonneg L1
    have hL2sq : (0:ℝ) ≤ L2 ^ 2 := sq_nonneg L2
    have hS1 : (0:ℝ) ≤ 12 * ((L1 / 2) * (w 0 + w 1)) ^ 2 :=
      mul_nonneg h12nn (sq_nonneg _)
    have hD1 : (0:ℝ) ≤ L1 ^ 2 * (w 0 - w 1) ^ 2 :=
      mul_nonneg hL1sq (sq_nonneg _)
    have hS2 : (0:ℝ) ≤ 12 * ((L2 / 2) * (w 1 + w 2)) ^ 2 :=
      mul_nonneg h12nn (sq_nonneg _)
    have hD2 : (0:ℝ) ≤ L2 ^ 2 * (w 1 - w 2) ^ 2 :=
      mul_nonneg hL2sq (sq_nonneg _)
    have hA : (0:ℝ) ≤ (EI1 / L1 ^ 3) * (12 * ((L1 / 2) * (w 0 + w 1)) ^ 2
        + L1 ^ 2 * (w 0 - w 1) ^ 2) :=
      mul_nonneg (le_of_lt hc1) (add_nonneg hS1 hD1)
    have hB : (0:ℝ) ≤ (EI2 / L2 ^ 3) * (12 * ((L2 / 2) * (w 1 + w 2)) ^ 2
        + L2 ^ 2 * (w 1 - w 2) ^ 2) :=
      mul_nonneg (le_of_lt hc2) (add_nonneg hS2 hD2)
    have hsum_nn : (0:ℝ) ≤ (EI1 / L1 ^ 3) * (12 * ((L1 / 2) * (w 0 + w 1)) ^ 2
          + L1 ^ 2 * (w 0 - w 1) ^ 2)
        + (EI2 / L2 ^ 3) * (12 * ((L2 / 2) * (w 1 + w 2)) ^ 2
          + L2 ^ 2 * (w 1 - w 2) ^ 2) :=
      add_nonneg hA hB
    apply lt_of_le_of_ne hsum_nn
    intro hzero
    have hAB := (add_eq_zero_iff_of_nonneg hA hB).mp hzero.symm
    obtain ⟨hA0, hB0⟩ := hAB
    have hc1ne : EI1 / L1 ^ 3 ≠ 0 := ne_of_gt hc1
    have hc2ne : EI2 / L2 ^ 3 ≠ 0 := ne_of_gt hc2
    have hinner1 : 12 * ((L1 / 2) * (w 0 + w 1)) ^ 2
        + L1 ^ 2 * (w 0 - w 1) ^ 2 = 0 := by
      have h := (mul_eq_zero.mp hA0)
      cases h with
      | inl hc => exact absurd hc hc1ne
      | inr hi => exact hi
    have hinner2 : 12 * ((L2 / 2) * (w 1 + w 2)) ^ 2
        + L2 ^ 2 * (w 1 - w 2) ^ 2 = 0 := by
      have h := (mul_eq_zero.mp hB0)
      cases h with
      | inl hc => exact absurd hc hc2ne
      | inr hi => exact hi
    have h1parts := (add_eq_zero_iff_of_nonneg hS1 hD1).mp hinner1
    have h2parts := (add_eq_zero_iff_of_nonneg hS2 hD2).mp hinner2
    obtain ⟨hS10, hD10⟩ := h1parts
    obtain ⟨hS20, hD20⟩ := h2parts
    have h12ne : (12:ℝ) ≠ 0 := by norm_num
    have hsq1 : ((L1 / 2) * (w 0 + w 1)) ^ 2 = 0 := by
      have h := (mul_eq_zero.mp hS10)
      cases h with
      | inl hc => exact absurd hc h12ne
      | inr hi => exact hi
    have hsq2 : ((L2 / 2) * (w 1 + w 2)) ^ 2 = 0 := by
      have h := (mul_eq_zero.mp hS20)
      cases h with
      | inl hc => exact absurd hc h12ne
      | inr hi => exact hi
    have hL1sq_ne : L1 ^ 2 ≠ 0 := ne_of_gt (pow_pos hL1 2)
    have hL2sq_ne : L2 ^ 2 ≠ 0 := ne_of_gt (pow_pos hL2 2)
    have hsqD1 : (w 0 - w 1) ^ 2 = 0 := by
      have h := (mul_eq_zero.mp hD10)
      cases h with
      | inl hc => exact absurd hc hL1sq_ne
      | inr hi => exact hi
    have hsqD2 : (w 1 - w 2) ^ 2 = 0 := by
      have h := (mul_eq_zero.mp hD20)
      cases h with
      | inl hc => exact absurd hc hL2sq_ne
      | inr hi => exact hi
    have eS1 : (L1 / 2) * (w 0 + w 1) = 0 := sq_eq_zero_iff.mp hsq1
    have eS2 : (L2 / 2) * (w 1 + w 2) = 0 := sq_eq_zero_iff.mp hsq2
    have eD1 : w 0 - w 1 = 0 := sq_eq_zero_iff.mp hsqD1
    have eD2 : w 1 - w 2 = 0 := sq_eq_zero_iff.mp hsqD2
    have hw01 : w 0 = w 1 := sub_eq_zero.mp eD1
    have hw12 : w 1 = w 2 := sub_eq_zero.mp eD2
    have hL1half_ne : L1 / 2 ≠ 0 := ne_of_gt (div_pos hL1 (by norm_num))
    have hL2half_ne : L2 / 2 ≠ 0 := ne_of_gt (div_pos hL2 (by norm_num))
    have eSum1 : w 0 + w 1 = 0 := by
      have h := (mul_eq_zero.mp eS1)
      cases h with
      | inl hc => exact absurd hc hL1half_ne
      | inr hi => exact hi
    have eSum2 : w 1 + w 2 = 0 := by
      have h := (mul_eq_zero.mp eS2)
      cases h with
      | inl hc => exact absurd hc hL2half_ne
      | inr hi => exact hi
    have hw0 : w 0 = 0 := by linarith
    have hw1 : w 1 = 0 := by linarith
    have hw2 : w 2 = 0 := by linarith
    apply hw
    ext i
    fin_cases i
    · simpa using hw0
    · simpa using hw1
    · simpa using hw2

/-- Unique supported response: for positive-definite supported
stiffness, every free-rotation load has exactly one response. -/
theorem supportedStiffness_existsUnique
    {EI1 L1 EI2 L2 : ℝ}
    (hS : (supportedStiffness EI1 L1 EI2 L2).PosDef)
    (f : Fin 3 → ℝ) :
    ∃! w : Fin 3 → ℝ, supportedStiffness EI1 L1 EI2 L2 *ᵥ w = f := by
  have hU : IsUnit (supportedStiffness EI1 L1 EI2 L2) := hS.isUnit
  have hinj : Function.Injective (supportedStiffness EI1 L1 EI2 L2).mulVec :=
    Matrix.mulVec_injective_of_isUnit hU
  have hsurj : Function.Surjective (supportedStiffness EI1 L1 EI2 L2).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hU
  obtain ⟨w0, hw0⟩ := hsurj f
  exact ⟨w0, hw0, fun w' hw' => hinj (hw'.trans hw0.symm)⟩

/-- The assembled (unsupported) stiffness kills rigid
translation. -/
private theorem continuousBeamStiffness_mulVec_translation_of
    (htransl : ∀ EI L : ℝ,
      beamStiffness EI L *ᵥ ![1, 0, 1, 0] = 0)
    (EI1 L1 EI2 L2 : ℝ) :
    continuousBeamStiffness EI1 L1 EI2 L2 *ᵥ ![1, 0, 1, 0, 1, 0]
      = 0 := by
  unfold continuousBeamStiffness
  rw [Matrix.add_mulVec]
  have hG1 : spanOneGather *ᵥ (![1, 0, 1, 0, 1, 0] : Fin 6 → ℝ) = ![1, 0, 1, 0] := by
    rw [spanOneGather_mulVec]
    rfl
  have hG2 : spanTwoGather *ᵥ (![1, 0, 1, 0, 1, 0] : Fin 6 → ℝ) = ![1, 0, 1, 0] := by
    rw [spanTwoGather_mulVec]
    rfl
  have hM1 : ((spanOneGatherᵀ * beamStiffness EI1 L1 * spanOneGather)
      *ᵥ (![1, 0, 1, 0, 1, 0] : Fin 6 → ℝ)) = 0 := by
    have h : ((spanOneGatherᵀ * beamStiffness EI1 L1 * spanOneGather)
        *ᵥ (![1, 0, 1, 0, 1, 0] : Fin 6 → ℝ))
        = spanOneGatherᵀ *ᵥ (beamStiffness EI1 L1 *ᵥ (spanOneGather *ᵥ ![1, 0, 1, 0, 1, 0])) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [h, hG1, htransl, Matrix.mulVec_zero]
  have hM2 : ((spanTwoGatherᵀ * beamStiffness EI2 L2 * spanTwoGather)
      *ᵥ (![1, 0, 1, 0, 1, 0] : Fin 6 → ℝ)) = 0 := by
    have h : ((spanTwoGatherᵀ * beamStiffness EI2 L2 * spanTwoGather)
        *ᵥ (![1, 0, 1, 0, 1, 0] : Fin 6 → ℝ))
        = spanTwoGatherᵀ *ᵥ (beamStiffness EI2 L2 *ᵥ (spanTwoGather *ᵥ ![1, 0, 1, 0, 1, 0])) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [h, hG2, htransl, Matrix.mulVec_zero]
  rw [hM1, hM2, add_zero]

/-- The assembled (unsupported) stiffness kills rigid rotation
about the left end: with only the left deflection supported,
this nonzero mode (whose left deflection is zero) is a
mechanism, so one support is insufficient. -/
private theorem continuousBeamStiffness_mulVec_rotation_of
    (htransl : ∀ EI L : ℝ,
      beamStiffness EI L *ᵥ ![1, 0, 1, 0] = 0)
    (hrot : ∀ EI L : ℝ,
      beamStiffness EI L *ᵥ ![0, 1, L, 1] = 0)
    (EI1 L1 EI2 L2 : ℝ) :
    continuousBeamStiffness EI1 L1 EI2 L2
        *ᵥ ![0, 1, L1, 1, L1 + L2, 1] = 0
      ∧ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ) 0 = 0
      ∧ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ) ≠ 0 := by
  have hG1 : spanOneGather *ᵥ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ)
      = ![0, 1, L1, 1] := by
    rw [spanOneGather_mulVec]
    rfl
  have hG2 : spanTwoGather *ᵥ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ)
      = L1 • ![1, 0, 1, 0] + ![0, 1, L2, 1] := by
    rw [spanTwoGather_mulVec]
    ext i
    fin_cases i
    · change L1 = L1 * 1 + 0
      ring
    · change (1:ℝ) = L1 * 0 + 1
      ring
    · change L1 + L2 = L1 * 1 + L2
      ring
    · change (1:ℝ) = L1 * 0 + 1
      ring
  have hM1 : ((spanOneGatherᵀ * beamStiffness EI1 L1 * spanOneGather)
      *ᵥ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ)) = 0 := by
    have h : ((spanOneGatherᵀ * beamStiffness EI1 L1 * spanOneGather)
        *ᵥ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ))
        = spanOneGatherᵀ
          *ᵥ (beamStiffness EI1 L1
            *ᵥ (spanOneGather *ᵥ ![0, 1, L1, 1, L1 + L2, 1])) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [h, hG1, hrot, Matrix.mulVec_zero]
  have hM2 : ((spanTwoGatherᵀ * beamStiffness EI2 L2 * spanTwoGather)
      *ᵥ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ)) = 0 := by
    have h : ((spanTwoGatherᵀ * beamStiffness EI2 L2 * spanTwoGather)
        *ᵥ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ))
        = spanTwoGatherᵀ
          *ᵥ (beamStiffness EI2 L2
            *ᵥ (spanTwoGather *ᵥ ![0, 1, L1, 1, L1 + L2, 1])) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [h, hG2, Matrix.mulVec_add, Matrix.mulVec_smul, htransl, hrot,
      smul_zero, add_zero, Matrix.mulVec_zero]
  have hK : continuousBeamStiffness EI1 L1 EI2 L2
      *ᵥ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ) = 0 := by
    unfold continuousBeamStiffness
    rw [Matrix.add_mulVec, hM1, hM2, add_zero]
  refine ⟨hK, rfl, ?_⟩
  intro h
  have h10 : (1:ℝ) = 0 := congrFun h 1
  exact one_ne_zero h10

/-! ## C. Supported stiffness and rigid modes -/

/-- The supported quadratic form in factored form: only
rotational squares survive the support injection. -/
theorem supportedStiffness_quad_form_factor (EI1 L1 EI2 L2 : ℝ)
    (w : Fin 3 → ℝ) :
    w ⬝ᵥ (supportedStiffness EI1 L1 EI2 L2 *ᵥ w)
      = (EI1 / L1 ^ 3) * (12 * ((L1 / 2) * (w 0 + w 1)) ^ 2
          + L1 ^ 2 * (w 0 - w 1) ^ 2)
        + (EI2 / L2 ^ 3) * (12 * ((L2 / 2) * (w 1 + w 2)) ^ 2
          + L2 ^ 2 * (w 1 - w 2) ^ 2) :=
  supportedStiffness_quad_form_factor_of
    beamStiffness_quad_form_factor EI1 L1 EI2 L2 w

/-- With positive flexural rigidities and span lengths, the
supported stiffness is positive definite: the three simple
supports exclude every assembled mechanism. -/
theorem supportedStiffness_posDef {EI1 L1 EI2 L2 : ℝ}
    (hEI1 : 0 < EI1) (hL1 : 0 < L1) (hEI2 : 0 < EI2) (hL2 : 0 < L2) :
    (supportedStiffness EI1 L1 EI2 L2).PosDef :=
  supportedStiffness_posDef_of beamStiffness_quad_form_factor
    beamStiffness_transpose hEI1 hL1 hEI2 hL2

/-- The assembled (unsupported) stiffness kills rigid
translation. -/
theorem continuousBeamStiffness_mulVec_translation
    (EI1 L1 EI2 L2 : ℝ) :
    continuousBeamStiffness EI1 L1 EI2 L2 *ᵥ ![1, 0, 1, 0, 1, 0]
      = 0 :=
  continuousBeamStiffness_mulVec_translation_of
    beamStiffness_mulVec_translation EI1 L1 EI2 L2

/-- The assembled (unsupported) stiffness kills rigid rotation
about the left end: with only the left deflection supported,
this nonzero mode (whose left deflection is zero) is a
mechanism, so one support is insufficient. -/
theorem continuousBeamStiffness_mulVec_rotation
    (EI1 L1 EI2 L2 : ℝ) :
    continuousBeamStiffness EI1 L1 EI2 L2
        *ᵥ ![0, 1, L1, 1, L1 + L2, 1] = 0
      ∧ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ) 0 = 0
      ∧ (![0, 1, L1, 1, L1 + L2, 1] : Fin 6 → ℝ) ≠ 0 :=
  continuousBeamStiffness_mulVec_rotation_of
    beamStiffness_mulVec_translation
    beamStiffness_mulVec_rotation EI1 L1 EI2 L2

end Mechanics.EulerBernoulli
