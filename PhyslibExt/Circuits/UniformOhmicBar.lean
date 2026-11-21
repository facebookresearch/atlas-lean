/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniform ohmic bar terminal current

## i. Overview

A uniform conductive bar of length `ℓ`, cross-section `S` of
area `A`, conductivity `σ` and terminal voltage `V` carries the
uniform axial field `V/ℓ`. With Ohm's law `J = σE` the terminal
current is `σA/ℓ · V`: conductance times voltage, with
conductance `σA/ℓ` and resistance its reciprocal. A
nonuniform-field shortcut is refuted by an explicit example, and
a rectangle cross-section example computes the current exactly.

## ii. Key results

- `terminalCurrent_eq_conductance_mul`: the terminal current is
  conductance times voltage.
- `voltage_eq_resistance_mul_terminalCurrent`: the same relation
  in resistance form.
- The concrete rectangle case is exercised in the test module.

## iii. Table of contents

- A. The uniform ohmic bar

## iv. References

- J. W. Nilsson and S. A. Riedel, *Electric Circuits*, eleventh
  edition, Pearson, 2019: resistance and Ohm's law for a uniform
  conductor.

## A. The uniform ohmic bar

-/

@[expose] public section

namespace PhyslibExt.Circuits.UniformOhmicBar

open MeasureTheory Set

/-- The explicit uniform axial field of a bar of length `ℓ` with terminal voltage drop `V`. -/
noncomputable def uniformAxialField (V ℓ : ℝ) : ℝ :=
  V / ℓ

/-- Local scalar Ohm law: current density `J = σ E`. -/
def ohmCurrentDensity (σ E : ℝ) : ℝ :=
  σ * E

/-- Terminal current: the `+x` flux `∫_S J dA` of the axial current density `J` through the
cross-section `S` (current entering at terminal `0`, leaving at terminal `1`). -/
noncomputable def terminalCurrent (S : Set (ℝ × ℝ)) (J : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p in S, J p

/-- Conductance `σ A / ℓ` of the bar; defined for every `σ`, and `0` when `σ = 0`. -/
noncomputable def conductance (σ A ℓ : ℝ) : ℝ :=
  σ * A / ℓ

/-- Resistance `ℓ / (σ A)`, available only for `σ > 0`. This is a raw
totalized expression: it is a physical resistance (positive, and the
reciprocal of `conductance`) only on the physical domain `σ > 0`, `A > 0`,
`ℓ > 0`, as used by `conductance_mul_resistance` and `resistance_pos`. -/
noncomputable def resistance (σ A ℓ : ℝ) (_hσ : 0 < σ) : ℝ :=
  ℓ / (σ * A)

/-! ### Headline -/

/-- **Uniform ohmic bar.** For a bar with measurable cross-section `S` of area `A > 0`, length
`ℓ > 0`, conductivity `σ ≥ 0`, uniform axial field `E = V / ℓ` and local Ohm law `J = σ E` on
the cross-section, the terminal current is `I = (σ A / ℓ) V`. -/
lemma terminalCurrent_eq_conductance_mul (σ A ℓ V : ℝ) (S : Set (ℝ × ℝ))
    (E J : ℝ × ℝ → ℝ) (hS : MeasurableSet S) (hSA : volume S = ENNReal.ofReal A) (hA : 0 < A)
    (hℓ : 0 < ℓ) (hσ : 0 ≤ σ) (hE : ∀ p ∈ S, E p = uniformAxialField V ℓ)
    (hJ : ∀ p ∈ S, J p = ohmCurrentDensity σ (E p)) :
    terminalCurrent S J = conductance σ A ℓ * V := by
  have hJconst : Set.EqOn J (fun _ : ℝ × ℝ => ohmCurrentDensity σ (uniformAxialField V ℓ)) S :=
    fun p hp => by rw [hJ p hp, hE p hp]
  have hEq : (∫ p in S, J p ∂volume)
      = (∫ p in S, (fun _ : ℝ × ℝ => ohmCurrentDensity σ (uniformAxialField V ℓ)) p ∂volume) :=
    MeasureTheory.setIntegral_congr_fun hS hJconst
  have hC : (∫ p in S, (fun _ : ℝ × ℝ => ohmCurrentDensity σ (uniformAxialField V ℓ)) p ∂volume)
      = volume.real S • (ohmCurrentDensity σ (uniformAxialField V ℓ)) :=
    MeasureTheory.setIntegral_const _
  have hInt : terminalCurrent S J = volume.real S • (ohmCurrentDensity σ (uniformAxialField V ℓ)) := by
    unfold terminalCurrent
    exact hEq.trans hC
  rw [hInt, MeasureTheory.measureReal_def, hSA, ENNReal.toReal_ofReal hA.le, smul_eq_mul]
  unfold conductance ohmCurrentDensity uniformAxialField
  ring

/-! ### Resistance, only for `σ > 0` -/

/-- For `σ > 0`, `V = R I` with `R = ℓ / (σ A)`. -/
lemma voltage_eq_resistance_mul_terminalCurrent (σ A ℓ V : ℝ) (S : Set (ℝ × ℝ))
    (E J : ℝ × ℝ → ℝ) (hS : MeasurableSet S) (hSA : volume S = ENNReal.ofReal A) (hA : 0 < A)
    (hℓ : 0 < ℓ) (hσ : 0 < σ) (hE : ∀ p ∈ S, E p = uniformAxialField V ℓ)
    (hJ : ∀ p ∈ S, J p = ohmCurrentDensity σ (E p)) :
    V = resistance σ A ℓ hσ * terminalCurrent S J := by
  have hI :=
    terminalCurrent_eq_conductance_mul σ A ℓ V S E J hS hSA hA hℓ hσ.le hE hJ
  rw [hI]
  unfold resistance conductance
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have hA' : A ≠ 0 := ne_of_gt hA
  have hℓ' : ℓ ≠ 0 := ne_of_gt hℓ
  have hσA : σ * A ≠ 0 := mul_ne_zero hσ' hA'
  field_simp

/-- For `σ > 0`, conductance and resistance are reciprocal. -/
lemma conductance_mul_resistance (σ A ℓ : ℝ) (hσ : 0 < σ) (hA : 0 < A) (hℓ : 0 < ℓ) :
    conductance σ A ℓ * resistance σ A ℓ hσ = 1 := by
  unfold conductance resistance
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have hA' : A ≠ 0 := ne_of_gt hA
  have hℓ' : ℓ ≠ 0 := ne_of_gt hℓ
  have hσA : σ * A ≠ 0 := mul_ne_zero hσ' hA'
  field_simp

/-! ### Validation -/

/-- `σ = 0` gives zero conductance, with no division by `σ`. -/
lemma conductance_zero_left (A ℓ : ℝ) : conductance 0 A ℓ = 0 := by
  simp [conductance]

/-- An insulating bar (`σ = 0`) carries no terminal current. -/
lemma terminalCurrent_eq_zero_of_conductivity_eq_zero (A ℓ V : ℝ) (S : Set (ℝ × ℝ))
    (E J : ℝ × ℝ → ℝ) (hS : MeasurableSet S) (hSA : volume S = ENNReal.ofReal A) (hA : 0 < A)
    (hℓ : 0 < ℓ) (hE : ∀ p ∈ S, E p = uniformAxialField V ℓ)
    (hJ : ∀ p ∈ S, J p = ohmCurrentDensity 0 (E p)) :
    terminalCurrent S J = 0 := by
  have h :=
    terminalCurrent_eq_conductance_mul 0 A ℓ V S E J hS hSA hA hℓ (le_refl 0) hE hJ
  rw [conductance_zero_left] at h
  simpa using h

/-- Terminal orientation: with the terminals swapped the voltage drop is `-V` and the axial
current density is `-J`; the terminal current is then `-I`, and the law still reads
`(σ A / ℓ) (-V)`. -/
lemma terminalCurrent_reversed (σ A ℓ V : ℝ) (S : Set (ℝ × ℝ)) (E J : ℝ × ℝ → ℝ)
    (hS : MeasurableSet S) (hSA : volume S = ENNReal.ofReal A) (hA : 0 < A) (hℓ : 0 < ℓ)
    (hσ : 0 ≤ σ) (hE : ∀ p ∈ S, E p = uniformAxialField V ℓ)
    (hJ : ∀ p ∈ S, J p = ohmCurrentDensity σ (E p)) :
    terminalCurrent S (fun p => -J p) = -terminalCurrent S J ∧
      terminalCurrent S (fun p => -J p) = conductance σ A ℓ * (-V) := by
  have hI :=
    terminalCurrent_eq_conductance_mul σ A ℓ V S E J hS hSA hA hℓ hσ hE hJ
  have hNeg : terminalCurrent S (fun p => -J p) = -terminalCurrent S J := by
    unfold terminalCurrent
    exact MeasureTheory.integral_neg _
  refine ⟨hNeg, ?_⟩
  rw [hNeg, hI]
  ring

/-- Passive sign convention: the absorbed power `V I` is nonnegative. -/
lemma voltage_mul_terminalCurrent_nonneg (σ A ℓ V : ℝ) (S : Set (ℝ × ℝ))
    (E J : ℝ × ℝ → ℝ) (hS : MeasurableSet S) (hSA : volume S = ENNReal.ofReal A) (hA : 0 < A)
    (hℓ : 0 < ℓ) (hσ : 0 ≤ σ) (hE : ∀ p ∈ S, E p = uniformAxialField V ℓ)
    (hJ : ∀ p ∈ S, J p = ohmCurrentDensity σ (E p)) :
    0 ≤ V * terminalCurrent S J := by
  have hI :=
    terminalCurrent_eq_conductance_mul σ A ℓ V S E J hS hSA hA hℓ hσ hE hJ
  rw [hI]
  have hG : 0 ≤ conductance σ A ℓ := by
    unfold conductance
    exact div_nonneg (mul_nonneg hσ hA.le) hℓ.le
  have hEq : V * (conductance σ A ℓ * V) = conductance σ A ℓ * (V * V) := by ring
  rw [hEq]
  exact mul_nonneg hG (mul_self_nonneg V)

/-- A nonuniform field needs an integral: on a unit-length bar the axial field `E x = 2 x`
has terminal voltage `∫₀¹ E = 1`, yet the flux through the cross-section at `x = 0` is `0`,
not the constant-field value `(σ A / 1) · 1`. -/
lemma nonuniformField_constantShortcut_fails (σ A : ℝ) (S : Set (ℝ × ℝ))
    (hS : MeasurableSet S) (hSA : volume S = ENNReal.ofReal A) (hA : 0 < A) (hσ : 0 < σ) :
    (∫ x in (0 : ℝ)..1, 2 * x) = 1 ∧
      terminalCurrent S (fun _ => ohmCurrentDensity σ (2 * 0)) ≠
        conductance σ A 1 * ∫ x in (0 : ℝ)..1, 2 * x := by
  have hInt : (∫ x in (0 : ℝ)..1, 2 * x) = 1 := by
    have hMul : (∫ x in (0 : ℝ)..1, 2 * x) = 2 * (∫ x in (0 : ℝ)..1, x) :=
      intervalIntegral.integral_const_mul 2 (fun x : ℝ => x)
    rw [hMul, integral_id]
    norm_num
  have hLHS : terminalCurrent S (fun _ : ℝ × ℝ => ohmCurrentDensity σ (2 * 0)) = 0 := by
    have hEq : (∫ p in S, (fun _ : ℝ × ℝ => ohmCurrentDensity σ (2 * 0)) p ∂volume)
        = (∫ p in S, (0 : ℝ) ∂volume) := by
      apply MeasureTheory.setIntegral_congr_fun hS
      intro p _
      simp [ohmCurrentDensity]
    have hC : (∫ p in S, (0 : ℝ) ∂volume) = 0 := by
      rw [MeasureTheory.setIntegral_const]
      simp
    unfold terminalCurrent
    exact hEq.trans hC
  refine ⟨hInt, ?_⟩
  rw [hInt, mul_one]
  unfold conductance
  rw [div_one, hLHS]
  exact Ne.symm (mul_ne_zero (ne_of_gt hσ) (ne_of_gt hA))

/-- On the physical domain the resistance is positive. -/
lemma resistance_pos (σ A ℓ : ℝ) (hσ : 0 < σ) (hA : 0 < A) (hℓ : 0 < ℓ) :
    0 < resistance σ A ℓ hσ := by
  unfold resistance
  positivity

end PhyslibExt.Circuits.UniformOhmicBar
