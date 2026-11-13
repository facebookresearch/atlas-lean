/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Optical mineralogy and anisotropy: phase retardation

## i. Overview

For a lossless two-mode slab with fixed orthogonal polarization modes
and constant refractive indices `n₁, n₂`, thickness `h ≥ 0` and vacuum
wavelength `lam > 0`, the phase retardation of mode 1 relative to mode 2
is `δ = k₀ * (n₁ - n₂) * h`, where `k₀ = 2 * π / lam` is the vacuum
wavenumber (`WaveConventions.wavenumber`, physics convention). So
`δ = 2 * π * (n₁ - n₂) * h / lam`, with `h, lam` lengths and `δ` in
radians.

Conventions: `lam` is the wavelength in vacuum, not inside the slab.
`δ` is a signed relative phase. In the physical domain (`h > 0`,
`lam > 0`) it is positive exactly when mode 1 is the slow mode
(`n₁ > n₂`), and it changes sign when the two modes are swapped. The
nonnegative retardance (slow minus fast) is `|δ|`, which equals `δ`
when `n₂ ≤ n₁`, `h ≥ 0` and `lam > 0`.

Domain: `phaseRetardation` is defined for all real arguments, but it is
the physical retardation only for `h ≥ 0` and `lam > 0`. Elsewhere it is
only an algebraic extension of the formula with no physical meaning:
Lean's division is total, so `lam = 0` gives `δ = 0`, and a negative `h`
or `lam` reverses the sign. The results below are identities of that
extension; they hold for all real arguments, in particular in the
physical domain. No absorption, dispersion, or full indicatrix
derivation is claimed. Degenerate axes are not unique; that is out of
scope.

## ii. Key results

- `EarthScience.phaseRetardation`: the signed phase retardation
  `δ = k₀ * (n₁ - n₂) * h`.
- `EarthScience.phaseRetardation_eq`: `δ = 2 * π * (n₁ - n₂) * h / lam`.
- `EarthScience.phaseRetardation_zero_thickness`: `δ = 0` when `h = 0`.
- `EarthScience.phaseRetardation_equal_indices`: `δ = 0` when `n₁ = n₂`.
- `EarthScience.phaseRetardation_example`: `n₁ = 3 / 2, n₂ = 1, h = 1,
  lam = 1` gives `δ = π`.

## iii. Table of contents

- A. Phase retardation
- B. Vanishing retardation and a non-vacuous example

## iv. References

- E. Hecht, *Optics*, 5th ed., Pearson (2017), Chapter 8 (Polarization),
  on retarders: a plate of thickness `d` whose two modes have indices
  `n_o, n_e` introduces the relative phase `(2π / λ₀) * d * |n_o - n_e|`,
  with `λ₀` the vacuum wavelength. This is `|δ|` above.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Phase retardation -/

/-- Signed phase retardation of mode 1 relative to mode 2 for a lossless
two-mode slab: `δ = k₀ * (n₁ - n₂) * h`, where `k₀ = 2 * π / lam` is the
vacuum wavenumber, `lam` the vacuum wavelength and `h` the thickness,
with `δ` in radians. It is the physical retardation only for `h ≥ 0` and
`lam > 0`, where `δ` is positive exactly when `h > 0` and mode 1 is the
slow mode (`n₁ > n₂`). For other real arguments it is only an algebraic
extension of the formula. -/
noncomputable def phaseRetardation (n₁ n₂ h lam : ℝ) : ℝ :=
  PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions.wavenumber lam * (n₁ - n₂) * h

/-- The phase retardation is `δ = 2 * π * (n₁ - n₂) * h / lam`. -/
lemma phaseRetardation_eq (n₁ n₂ h lam : ℝ) :
    phaseRetardation n₁ n₂ h lam = 2 * Real.pi * (n₁ - n₂) * h / lam := by
  unfold phaseRetardation PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions.wavenumber
  ring

/-! ## B. Vanishing retardation and a non-vacuous example -/

/-- `δ = 0` when the thickness `h` is `0`. -/
theorem phaseRetardation_zero_thickness (n₁ n₂ lam : ℝ) :
    phaseRetardation n₁ n₂ 0 lam = 0 := by
  simp [phaseRetardation]

/-- `δ = 0` when the two principal indices coincide (`n₁ = n₂`). -/
theorem phaseRetardation_equal_indices (n h lam : ℝ) :
    phaseRetardation n n h lam = 0 := by
  simp [phaseRetardation]

/-- Non-vacuous case: `n₁ = 3 / 2, n₂ = 1, h = 1, lam = 1` gives `δ = π`. -/
lemma phaseRetardation_example :
    phaseRetardation (3 / 2) 1 1 1 = Real.pi := by
  rw [phaseRetardation_eq]
  norm_num
  ring

end EarthScience
