/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Wave conventions for frequency and wavelength

Algebraic relations between frequency, angular frequency, wavenumber and wavelength.

## i. Overview

Frequency `ν`, angular frequency `ω`, wavenumber `k` and wavelength `λ` are related by the
physics convention `ω = 2πν` and `k = 2π / λ`, used throughout. The crystallographic
convention `k = 1 / λ` differs by `2π`; mixing the two produces a `2π` error, so `wavenumber`
is the physics `2π / λ` and not the crystallographic `1 / λ`.

These are algebraic relations between real numbers; no Fourier transform is claimed here.

Provenance: atlas roadmap R09 and R11; task MF15, target MF15.2.

## ii. Key results

- `PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions.angularFrequency` :
  angular frequency `ω = 2πν`.
- `PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions.frequency` :
  frequency `ν = ω / (2π)`.
- `PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions.wavenumber` :
  wavenumber `k = 2π / λ` (physics convention).
- `PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions.wavelength` :
  wavelength `λ = 2π / k`.
- `PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions.frequency_angularFrequency` :
  round-trip `frequency (angularFrequency ν) = ν`.
- `PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions.angularFrequency_frequency` :
  round-trip `angularFrequency (frequency ω) = ω`.
- `PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions.wavenumber_wavelength` :
  round-trip `wavenumber (wavelength k) = k` for `k ≠ 0`.
- `PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions.wavelength_wavenumber` :
  round-trip `wavelength (wavenumber lam) = lam` for `lam ≠ 0`.

## iii. Table of contents

- A. Frequency and angular frequency
- B. Wavenumber and wavelength

## iv. References

* D. J. Griffiths, *Introduction to Electrodynamics*, 4th ed., Cambridge University Press (2017),
  Section 9.1.2, for sinusoidal waves with `k = 2π/λ` and `ω = 2πν`.

-/

@[expose] public section

noncomputable section

namespace PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions

/-! ## A. Frequency and angular frequency -/

/-- Angular frequency `ω = 2πν` (physics convention). -/
def angularFrequency (ν : ℝ) : ℝ := 2 * Real.pi * ν

/-- Frequency `ν = ω / (2π)`. -/
def frequency (ω : ℝ) : ℝ := ω / (2 * Real.pi)

/-- Round-trip: `frequency (angularFrequency ν) = ν`. -/
lemma frequency_angularFrequency (ν : ℝ) :
    frequency (angularFrequency ν) = ν := by
  unfold frequency angularFrequency
  field_simp

/-- Round-trip: `angularFrequency (frequency ω) = ω`. -/
lemma angularFrequency_frequency (ω : ℝ) :
    angularFrequency (frequency ω) = ω := by
  unfold angularFrequency frequency
  field_simp

/-! ## B. Wavenumber and wavelength -/

/-- Wavenumber `k = 2π / λ` (physics convention; NOT the crystallographic `1/λ`). -/
def wavenumber (lam : ℝ) : ℝ := 2 * Real.pi / lam

/-- Wavelength `λ = 2π / k`. -/
def wavelength (k : ℝ) : ℝ := 2 * Real.pi / k

/-- Round-trip: `wavenumber (wavelength k) = k` for `k ≠ 0`. -/
lemma wavenumber_wavelength {k : ℝ} (hk : k ≠ 0) :
    wavenumber (wavelength k) = k := by
  unfold wavenumber wavelength
  field_simp

/-- Round-trip: `wavelength (wavenumber lam) = lam` for `lam ≠ 0`. -/
lemma wavelength_wavenumber {lam : ℝ} (hlam : lam ≠ 0) :
    wavelength (wavenumber lam) = lam := by
  unfold wavelength wavenumber
  field_simp

end PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions
