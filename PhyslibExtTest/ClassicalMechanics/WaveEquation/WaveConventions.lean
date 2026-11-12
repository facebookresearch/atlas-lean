/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions

namespace PhyslibExtTest.ClassicalMechanics.WaveEquation.WaveConventions

/-! ### Frequency, angular frequency, wavenumber, and wavelength -/

example : angularFrequency 440 = 880 * Real.pi := by
  unfold angularFrequency
  ring

example : frequency (880 * Real.pi) = 440 := by
  unfold frequency
  field_simp
  ring

example : wavenumber 500 = 2 * Real.pi / 500 := rfl

example : frequency (angularFrequency 440) = 440 :=
  frequency_angularFrequency 440

example : angularFrequency (frequency (880 * Real.pi)) = 880 * Real.pi :=
  angularFrequency_frequency (880 * Real.pi)

example : wavelength (wavenumber 500) = 500 :=
  wavelength_wavenumber (by norm_num)

example : wavenumber (wavelength (2 * Real.pi / 500)) = 2 * Real.pi / 500 :=
  wavenumber_wavelength (by positivity)

end PhyslibExtTest.ClassicalMechanics.WaveEquation.WaveConventions

#print axioms frequency_angularFrequency
#print axioms angularFrequency_frequency
#print axioms wavenumber_wavelength
#print axioms wavelength_wavenumber
