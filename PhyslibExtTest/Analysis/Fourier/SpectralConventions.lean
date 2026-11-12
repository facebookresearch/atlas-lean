/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Analysis.Fourier.SpectralConventions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open PhyslibExt.Analysis.Fourier.SpectralConventions

namespace PhyslibExtTest.Analysis.Fourier.SpectralConventions

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

/-! ### Structure factor: sign-sensitive `ZMod 4` test -/

/-- A unit amplitude at position `1` of `ZMod 4`, evaluated at `k = 1`, gives
`-i`: the negative-exponent kernel of `ZMod.dft`, not the positive-exponent
value `i`. -/
example :
    structureFactor (fun _ : Fin 1 => (1 : ℂ)) ![1] (1 : ZMod 4) = -Complex.I := by
  have h1 : ZMod.stdAddChar (-(1 : ZMod 4)) = -Complex.I := by
    have h := ZMod.stdAddChar_coe (N := 4) (-1)
    rw [Int.cast_neg, Int.cast_one] at h
    rw [h, ← Complex.exp_neg_pi_div_two_mul_I]
    congr 1
    push_cast
    ring
  simp [structureFactor, h1]

/-! ### Two-site structure factor on `ZMod 2` -/

example :
    structureFactor (fun _ : Fin 2 => (3 : ℂ)) ![0, 1] (1 : ZMod 2) = 0 :=
  structureFactor_twoSite_cancel 3

example : structureFactor (fun _ : Fin 2 => (3 : ℂ)) ![0, 1] (0 : ZMod 2) =
    2 * 3 := by
  rw [structureFactor_eq_sum_amp_of_zero, Fin.sum_univ_two, two_mul]

example (a : ℂ) :
    structureFactor (fun _ : Fin 2 => a) ![0, 1] (0 : ZMod 2) = 2 * a := by
  rw [structureFactor_eq_sum_amp_of_zero, Fin.sum_univ_two, two_mul]

/-! ### Monatomic chain normal modes, `N = 6`, `K = m = 1` -/

example (K m : ℝ) (hm : 0 < m) (hK : 0 ≤ K) :
    chainNormalModeFrequency K m hm hK 6 0 = 0 :=
  chainNormalModeFrequency_zero K m hm hK 6

example : chainNormalModeFrequency 1 1 (by norm_num) (by norm_num) 6 4 =
    chainNormalModeFrequency 1 1 (by norm_num) (by norm_num) 6 2 :=
  chainNormalModeFrequency_symm 1 1 (by norm_num) (by norm_num) (j := 2) (hj := by norm_num)

example : 0 ≤ chainNormalModeFrequency 1 1 (by norm_num) (by norm_num) 6 2 :=
  chainNormalModeFrequency_nonneg 1 1 (by norm_num) (by norm_num) 6 2

example : chainNormalModeFrequency 1 1 (by norm_num) (by norm_num) 6 3 = 2 := by
  have harg : Real.pi * ((3 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = Real.pi / 2 := by
    push_cast
    ring
  simp only [chainNormalModeFrequency, harg, Real.sin_pi_div_two, div_one,
    Real.sqrt_one, abs_one, mul_one]

end PhyslibExtTest.Analysis.Fourier.SpectralConventions

#print axioms frequency_angularFrequency
#print axioms angularFrequency_frequency
#print axioms wavenumber_wavelength
#print axioms wavelength_wavenumber
#print axioms structureFactor_eq_sum_amp_of_zero
#print axioms structureFactor_twoSite_cancel
#print axioms chainNormalModeFrequency_zero
#print axioms chainNormalModeFrequency_nonneg
#print axioms chainNormalModeFrequency_symm
