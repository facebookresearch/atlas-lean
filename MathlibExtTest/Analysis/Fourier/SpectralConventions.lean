/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.SpectralConventions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open MathlibExt.Analysis.Fourier.SpectralConventions

namespace MathlibExtTest.Analysis.Fourier.SpectralConventions

/-! ### DFT normalization on `ZMod 4` -/

theorem dft_single_zero (k : ZMod 4) :
    ZMod.dft (Pi.single 0 1 : ZMod 4 → ℂ) k = 1 := by
  simp [ZMod.dft_apply, Pi.single_apply]

theorem normalizedDft_single_zero (k : ZMod 4) :
    normalizedDft (Pi.single 0 1 : ZMod 4 → ℂ) k = (4 : ℂ)⁻¹ := by
  simp [normalizedDft, dft_single_zero]

example : normalizedDft (Pi.single 0 1 : ZMod 4 → ℂ) 0 = (4 : ℂ)⁻¹ :=
  normalizedDft_single_zero 0

example : normalizedDft (Pi.single 0 1 : ZMod 4 → ℂ) 1 = (4 : ℂ)⁻¹ :=
  normalizedDft_single_zero 1

example : ZMod.dft.symm (Pi.single 0 1 : ZMod 4 → ℂ) (-1) = (4 : ℂ)⁻¹ := by
  rw [← normalizedDft_eq_invDFT_neg, normalizedDft_single_zero]

example : ZMod.dft ((3 : ℂ) • (Pi.single 0 1 : ZMod 4 → ℂ)) 1 = 3 := by
  rw [ZMod.dft_const_smul, Pi.smul_apply, dft_single_zero, smul_eq_mul, mul_one]

end MathlibExtTest.Analysis.Fourier.SpectralConventions

#print axioms normalizedDft_eq_invDFT_neg
