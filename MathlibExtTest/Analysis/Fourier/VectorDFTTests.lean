/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.VectorDFT
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExt.Analysis.Fourier.VectorDFTTests

def fourSamples : Vector ℂ 4 := ⟨#[1, 2, 3, 4], rfl⟩

example : fourSamples.toArray.getD 0 0 = 1 := rfl
example : fourSamples.toArray.getD 3 0 = 4 := rfl
example : fourSamples.toArray.getD 4 0 = 0 := rfl

theorem fourPositiveRoot : ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  rw [MathlibExt.Analysis.Fourier.FastFourierTransformWanted.stdAddChar_one_eq_exp]
  have angle : 2 * (Real.pi : ℂ) * Complex.I / ((4 : ℕ) : ℂ) =
      (Real.pi : ℂ) / 2 * Complex.I := by
    norm_num
    ring
  rw [angle, Complex.exp_pi_div_two_mul_I]

theorem fourNegativeRoot : ZMod.stdAddChar (-1 : ZMod 4) = -Complex.I := by
  rw [MathlibExt.Analysis.Fourier.FastFourierTransformWanted.stdAddChar_neg_one_eq_exp]
  have angle : -(2 * (Real.pi : ℂ) * Complex.I / ((4 : ℕ) : ℂ)) =
      -(Real.pi : ℂ) / 2 * Complex.I := by
    norm_num
    ring
  rw [angle, Complex.exp_neg_pi_div_two_mul_I]

theorem fourNegativeCoefficient :
    ZMod.dft (fun j : ZMod 4 => fourSamples.toArray.getD j.val 0) ((1 : ℕ) : ZMod 4) =
      -2 + 2 * Complex.I := by
  rw [← MathlibExt.Analysis.Fourier.FastFourierTransformWanted.dftSum_stdAddChar_neg_vector
    fourSamples 1, fourNegativeRoot]
  apply Complex.ext <;>
    norm_num [MathlibExt.Analysis.Fourier.FastFourierTransformWanted.dftSum,
      Finset.sum_range_succ, fourSamples, Array.getD, pow_succ]

theorem fourPositiveInverseCoefficient :
    ZMod.dft.symm (fun j : ZMod 4 => fourSamples.toArray.getD j.val 0)
      ((1 : ℕ) : ZMod 4) = (-2 - 2 * Complex.I) / 4 := by
  rw [← MathlibExt.Analysis.Fourier.FastFourierTransformWanted.invDFT_eq_dftSum_stdAddChar_vector
    fourSamples 1, fourPositiveRoot]
  apply Complex.ext <;>
    norm_num [MathlibExt.Analysis.Fourier.FastFourierTransformWanted.dftSum,
      Finset.sum_range_succ, fourSamples, Array.getD, pow_succ]

end MathlibExt.Analysis.Fourier.VectorDFTTests
