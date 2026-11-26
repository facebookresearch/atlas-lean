/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitMoebiusFormula

/-!
# Tests for the Möbius function of the square-splitting convolution

Values at powers of two and the zeta-value corollary of the Euler product at `s = 2`.
-/

@[expose] public section

namespace MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitMoebiusFormula

open MetaMathlibExt

/-- `μ⋆(2) = -1`. -/
example (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    m 2 = -1 :=
  ((squareSplitMoebius_formula m hm).2.1 2 Nat.prime_two).1

/-- `μ⋆(4) = -1`. -/
example (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    m 4 = -1 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact ((squareSplitMoebius_formula m hm).2.1 2 Nat.prime_two).2.1

/-- `μ⋆(8) = 1`. -/
example (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    m 8 = 1 := by
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8]
  exact ((squareSplitMoebius_formula m hm).2.1 2 Nat.prime_two).2.2.1

/-- `μ⋆(16) = 0`. -/
example (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    m 16 = 0 := by
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16]
  exact ((squareSplitMoebius_formula m hm).2.1 2 Nat.prime_two).2.2.2 4 le_rfl

/-- At `s = 2`, the Dirichlet series equals `1 / (ζ(2) * ζ(4))`. -/
example (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    LSeries (fun n => m n) 2 = 1 / (riemannZeta 2 * riemannZeta 4) := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by
    have hre : (2 : ℂ).re = 2 := rfl
    rw [hre]
    norm_num
  have h := (squareSplitMoebius_formula m hm).2.2 2 hs
  have h22 : (2 : ℂ) * 2 = 4 := by norm_num
  rw [h22] at h
  exact h.2

end MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitMoebiusFormula
