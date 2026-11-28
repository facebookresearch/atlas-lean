/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitConvInverseOfIsMultiplicative
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# Tests for the square-splitting inverse of a multiplicative function

The inverse of the constant-one function under the square-splitting convolution
takes the values $-1$, $-1$ and $1$ at $p$, $p^2$ and $p^3$ for every prime $p$.
-/

@[expose] public section

namespace MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitConvInverseOfIsMultiplicative

open MetaMathlibExt

theorem zeta_inv_prime_vals {p : ℕ} (hp : p.Prime) :
    ∃ g : ArithmeticFunction ℂ,
      squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) g = 1 ∧
      g p = -1 ∧ g (p ^ 2) = -1 ∧ g (p ^ 3) = 1 := by
  have hzeta : ((ArithmeticFunction.zeta : ArithmeticFunction ℂ)).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  obtain ⟨g, hfg, -, -, -, -, hvals⟩ := squareSplitConv_inverse_of_isMultiplicative hzeta
  obtain ⟨hgp, hgp2, hgp3⟩ := hvals p hp
  have hz1 : (ArithmeticFunction.zeta : ArithmeticFunction ℂ) 1 = (1:ℂ) := by
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne one_ne_zero, Nat.cast_one]
  have hzp : (ArithmeticFunction.zeta : ArithmeticFunction ℂ) p = (1:ℂ) := by
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hp.ne_zero, Nat.cast_one]
  have hzp2 : (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ 2) = (1:ℂ) := by
    rw [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne (pow_ne_zero 2 hp.ne_zero), Nat.cast_one]
  have hzp3 : (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ 3) = (1:ℂ) := by
    rw [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne (pow_ne_zero 3 hp.ne_zero), Nat.cast_one]
  have hgp' : g p = -1 := by
    rw [hzp, hz1] at hgp
    simpa using hgp
  have hgp2' : g (p ^ 2) = -1 := by
    rw [hzp2, hz1] at hgp2
    simpa using hgp2
  have hgp3' : g (p ^ 3) = 1 := by
    rw [hzp, hzp2, hzp3, hz1] at hgp3
    have hnum : (2:ℂ) * 1 * 1 - 1 * 1 = 1 := by ring
    rw [hnum] at hgp3
    simpa using hgp3
  exact ⟨g, hfg, hgp', hgp2', hgp3'⟩

end MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitConvInverseOfIsMultiplicative
