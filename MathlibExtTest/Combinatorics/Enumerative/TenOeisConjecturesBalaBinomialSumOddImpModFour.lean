/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Enumerative.TenOeisConjecturesBalaBinomialSumOddImpModFour
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Connected.Clopen
import MathlibExt.Combinatorics.AP.Basic
import MathlibExt.Combinatorics.Enumerative.FriedAlternatingBinomialIdentity
import MathlibExt.Combinatorics.Enumerative.RepeatingDecimalRatio
import MathlibExt.Combinatorics.Enumerative.TriangularNearSquareBeattySqrtTwo

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.TenOeisConjecturesBalaBinomialSumOddImpModFour` -/

namespace MathlibExtTest.Combinatorics.Enumerative.TenOeisConjecturesBalaBinomialSumOddImpModFour

open MetaMathlibExt

/-- Bala's binomial sum `a(n) = ∑ k ∈ range (n+1), C(2n+1,n+k+1)·(-2)^k`. -/
private def bala (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (n + k + 1) : ℤ) * (-2) ^ k

-- Values: `a(0) = 1`, `a(1) = 1`, `a(3) = 13` are odd, while `a(2) = 4` is even.
example : bala 0 = 1 ∧ bala 1 = 1 ∧ bala 3 = 13 ∧ bala 2 = 4 := by
  simp only [bala]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- The odd values `a(0)`, `a(1)`, `a(3)` are `1` modulo `4`, by the theorem.
example : bala 0 % 4 = 1 := bala_binomial_sum_odd_imp_mod_four 0 (by decide)

example : bala 1 % 4 = 1 := bala_binomial_sum_odd_imp_mod_four 1 (by decide)

example : bala 3 % 4 = 1 := bala_binomial_sum_odd_imp_mod_four 3 (by decide)

-- The hypothesis is nontrivial: `a(2) = 4` is even, so the theorem does not apply at `n = 2`.
example : ¬Odd (bala 2) := by decide

-- Corollary: `a(3) - 1` is a multiple of `4`.
example : (4 : ℤ) ∣ bala 3 - 1 := by
  have h1 : bala 3 = 13 := by decide
  have h2 : bala 3 % 4 = 1 := bala_binomial_sum_odd_imp_mod_four 3 (by decide)
  omega

end MathlibExtTest.Combinatorics.Enumerative.TenOeisConjecturesBalaBinomialSumOddImpModFour
