/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.WilsonQuotientsExistsIntEqWilsonQuotientZPlusTwoMulAndModEq

/-! # Tests for the sign-adjusted Wilson quotient sum at even arguments -/

namespace MathlibExtTest.NumberTheory.WilsonQuotientsExistsIntEqWilsonQuotientZPlusTwoMulAndModEq

open MathlibExt.NumberTheory.WilsonQuotientsWanted

example : wilsonQuotientMPlus 1 4 = 1 / 4 := by
  norm_num [wilsonQuotientMPlus, Nat.factorial]

example : wilsonQuotientZPlus 3 = 2 := by
  norm_num [wilsonQuotientZPlus, wilsonQuotientMPlus, Finset.sum_range_succ, Nat.factorial]

example : ∃ z : ℤ, (z : ℚ) = wilsonQuotientZPlus 6 ∧ z ≡ 4 [ZMOD 6] := by
  obtain ⟨z, hz, _, hR⟩ :=
    exists_int_eq_wilsonQuotientZPlus_two_mul_and_modEq 3 (by decide)
  have hmod := hR ⟨Nat.prime_three, by decide⟩
  refine ⟨z, ?_, ?_⟩
  · simpa using hz
  · simpa using hmod

example : ∃ z : ℤ, (z : ℚ) = wilsonQuotientZPlus 12 ∧ z ≡ 0 [ZMOD 12] := by
  obtain ⟨z, hz, hQ, _⟩ :=
    exists_int_eq_wilsonQuotientZPlus_two_mul_and_modEq 6 (by decide)
  have hcomp : ¬(6 = 1 ∨ Nat.Prime 6) := by decide
  have hmod := hQ (Or.inr hcomp)
  refine ⟨z, ?_, ?_⟩
  · simpa using hz
  · simpa using hmod

end MathlibExtTest.NumberTheory.WilsonQuotientsExistsIntEqWilsonQuotientZPlusTwoMulAndModEq
