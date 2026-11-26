/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeometricSumsTwoSquaresAltBigeomPythagorean
import Mathlib.Tactic.NormNum

/-!
# Tests for alternating geometric sums as sums of coprime squares

Concrete instances give primitive representations of `13`, `205`, and `1`,
and classify the prime divisors of `205`.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and Franz Lemmermeyer,
"Geometric Sums as Sums of Two Squares", *INTEGERS* 26 (2026), Article A30
(<https://math.colgate.edu/~integers/vol26.html>).
-/

namespace MathlibExtTest.NumberTheory.GeometricSumsTwoSquaresAltBigeomPythagorean

open MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

example : ∃ a b : ℕ, (13 : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ∧ Nat.Coprime a b := by
  have h := (altBigeom_pythagorean 2 1 1 isCoprime_one_right (by decide)).2
  norm_num [Finset.sum_range_succ] at h
  exact h

example : ∃ a b : ℕ, (205 : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ∧ Nat.Coprime a b := by
  have h := (altBigeom_pythagorean 2 1 2 isCoprime_one_right (by decide)).2
  norm_num [Finset.sum_range_succ] at h
  exact h

example : ∃ a b : ℕ, (13 : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ∧ Nat.Coprime a b := by
  have h := (altBigeom_pythagorean (-2) 1 1 isCoprime_one_right (by decide)).2
  norm_num [Finset.sum_range_succ] at h
  exact h

example : ∃ a b : ℕ, (1 : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ∧ Nat.Coprime a b := by
  have h := (altBigeom_pythagorean 0 1 2 isCoprime_one_right (by decide)).2
  norm_num [Finset.sum_range_succ] at h
  exact h

example (q : ℕ) (hq : q.Prime) (hd : (q : ℤ) ∣ 205) : q = 2 ∨ q % 4 = 1 := by
  apply (altBigeom_pythagorean 2 1 2 isCoprime_one_right (by decide)).1 q hq
  norm_num [Finset.sum_range_succ]
  exact hd

end MathlibExtTest.NumberTheory.GeometricSumsTwoSquaresAltBigeomPythagorean
