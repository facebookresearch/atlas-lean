/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingPrimeGeometricSum
import Mathlib.Tactic.NormNum

/-! # Tests for alternating prime geometric sums -/

namespace MathlibExtTest.NumberTheory.AlternatingPrimeGeometricSum

open MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

example : ∃ a b : ℕ, (73 : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ∧ Nat.Coprime a b := by
  have h := (altGeomSum_pythagorean 3 2 (by decide) (by decide) ⟨1, rfl⟩ (by decide)).2
  norm_num [Finset.sum_range_succ] at h
  exact h

example : ∃ a b : ℕ, (6481 : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ∧ Nat.Coprime a b := by
  have h := (altGeomSum_pythagorean 3 4 (by decide) (by decide) ⟨2, rfl⟩ (by decide)).2
  norm_num [Finset.sum_range_succ] at h
  exact h

example (q : ℕ) (hq : q.Prime) (hd : (q : ℤ) ∣ 375601) : q = 2 ∨ q % 4 = 1 := by
  apply (altGeomSum_pythagorean 5 2 (by decide) (by decide) ⟨1, rfl⟩ (by decide)).1 q hq
  norm_num [Finset.sum_range_succ]
  exact hd

end MathlibExtTest.NumberTheory.AlternatingPrimeGeometricSum
