/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.PracticalPolygonalSumsExistsPracticalAddTriangular

namespace MetaMathlibExt

-- At the positive lower endpoint, the triangular summand is zero.
example : IsPracticalNumber 1 ∧ 1 = 1 + Nat.polygonalNumber 3 0 := by
  refine ⟨isPracticalNumber_iff.mpr ⟨by decide, ?_⟩, by rw [Nat.polygonalNumber_zero]⟩
  intro m hm hle
  have : m = 1 := le_antisymm hle hm
  subst m
  exact ⟨{1}, by decide, by decide⟩

-- A positive triangular summand: 5 = 4 + 1, with the divisor sums of 4 checked explicitly.
example : IsPracticalNumber 4 ∧ 5 = 4 + Nat.polygonalNumber 3 1 := by
  refine ⟨isPracticalNumber_iff.mpr ⟨by decide, ?_⟩, by rw [Nat.polygonalNumber_one]⟩
  intro m hm hle
  interval_cases m
  · exact ⟨{1}, by decide, by decide⟩
  · exact ⟨{2}, by decide, by decide⟩
  · exact ⟨{1, 2}, by decide, by decide⟩
  · exact ⟨{4}, by decide, by decide⟩

-- The public theorem is usable without importing the old wanted module.
example : ∃ q k : ℕ, IsPracticalNumber q ∧ 5 = q + Nat.polygonalNumber 3 k :=
  exists_practical_add_triangular 5 (by decide)

end MetaMathlibExt
