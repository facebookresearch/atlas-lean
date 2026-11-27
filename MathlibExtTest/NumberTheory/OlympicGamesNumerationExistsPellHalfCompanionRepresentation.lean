/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OlympicGamesNumerationExistsPellHalfCompanionRepresentation

/-!
# Tests for Pell and half-companion Pell numeration

The representation theorem gives a bounded-digit expansion of the positive integer fifteen.
-/

namespace MathlibExtTest.NumberTheory.OlympicGamesNumerationExistsPellHalfCompanionRepresentation

open Finset MetaMathlibExt

example : ∃ (n : ℕ) (a : ℕ → ℕ), 1 ≤ n ∧
    15 = ∑ k ∈ Icc 1 n,
      a k * (if k % 2 = 1 then pellNumber k else pellLucasSequence k) ∧
    (∀ k, a (2 * k + 1) ≤ 3 ∧ a (2 * k) ≤ 1) := by
  obtain ⟨n, a, hn, _, _, hsum, _, _, hbound, _, _⟩ :=
    exists_pell_halfCompanion_representation
      (fun k ↦ if k % 2 = 1 then pellNumber k else pellLucasSequence k)
      (fun _ ↦ rfl) (t := 15) (by decide)
  exact ⟨n, a, hn, hsum, hbound⟩

end MathlibExtTest.NumberTheory.OlympicGamesNumerationExistsPellHalfCompanionRepresentation
