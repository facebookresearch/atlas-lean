/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PracticalPolygonalSumsPracticalAddPolygonalExceptions
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic

/-!
# Tests for exceptions to sums of a practical number and polygonal numbers
-/

namespace MathlibExtTest.NumberTheory.PracticalPolygonalSumsPracticalAddPolygonalExceptions

open MetaMathlibExt

-- For 12-gonal numbers the exceptions are infinite, so at least one exists.
example : ∃ n : ℕ, 0 < n ∧
    ¬ ∃ q m : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber 12 m := by
  have hinf := (practical_add_polygonal_exceptions 12).1 ⟨by decide, Or.inl rfl⟩
  obtain ⟨n, hn⟩ := hinf.nonempty
  exact ⟨n, hn⟩

-- For a large index there is an exception: use `M = 1` and `t = S`.
example : ∃ S n : ℕ, 0 < n ∧
    ¬ ∃ q x y : ℕ, IsPracticalNumber q ∧
      n = q + Nat.polygonalNumber S x + Nat.polygonalNumber S y := by
  obtain ⟨S, hS⟩ := (practical_add_polygonal_exceptions 0).2 1
  obtain ⟨F, hFcard, hFmem⟩ := hS S le_rfl
  have hpos : 0 < F.card := by omega
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
  exact ⟨S, n, hFmem n hn⟩

end MathlibExtTest.NumberTheory.PracticalPolygonalSumsPracticalAddPolygonalExceptions
