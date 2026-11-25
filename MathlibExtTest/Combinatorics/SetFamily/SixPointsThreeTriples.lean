/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.SixPointsThreeTriples
import Mathlib.Data.Fintype.Card

/-! # Tests for the (6, 3) extremal number -/

namespace MathlibExtTest.SixPointsThreeTriples

open Finset Filter Topology
open MathlibExt.Combinatorics.SixPointsThreeTriplesErdosProblem716Wanted

-- Fewer than three vertices cannot support a triple.
example (n : ℕ) (hn : n < 3) : sixThreeExtremalNumber n = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold sixThreeExtremalNumber
  apply csSup_le'
  rintro _ ⟨E, h3, -, rfl⟩
  by_contra! h
  obtain ⟨T, hT⟩ := card_pos.mp h
  have hle := card_le_univ T
  rw [h3 T hT, Fintype.card_fin] at hle
  omega

-- On four vertices, two triples sharing a pair attain the upper bound.
example : sixThreeExtremalNumber 4 = 2 := by
  unfold sixThreeExtremalNumber
  apply IsGreatest.csSup_eq
  constructor
  · let E : Finset (Finset (Fin 4)) := {{0, 1, 2}, {0, 1, 3}}
    refine ⟨E, ?_, ?_, ?_⟩
    · decide
    · intro S _
      exact (card_filter_le _ _).trans (by decide : E.card ≤ 2)
    · decide
  · rintro _ ⟨E, -, hfree, rfl⟩
    simpa using hfree univ (by simp)

example : Tendsto (fun n : ℕ => (sixThreeExtremalNumber n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0) :=
  sixThreeExtremalNumberLittleO_holds

end MathlibExtTest.SixPointsThreeTriples
