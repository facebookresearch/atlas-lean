/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.FavouriteDistancesFourSpaceErdosProblem754
import Mathlib.Data.Set.Card

namespace MathlibExtTest.Combinatorics.FavouriteDistancesFourSpaceErdosProblem754

open MathlibExt.Combinatorics.FavouriteDistancesFourSpaceErdosProblem754Wanted

private abbrev Point := EuclideanSpace ℝ (Fin 4)

example :
    ∃ C : ℝ, ∀ (A : Finset Point) (f : ℕ), A.Nonempty →
      (∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ f ≤ {y | y ∈ A ∧ dist x y = r}.ncard) →
        (f : ℝ) ≤ A.card / 2 + C :=
  favouriteDistanceCountHalfPlusConstant_holds

-- A positive radius excludes the sole point of a singleton.
example (x : Point) (r : ℝ) (hr : 0 < r) :
    {y | y ∈ ({x} : Finset Point) ∧ dist x y = r}.ncard = 0 := by
  have h : {y | y ∈ ({x} : Finset Point) ∧ dist x y = r} = ∅ := by
    ext y
    change (y ∈ ({x} : Finset Point) ∧ dist x y = r) ↔ False
    simp only [Finset.mem_singleton, iff_false]
    rintro ⟨rfl, hd⟩
    exact hr.ne' (hd.symm.trans (dist_self _))
  rw [h, Set.ncard_empty]

-- Either point of a pair has one neighbour at positive distance.
example (x y : Point) (hxy : x ≠ y) :
    ∀ z ∈ ({x, y} : Finset Point),
      ∃ r : ℝ, 0 < r ∧ 1 ≤ {w | w ∈ ({x, y} : Finset Point) ∧ dist z w = r}.ncard := by
  classical
  intro z hz
  have hf (r : ℝ) :
      {w | w ∈ ({x, y} : Finset Point) ∧ dist z w = r}.Finite :=
    (Finset.finite_toSet ({x, y} : Finset Point)).subset fun _ hw ↦ hw.1
  rcases Finset.mem_insert.mp hz with rfl | hy
  · exact ⟨dist z y, dist_pos.mpr hxy, (Set.ncard_pos (hf _)).mpr ⟨y, by simp⟩⟩
  · obtain rfl := Finset.mem_singleton.mp hy
    exact ⟨dist z x, dist_pos.mpr hxy.symm, (Set.ncard_pos (hf _)).mpr ⟨x, by simp⟩⟩

end MathlibExtTest.Combinatorics.FavouriteDistancesFourSpaceErdosProblem754
