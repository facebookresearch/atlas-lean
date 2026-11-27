/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Geometry.RichDistances

/-! # Tests for rich distances in the Euclidean plane -/

open Finset MathlibExt.Geometry.ErdosProblem756Wanted

namespace MathlibExtTest.Geometry.RichDistances

-- Two distinct points determine one unordered pair at their common distance.
example {x y : EuclideanSpace ℝ (Fin 2)} (hxy : x ≠ y) (k : ℕ) :
    dist x y ∈ richDistances {x, y} k ↔ k ≤ 1 := by
  classical
  have hoff : ({x, y} : Finset _).offDiag = {(x, y), (y, x)} := by
    ext ⟨a, b⟩
    simp only [mem_offDiag, mem_insert, mem_singleton, Prod.mk.injEq]
    grind
  have hd : dist x y ∈ distanceSet {x, y} := by
    exact mem_image.mpr ⟨(x, y), mem_offDiag.mpr ⟨by simp, by simp, hxy⟩, rfl⟩
  have hmult : distanceMultiplicity {x, y} (dist x y) = 1 := by
    simp [distanceMultiplicity, hoff, Finset.filter_insert, Finset.filter_singleton,
      dist_comm y x, hxy]
  simp [richDistances, hd, hmult]

-- The empty configuration realizes the maximum for zero points.
example : maxRichDistances 0 = 0 := by
  simp [maxRichDistances, richDistances, distanceSet]

-- At n = 4 the floor bound first requires a distance with positive multiplicity.
example : ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = 4 ∧
    ∃ d ∈ distanceSet A, 5 ≤ distanceMultiplicity A d := by
  obtain ⟨A, hA, hrich⟩ := conjecture_holds.2.1 4
  change 1 ≤ (richDistances A 5).card at hrich
  obtain ⟨d, hd⟩ := card_pos.mp hrich
  exact ⟨A, hA, d, mem_filter.mp hd⟩

end MathlibExtTest.Geometry.RichDistances
