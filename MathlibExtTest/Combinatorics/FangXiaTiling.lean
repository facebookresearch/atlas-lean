/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.FangXiaTiling

open MathlibExt.Combinatorics.FangXiaTilingWanted.Combinatorics.FangXiaTilingProblem

-- In degree two, the identity and the unique transposition exhaust the group.
private theorem two_tiling : IsTiling (transpositionsWithOne 2) {1} := by
  have hall : ∀ g : Equiv.Perm (Fin 2), g = 1 ∨
      ∃ i j : Fin 2, i ≠ j ∧ g = Equiv.swap i j := by decide
  intro g
  refine ⟨⟨⟨g, hall g⟩, ⟨1, rfl⟩⟩, mul_one _, ?_⟩
  rintro ⟨x, y⟩ h
  have hy : y.val = 1 := y.property
  apply Prod.ext <;> apply Subtype.ext
  · simpa [hy] using h
  · exact hy

private def oneRow : PartitionShape 2 := ⟨[2], by decide, by decide, rfl⟩

example : IsPartitionTransitive {1} oneRow :=
  fang_xia_partition_transitive_of_tiling two_tiling oneRow (by decide)

-- Self-conjugate shapes have zero content, including the empty shape.
example : PartitionShape.contentSum (n := 3) ⟨[2, 1], by decide, by decide, rfl⟩ = 0 := rfl

example (Y : Set (Equiv.Perm (Fin 0))) (h : IsTiling (transpositionsWithOne 0) Y) :
    IsPartitionTransitive Y (⟨[], by decide, by decide, rfl⟩ : PartitionShape 0) :=
  fang_xia_partition_transitive_of_tiling h _ (by decide)

-- The column of height two lies strictly below the content cutoff.
example : PartitionShape.contentSum (n := 2) ⟨[1, 1], by decide, by decide, rfl⟩ = -2 := rfl
