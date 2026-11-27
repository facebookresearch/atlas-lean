/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Percolation.BurtonKeane

/-! # Uniqueness of the infinite cluster at two specified sites -/

open MeasureTheory StatMech StatMech.Lattice StatMech.Percolation
open MathlibExt.Probability.Percolation.BurtonKeaneWanted
open scoped NNReal

-- Any two sites belonging to infinite clusters are almost surely connected.
example {d : ℕ} (p : ℝ≥0) (hp : p ≤ 1) (x y : Site d) :
    ∀ᵐ ω ∂(bernoulliProductMeasure (E := Sym2 (Site d)) p hp),
      (cluster d ω x).Infinite → (cluster d ω y).Infinite → Connected d ω x y := by
  filter_upwards [burton_keane_bernoulli d p hp] with ω hω
  intro hx hy
  have hsub := Set.encard_le_one_iff_subsingleton.mp hω
  have heq := hsub (show cluster d ω x ∈ infiniteClusters d ω from ⟨hx, x, rfl⟩)
    (show cluster d ω y ∈ infiniteClusters d ω from ⟨hy, y, rfl⟩)
  change y ∈ cluster d ω x
  rw [heq]
  exact self_mem_cluster ω y
