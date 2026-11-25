/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.RationalSimplicialHomology

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared

-- The empty face gives the augmentation row, with coefficient one at a vertex.
example : boundaryMatrix {∅, {3}} 0 ⟨∅, by decide⟩ ⟨{3}, by decide⟩ = 1 := by
  decide +kernel

-- Erasing the second vertex of an edge contributes the negative sign.
example : boundaryMatrix ({1, 3} : Finset ℕ).powerset 1
    ⟨{1}, by decide⟩ ⟨{1, 3}, by decide⟩ = -1 := by decide +kernel

-- The link of a facet contains the empty face and has reduced Betti number one in degree -1.
example : link ({1, 3} : Finset ℕ).powerset {1, 3} = {∅} := by decide

example : reducedBetti {∅} 0 = 1 := by
  have hzero : boundaryMatrix {∅} 0 = 0 := by
    ext i j
    have h := Finset.mem_filter.mp j.property
    simp at h
    obtain ⟨hj, hcard⟩ := h
    simp [hj] at hcard
  rw [reducedBetti, hzero, Matrix.rank_zero]
  decide +kernel
