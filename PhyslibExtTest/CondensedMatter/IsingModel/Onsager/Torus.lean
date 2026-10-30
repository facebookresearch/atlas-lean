/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.Torus

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Onsager.Torus`

On the `3 × 3` torus `onsTorusGraph 3`:
* `(0, 0)` is adjacent to `(0, 1)`, `(0, 2)` (wrap-around), `(1, 0)` and `(2, 0)`, and not to the
  diagonal neighbour `(1, 1)`;
* `onsTorus_card_verts`, `onsTorus_degree`, `onsTorus_card_edges`: `9` sites, degree `4`, `18`
  edges; the edge count is also computed directly by `decide`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Onsager.Torus

open StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- Nearest neighbours of the origin on the `3 × 3` torus, including the wrap-around neighbours.
example : (onsTorusGraph 3).Adj (0, 0) (0, 1) ∧ (onsTorusGraph 3).Adj (0, 0) (0, 2) ∧
    (onsTorusGraph 3).Adj (0, 0) (1, 0) ∧ (onsTorusGraph 3).Adj (0, 0) (2, 0) := by
  decide

-- A diagonal pair is not adjacent.
example : ¬ (onsTorusGraph 3).Adj (0, 0) (1, 1) := by decide

-- `9` sites, degree `4`, `18 = 2 · 3²` edges.
example : Fintype.card (ZMod 3 × ZMod 3) = 9 ∧ (onsTorusGraph 3).degree (0, 0) = 4 ∧
    (onsTorusGraph 3).edgeFinset.card = 18 :=
  ⟨by rw [onsTorus_card_verts]; norm_num, onsTorus_degree 3 (0, 0),
    by rw [onsTorus_card_edges]; norm_num⟩

-- The edge count, computed directly.
example : (onsTorusGraph 3).edgeFinset.card = 18 := by decide

end PhyslibExtTest.CondensedMatter.IsingModel.Onsager.Torus
