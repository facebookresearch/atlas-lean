/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2Quantitative

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2Quantitative`

* `shb_P2_current_factor` applied to a backbone path of a current with sources `{x, y}`;
* `shb_sources_removePath_eq_empty_of_select` applied to a selected path;
* `shb_backboneNum_eq_removeWalk_sum` and `shb_rho_eq_removeWalk_sum_div` (unconditional) for any
  path.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.P2Quantitative

open _root_.StatMech _root_.StatMech.Sharpness

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- Removing a backbone path leaves a sourceless current, and the weight factorizes.
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (β : ℝ) (J : Sym2 V → ℝ)
    (n : Current V) (x y : V) (p : IsBackbonePath G n x y) (hxy : x ≠ y)
    (hs : sources G n = {x, y}) : sources G (removeWalk n p.1) = ∅ :=
  (shb_P2_current_factor G β J p hxy hs).1

-- The same for a path chosen by the backbone selector.
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (n : Current V) (x y : V)
    (ω : G.Path x y) (hxy : x ≠ y) (hs : sources G n = {x, y})
    (hsel : shb_backboneSelect G n x y = some ω) : sources G (removeWalk n (ω : G.Walk x y)) = ∅ :=
  shb_sources_removePath_eq_empty_of_select G n ω hxy hs hsel

-- The backbone numerator and `ρ` as removed-walk sums.
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (β : ℝ) (J : Sym2 V → ℝ)
    (x y : V) (ω : G.Path x y) :=
  And.intro (shb_backboneNum_eq_removeWalk_sum G β J ω) (shb_rho_eq_removeWalk_sum_div G β J ω)

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.P2Quantitative
