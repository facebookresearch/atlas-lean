/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.BondwiseOrderedExploration

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.BondwiseOrderedExploration`

* `shb_bondwiseOrderedTests` on the order `[1, 2, 3]`: the test at a bond reads the bond
  (`test_apply`), and an accepted bond lies in its determined cut (`accepted_mem_determinedCut`);
* `selects_iff_of_agreeOn_determinedTrace` for two configurations that agree everywhere;
* The bondwise reindexing route was removed with the vacuous selector API.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.BondwiseOrderedExploration

open _root_.StatMech _root_.StatMech.Sharpness
open _root_.StatMech.Sharpness.BackboneDeterminedCutSwitching

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

/-- The one-bond ordered tests along `[1, 2, 3]`. -/
def tests123 : shb_OrderedLocalTests ℕ ℕ := shb_bondwiseOrderedTests [1, 2, 3] (by decide)

-- The test at a bond reads that bond.
example (ω : ℕ → Bool) : tests123.test ω 2 = ω 2 :=
  shb_bondwiseOrderedTests.test_apply _ _ ω 2

-- An accepted bond is in its own determined cut.
example : 3 ∈ tests123.determinedCut 3 :=
  shb_bondwiseOrderedTests.accepted_mem_determinedCut _ _ 3

-- Selection only depends on the determined trace.
example {D B : Type*} [DecidableEq B] (X : shb_DynamicEdgeExploration D B) (ω : B → Bool) (d : D)
    (word : List B) :
    X.Selects (fun _ b => ω b) d word ↔ X.Selects (fun _ b => ω b) d word :=
  X.selects_iff_of_agreeOn_determinedTrace ω ω d word fun _ _ => rfl

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.BondwiseOrderedExploration
