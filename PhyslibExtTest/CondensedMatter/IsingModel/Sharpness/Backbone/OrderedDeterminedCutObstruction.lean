/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.OrderedDeterminedCutObstruction

/-!
# Tests for `OrderedDeterminedCutObstruction`

Module under test:
`PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.OrderedDeterminedCutObstruction`.

* `shb_supportLex_not_local_to_acceptedPath`: two currents on `K₄` agreeing on the direct edge
  `03` with different support-lex selections (the counterexample is extracted);
* `shb_no_directEdge_local_characterization` (refutation): the selection is not a function of
  the direct edge alone.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone
namespace OrderedDeterminedCutObstruction

open _root_.StatMech.Sharpness

-- The counterexample pair exists.
example : ∃ A B, A ⊆ shbK4G ∧ B ⊆ shbK4G ∧ shbK4SelectsDirect03 A ∧ ¬ shbK4SelectsDirect03 B := by
  obtain ⟨A, B, hA, hB, -, -, -, hsA, hsB⟩ := shb_supportLex_not_local_to_acceptedPath
  exact ⟨A, B, hA, hB, hsA, hsB⟩

-- No local characterization through the direct edge.
example : ¬ ∃ q : Bool → Bool, ∀ A ⊆ shbK4G, shbK4Boundary A = {0, 3} →
    decide (shbK4SelectsDirect03 A) = q (decide (shbK4Edge.e03 ∈ A)) :=
  shb_no_directEdge_local_characterization

-- In particular the constant `true` rule fails.
example : ¬ ∀ A ⊆ shbK4G, shbK4Boundary A = {0, 3} → decide (shbK4SelectsDirect03 A) = true :=
  fun h => shb_no_directEdge_local_characterization ⟨fun _ => true, h⟩

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.OrderedDeterminedCutObstruction
