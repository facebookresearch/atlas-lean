/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EquivalenceLiftingTarget

/-!
# Public client for target-prescribed strict equivalence lifting

The given target is retained, and transport of the returned source
equality compares actual typed image edges. No source quasicategory
instance or homotopy-category isofibration is supplied.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory.EquivalenceLiftingTargetTest

/-- The target-prescribed client retains the explicit preimage equality
and transports the source of the actual image edge. -/
theorem exists_target_lift_with_edge_eq {X Y : SSet.{u}} {p : X ⟶ Y}
    [SSet.InnerFibration p] [SSet.Quasicategory Y]
    [SSet.HasStrictEquivalenceLifting p] {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (g : SSet.Edge y (p.app (op ⦋0⦌) x)) (hg : g.IsEquivalence) :
    ∃ (x' : X _⦋0⦌) (hx' : p.app (op ⦋0⦌) x' = y) (a : SSet.Edge x' x),
      a.IsEquivalence ∧ (a.map p).ofEq hx' rfl = g := by
  obtain ⟨x', hx', a, ha, hag⟩ :=
    SSet.HasStrictEquivalenceLifting.exists_lift_target (p := p) g hg
  exact ⟨x', hx', a, ha, SSet.Edge.ext hag⟩

end MathlibExtTest.AlgebraicTopology.Quasicategory.EquivalenceLiftingTargetTest
