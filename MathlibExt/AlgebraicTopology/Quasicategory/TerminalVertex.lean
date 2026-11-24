/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc

/-!
# The intrinsic full-boundary terminal-vertex criterion

A terminal vertex extends every original simplex boundary whose original
last vertex is that point. This neutral predicate is shared with the
WalkingAdjunction API. Its native over-slice characterizations are in
TerminalVertexCriterion, proved by the existing cone/boundary comparison.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial
universe u

namespace SSet

/-- The full original last-vertex boundary-extension criterion. -/
def IsTerminalVertex {X : SSet.{u}} (t : (Δ[0] : SSet.{u}) ⟶ X) : Prop :=
  ∀ (n : ℕ) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X),
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫ boundary.ι (0 : Fin (n + 2)) ≫ b = t →
    ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ X, ∂Δ[n + 1].ι ≫ f = b

end SSet
