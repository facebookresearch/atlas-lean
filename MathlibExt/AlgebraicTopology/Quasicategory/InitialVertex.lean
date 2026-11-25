/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.Quasicategory.TerminalVertex
public import MathlibExt.AlgebraicTopology.SimplicialSet.OppositeSimplex

/-!
# Intrinsic initial vertices

An initial vertex satisfies the dual of the full-boundary terminal condition:
reverse the original simplicial set and the given point, then extend every
boundary ending at that point. Every dimension of the original simplicial set
is retained. The under-slice characterization is proved in InitialVertexCriterion.

This is the dual condition of Higher Topos Theory, Definition 1.2.12.3 and
Remark 1.2.12.6.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

/-- Initiality is the full original terminal boundary condition after order reversal. -/
def IsInitialVertex {X : SSet.{u}} (x : (Δ[0] : SSet.{u}) ⟶ X) : Prop :=
  IsTerminalVertex (oppositeVertex x)

/-- The dual condition uses the same original point and all original boundary dimensions. -/
theorem isInitialVertex_iff_isTerminalVertex_opposite {X : SSet.{u}}
    (x : (Δ[0] : SSet.{u}) ⟶ X) :
    IsInitialVertex x ↔ IsTerminalVertex (oppositeVertex x) :=
  Iff.rfl


end SSet
