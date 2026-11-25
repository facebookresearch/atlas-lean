/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.Quasicategory.TerminalVertexCriterion

/-!
# Original terminal points under ambient isomorphisms

The actual join-slice functor on structured targets transports an
ambient isomorphism to the original vertex over-slices. The original
projection maps then form an arrow isomorphism, preserving every boundary.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

variable {X Y : SSet.{u}}

/-- The original vertex over-slices under an actual ambient isomorphism. -/
def vertexSliceIso (c : (Δ[0] : SSet.{u}) ⟶ X) (e : X ≅ Y) :
    sliceOver X c ≅ sliceOver Y (c ≫ e.hom) := by
  let eU : Under.mk c ≅ Under.mk (c ≫ e.hom) := Under.isoMk e rfl
  exact (joinRightDivision (Δ[0] : SSet.{u})).mapIso eU

/-- The source comparison is the actual original over-slice map. -/
theorem vertexSliceIso_hom (c : (Δ[0] : SSet.{u}) ⟶ X) (e : X ≅ Y) :
    (vertexSliceIso c e).hom = sliceOver.map X c e.hom := rfl

/-- The original vertex projections are isomorphic as actual arrows. -/
def vertexProjectionArrowIso (c : (Δ[0] : SSet.{u}) ⟶ X) (e : X ≅ Y) :
    Arrow.mk (sliceOver.proj X c) ≅
      Arrow.mk (sliceOver.proj Y (c ≫ e.hom)) :=
  Arrow.isoMk (vertexSliceIso c e) e
    (by rw [vertexSliceIso_hom]; exact sliceOver.map_proj X c e.hom)

/-- Terminality of the given original point is unchanged by an ambient isomorphism. -/
theorem isTerminalVertex_iff_of_iso (c : (Δ[0] : SSet.{u}) ⟶ X) (e : X ≅ Y) :
    IsTerminalVertex c ↔ IsTerminalVertex (c ≫ e.hom) := by
  rw [isTerminalVertex_iff, isTerminalVertex_iff]
  apply forall_congr'
  intro m
  exact HasLiftingProperty.iff_of_arrow_iso_right (boundary m).ι
    (vertexProjectionArrowIso c e)

end SSet
