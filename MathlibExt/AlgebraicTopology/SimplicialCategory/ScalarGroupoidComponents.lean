/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategoryVertexLaws
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategoryFunctoriality

/-!
# Actual strict scalar inverses give original groupoid components

Every original component Hom class is represented by an original
zero-degree Hom vertex. If its SAME native scalar category is a groupoid,
that vertex has its actual original inverse. Original component identity
and composition readbacks prove both full inverse equations. No Kan
or completion weak outcome is assumed.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.SimplicialEnrichment.ComponentCategory
variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- The original zero-scalar native inverse represents an actual component-category inverse. -/
theorem arrowOf_isIso_of_scalarGroupoid [IsGroupoid (SSet.ScalarObject C (op ⦋0⦌))]
    {x y : C} (a : (x ⟶[SSet.{u}] y) _⦋0⦌) : IsIso (arrowOf C a) := by
  let f : SSet.ScalarObject.mk (Δ := op ⦋0⦌) x ⟶ SSet.ScalarObject.mk (Δ := op ⦋0⦌) y := a
  let b : (y ⟶[SSet.{u}] x) _⦋0⦌ := inv f
  refine ⟨⟨arrowOf C b, ?_, ?_⟩⟩
  · have he := IsIso.hom_inv_id f
    exact (arrowOf_composition C a b).trans
      ((congrArg (arrowOf C) he).trans (arrowOf_identity C x))
  · have he := IsIso.inv_hom_id f
    exact (arrowOf_composition C b a).trans
      ((congrArg (arrowOf C) he).trans (arrowOf_identity C y))

/-- The SAME original component category is a groupoid from actual original zero-scalar inverses. -/
theorem isGroupoid_of_zeroScalarGroupoid [IsGroupoid (SSet.ScalarObject C (op ⦋0⦌))] :
    IsGroupoid (objects.{u} C) where
  all_isIso {x y} a := by
    obtain ⟨v, hv⟩ := SSet.π₀.mk_surjective a
    rw [← hv]
    exact arrowOf_isIso_of_scalarGroupoid C v

end CategoryTheory.SimplicialEnrichment.ComponentCategory
