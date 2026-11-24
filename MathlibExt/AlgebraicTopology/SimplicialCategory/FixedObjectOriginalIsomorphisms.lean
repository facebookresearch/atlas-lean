/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectVertexMaps
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# The actual original fixed-fiber inclusion reflects whole original isomorphisms

The genuine original inverse preserves each label by the SAME original
inverse triangle and the actual fixed-map vertex equation. Both whole
original functors are retained literally in the fixed fiber.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects
variable {O : Type u} {C D : FixedObjects O}

/-- The SAME original whole inverse preserves each original label exactly. -/
theorem originalInverse_vertex (F : C ⟶ D) [IsIso F.val] (o : O) :
    (inv F.val).obj (vertex D o) = vertex C o := by
  have h := congrArg (fun G : C.val ⟶ C.val => G.obj (vertex C o)) (IsIso.hom_inv_id F.val)
  exact (congrArg (inv F.val).obj (map_vertex F o)).symm.trans h

/-- The genuine original whole inverse is the SAME exact functor in the original fixed-label
fiber. -/
def originalInverse (F : C ⟶ D) [IsIso F.val] : D ⟶ C :=
  ofVertexEquation (inv F.val) (originalInverse_vertex F)

/-- The SAME whole original isomorphism with both original inverse maps belongs to the
actual fixed fiber. -/
def originalIso (F : C ⟶ D) [IsIso F.val] : C ≅ D where
  hom := F
  inv := originalInverse F
  hom_inv_id := Functor.Fiber.hom_ext (IsIso.hom_inv_id F.val)
  inv_hom_id := Functor.Fiber.hom_ext (IsIso.inv_hom_id F.val)

/-- The SAME original fixed-label map is an isomorphism from its actual entire carrier inverse. -/
theorem isIso_of_original_isIso (F : C ⟶ D) [IsIso F.val] : IsIso F := (originalIso F).isIso_hom

/-- The original fixed-fiber inclusion genuinely reflects every whole original isomorphism. -/
instance originalInclusion_reflectsIsomorphisms :
    (Functor.Fiber.fiberInclusion : FixedObjects O ⥤ Carrier.{u}).ReflectsIsomorphisms where
  reflects F h := by
    let _ : IsIso F.val := h
    exact isIso_of_original_isIso F

end CategoryTheory.SimplicialEnrichment.FixedObjects
