/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerModelCategory
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerPointPresentability
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The same original terminal point and its full component lifting

The original object-forgetting/codiscrete adjunction proves that the
same original point is terminal. Its full original terminal map retains
the actual scalar maps to the tensor unit. Its component functor lifts
every isomorphism by the identity at the same source object.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.Bergner

/-- The SAME original global point is genuinely terminal through the original codiscrete right adjoint. -/
def pointIsTerminal : IsTerminal BergnerObjects.point.{u} := by
  let _ : CodiscreteEnrichment.functor.{u}.IsRightAdjoint :=
    CodiscreteEnrichment.adjunction.isRightAdjoint
  exact IsTerminal.isTerminalObj CodiscreteEnrichment.functor _
    (Types.isTerminalPUnit : IsTerminal PUnit.{u+1})

/-- The whole original terminal map retains its literal original object function and all unit Hom maps. -/
def toPoint (C : Carrier.{u}) : C ⟶ BergnerObjects.point.{u} :=
  CodiscreteEnrichment.extend C PUnit.{u+1} (↾fun _ => PUnit.unit)

/-- The entire original terminal Hom map is exactly the SAME scalar map to the tensor unit. -/
theorem toPoint_hom (C : Carrier.{u}) (x y : C) :
    (toPoint C).map x y = CodiscreteEnrichment.toUnit (x ⟶[SSet.{u}] y) := rfl

private theorem point_component_homs_subsingleton (x y : ComponentCategory.objects.{u} BergnerObjects.point.{u}) :
    Subsingleton (x ⟶ y) := by
  change Subsingleton (SSet.π₀ (𝟙_ SSet.{u}))
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective b
  cases x
  cases y
  rfl

/-- The SAME original point-map component functor genuinely lifts every isomorphism at the original source object. -/
theorem toPoint_component_isIsofibration (C : Carrier.{u}) :
    (ComponentCategory.mapFunctor (toPoint C)).IsIsofibration where
  exists_lift {X} {Y} g := by
    have h : (ComponentCategory.mapFunctor (toPoint C)).obj X = Y :=
      @Subsingleton.elim PUnit.{u+1} inferInstance _ _
    refine ⟨X, Iso.refl X, h, ?_⟩
    apply Iso.ext
    exact @Subsingleton.elim _ (point_component_homs_subsingleton _ _) _ _

end CategoryTheory.SimplicialEnrichment.Bergner
