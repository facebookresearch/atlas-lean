/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeLatchingColimit

/-!
# Genuine monomorphisms of original right-cube latching maps

The actual proper-injection colimit is the constructed support boundary.
The canonical whole map to the original cube is its inclusion after
that genuine colimit isomorphism, hence is a monomorphism in every
degree. Degree zero retains its literal empty colimit.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CoherentRealization.RightCubeLatchingMono
open RightCubeLatchingDiagram RightCubeSupportBoundary

/-- The canonical ambient cocone of the same original proper-injection diagram. -/
def ambient (n : ℕ) : Cocone (RightCubeLatchingDiagram.diagram.{u} n) where
  pt := RightCubeRelations.object n
  ι := (cocone n).ι ≫ (Functor.const _).map (boundary n).ι

/-- The original ambient cocone retains exactly each supplied proper-injection quotient map. -/
theorem ambient_app (n : ℕ) (a : (SimplicialObject.matchingIndex n)ᵒᵖ) :
    (ambient.{u} n).ι.app a = RightCubeCosimplicialMaps.map a.unop.obj.hom.unop := rfl

/-- The actual original latching map from the whole proper-injection colimit to the same original cube. -/
def latchingMap (n : ℕ) : colimit (RightCubeLatchingDiagram.diagram.{u} n) ⟶ RightCubeRelations.object.{u} n :=
  colimit.desc (RightCubeLatchingDiagram.diagram.{u} n) (ambient.{u} n)

/-- The genuine original colimit isomorphism from the actual latching object to the whole proper-support boundary. -/
def latchingIso (n : ℕ) : colimit (RightCubeLatchingDiagram.diagram.{u} n) ≅ (boundary.{u} n : SSet.{u}) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (RightCubeLatchingDiagram.diagram.{u} n))
    (RightCubeLatchingColimit.isColimit.{u} n)

/-- Every original proper-face inclusion is retained by the actual latching isomorphism. -/
theorem latchingIso_fac (n : ℕ) (a : (SimplicialObject.matchingIndex n)ᵒᵖ) :
    colimit.ι (RightCubeLatchingDiagram.diagram.{u} n) a ≫ (latchingIso n).hom = inclusion a.unop :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (RightCubeLatchingDiagram.diagram.{u} n))
    (RightCubeLatchingColimit.isColimit.{u} n) a

/-- The whole original latching map is exactly the actual support-boundary inclusion after its proved
  colimit isomorphism. -/
theorem iso_factor (n : ℕ) : (latchingIso.{u} n).hom ≫ (boundary n).ι = latchingMap n := by
  apply colimit.hom_ext
  intro a
  exact (Category.assoc (colimit.ι (RightCubeLatchingDiagram.diagram.{u} n) a) (latchingIso.{u} n).hom
    (boundary.{u} n).ι).symm.trans
    ((congrArg (fun f => f ≫ (boundary.{u} n).ι) (latchingIso_fac.{u} n a)).trans
      ((inclusion_ι.{u} a.unop).trans (colimit.ι_desc (ambient.{u} n) a).symm))

/-- Every actual original right-cube latching map is a whole simplicial monomorphism, including resolving
  degree zero. -/
theorem latchingMap_mono (n : ℕ) : Mono (latchingMap.{u} n) := by
  have h : Mono ((latchingIso.{u} n).hom ≫ (boundary n).ι) := inferInstance
  exact iso_factor n ▸ h

end CategoryTheory.CoherentRealization.RightCubeLatchingMono
