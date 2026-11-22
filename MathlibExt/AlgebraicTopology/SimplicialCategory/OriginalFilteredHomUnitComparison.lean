/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredUnderHomDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedOriginalHomSquare
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalInjectiveLabelUnitHoms
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierFilteredObjectInjections

/-!
# The full original filtered-tail Hom diagram has its SAME original unit comparison

The original objects are transported along their complete original
indexing arrows. Their actual colimit labels agree by the original
object cocone. The SAME full original source units give a natural
coefficient comparison and are isomorphisms when stage objects inject.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom
open FixedObjects

variable {J : Type u} [Category.{u} J] (F : J ⥤ Carrier.{u}) (j : J) (x y : F.obj j)

/-- The SAME original endpoint transported by the actual indexing arrow. -/
abbrev image (a : Under j) (z : F.obj j) := (F.map a.hom).obj z

/-- The actual original object cocone retains precisely the SAME source label. -/
theorem image_label (a : Under j) (z : F.obj j) :
    CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) a.right (image F j a z) =
      CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j z :=
  ConcreteCategory.congr_hom (C := Type u) ((CarrierColimit.labelCocone F).w a.hom) z

/-- The SAME actual source unit maps the transported endpoint to exactly its original colimit label. -/
theorem unit_endpoint (a : Under j) (z : F.obj j) :
    (CarrierLabelDiagram.leg F (CarrierColimit.labelCocone F) a.right).obj (image F j a z) =
      vertex ((CarrierColimit.stages F).obj a.right)
        (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j z) :=
  (CarrierLabelExtension.inclusion_obj (F.obj a.right)
    (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) a.right) (image F j a z)).trans
      (congrArg (vertex ((CarrierColimit.stages F).obj a.right)) (image_label F j a z))

/-- The actual full fixed-label coefficient diagram on the SAME original under-source tail. -/
def unitHomDiagram : Under j ⥤ SSet.{u} :=
  Under.forget j ⋙ CarrierColimit.stages F ⋙
    FixedObjects.evaluation (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j x)
      (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j y)

/-- The SAME complete original unit Hom map with only its two true endpoint-label equations. -/
def unitHomMap (a : Under j) : (homDiagram F j x y).obj a ⟶ (unitHomDiagram F j x y).obj a :=
  (CarrierLabelDiagram.leg F (CarrierColimit.labelCocone F) a.right).map (image F j a x) (image F j a y) ≫
    eqToHom (congrArg₂ (fun b c : ((CarrierColimit.stages F).obj a.right).val => b ⟶[SSet.{u}] c)
      (unit_endpoint F j a x) (unit_endpoint F j a y))

/-- The complete original source squares give naturality of the SAME full original coefficient comparison. -/
theorem unitHomMap_naturality {a b : Under j} (f : a ⟶ b) :
    (homDiagram F j x y).map f ≫ unitHomMap F j x y b =
      unitHomMap F j x y a ≫ (unitHomDiagram F j x y).map f := by
  let E := CarrierLabelDiagram.leg F (CarrierColimit.labelCocone F) a.right
  let E' := CarrierLabelDiagram.leg F (CarrierColimit.labelCocone F) b.right
  let G := (CarrierColimit.stages F).map f.right
  exact (originalHomSquare E (F.map f.right) G.val E'
    (CarrierLabelDiagram.leg_naturality F (CarrierColimit.labelCocone F) f.right)
      (image F j a x) (image F j a y)
        (unit_endpoint F j a x) (unit_endpoint F j a y)
          (OriginalUnderHom.endpoint (F.obj j) ((sourceDiagram F j).map f) x)
          (OriginalUnderHom.endpoint (F.obj j) ((sourceDiagram F j).map f) y)
            (map_vertex G (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j x))
            (map_vertex G (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j y))
              (unit_endpoint F j b x) (unit_endpoint F j b y)).symm

/-- The SAME entire original unit coefficient comparison on every actual under-source object. -/
def unitHomComparison : homDiagram F j x y ⟶ unitHomDiagram F j x y where
  app := unitHomMap F j x y
  naturality _a _b f := unitHomMap_naturality F j x y f

/-- Each SAME complete original unit coefficient is invertible from the actual original stage object injectivity. -/
theorem unitHomMap_isIso [IsFiltered J]
    (h : ∀ {a b : J} (f : a ⟶ b), Function.Injective (F.map f).obj) (a : Under j) :
    IsIso (unitHomMap F j x y a) := by
  let U := CarrierLabelDiagram.leg F (CarrierColimit.labelCocone F) a.right
  let _ : IsIso (U.map (image F j a x) (image F j a y)) :=
    CarrierLabelExtension.inclusion_hom_isIso (F.obj a.right)
      (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) a.right)
        (CarrierColimit.label_injective F h a.right) _ _
  let t := congrArg₂ (fun b c : ((CarrierColimit.stages F).obj a.right).val => b ⟶[SSet.{u}] c)
    (unit_endpoint F j a x) (unit_endpoint F j a y)
  let T : (U.obj (image F j a x) ⟶[SSet.{u}] U.obj (image F j a y)) ≅
      (unitHomDiagram F j x y).obj a := eqToIso t
  let _ : IsIso T.hom := T.isIso_hom
  exact inferInstanceAs (IsIso (U.map (image F j a x) (image F j a y) ≫ T.hom))

/-- The actual full original unit comparison is a genuine natural isomorphism at all original stage Homs. -/
def unitHomIso [IsFiltered J]
    (h : ∀ {a b : J} (f : a ⟶ b), Function.Injective (F.map f).obj) :
    homDiagram F j x y ≅ unitHomDiagram F j x y :=
  NatIso.ofComponents
    (fun a => @asIso SSet.{u} inferInstance ((homDiagram F j x y).obj a)
      ((unitHomDiagram F j x y).obj a) (unitHomMap F j x y a) (unitHomMap_isIso F j x y h a))
    (fun {_a _b} f => unitHomMap_naturality F j x y f)

end CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom
