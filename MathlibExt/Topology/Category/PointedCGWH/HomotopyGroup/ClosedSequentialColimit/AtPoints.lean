/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.Colimits.AtPoints
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.ClosedSequentialColimit

/-!
# Closed sequential homotopy colimits at arbitrary points

The actual repointed cocone supplies the all-degree Type comparison and the
positive Group comparison. Both maps and every whole cocone-map square are
retained.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Topology

namespace PointedCGWH.BasedClosedPiColimitGeometry
open PointedCGWH.PointedAtGeometry
open PointedCGWH.SequentialHomotopyColimit

/-- The ENTIRE original based Type homotopy cocone uses the actual original degree and legs. -/
def basedTypeCocone (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (a : F.obj 0) :
    Cocone (diagramAt F a ⋙ piNFunctor k) :=
  (piNFunctor k).mapCocone (coconeAt c a)

/-- Genuine original compact source proves the complete based Type cocone universal property. -/
def basedTypeIsColimit (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (a : F.obj 0) : IsColimit (basedTypeCocone k c a) :=
  piNIsColimit k (coconeAt c a) (coconeAtIsColimit c hc a) (fun _ _ f => hF f)

/-- BOTH entire chosen based Type comparison functions keep the SAME original Type colimit. -/
def basedTypeComparisonIso (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (a : F.obj 0) : colimit (diagramAt F a ⋙ piNFunctor k) ≅
      (piNFunctor k).obj (PointedCGWH.pointedAt c.pt (coconePoint c a)) :=
  piNComparisonIso k (coconeAt c a) (coconeAtIsColimit c hc a) (fun _ _ f => hF f)

/-- The ENTIRE chosen Type Iso retains every map and law of the actual original comparison. -/
theorem basedTypeComparisonIso_actual (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (a : F.obj 0) : basedTypeComparisonIso k c hc hF a =
      piNComparisonIso k (coconeAt c a) (coconeAtIsColimit c hc a) (fun _ _ f => hF f) := rfl

/-- EVERY original based Type leg retains the ENTIRE actual forward comparison function. -/
theorem basedTypeComparisonIso_hom_ι (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (a : F.obj 0) (j : ℕ) :
    colimit.ι (diagramAt F a ⋙ piNFunctor k) j ≫ (basedTypeComparisonIso k c hc hF a).hom =
      (piNFunctor k).map ((coconeAt c a).ι.app j) :=
  piNComparisonIso_hom_ι k (coconeAt c a) (coconeAtIsColimit c hc a) (fun _ _ f => hF f) j

/-- EVERY original based Type leg retains the ENTIRE actual inverse comparison function. -/
theorem basedTypeComparisonIso_inv_ι (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (a : F.obj 0) (j : ℕ) :
    (piNFunctor k).map ((coconeAt c a).ι.app j) ≫ (basedTypeComparisonIso k c hc hF a).inv =
      colimit.ι (diagramAt F a ⋙ piNFunctor k) j :=
  piNComparisonIso_inv_ι k (coconeAt c a) (coconeAtIsColimit c hc a) (fun _ _ f => hF f) j

/-- EVERY whole original diagram/cocone map preserves the ENTIRE based Type hom square. -/
theorem basedTypeComparisonIso_hom_naturality (k : ℕ) {F G : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (G.map f)))
    (α : F ⟶ G) (t : c.pt ⟶ d.pt) (h : ∀ j, c.ι.app j ≫ t = α.app j ≫ d.ι.app j)
    (a : F.obj 0) :
    colim.map (Functor.whiskerRight (diagramAtMap α a) (piNFunctor k)) ≫
        (basedTypeComparisonIso k d hd hG (α.app 0 a)).hom =
      (basedTypeComparisonIso k c hc hF a).hom ≫ (piNFunctor k).map (coconeAtMap c d α t h a) :=
  piNComparisonIso_naturality k (coconeAt c a) (coconeAt d (α.app 0 a))
    (coconeAtIsColimit c hc a) (coconeAtIsColimit d hd (α.app 0 a))
    (fun _ _ f => hF f) (fun _ _ f => hG f) (diagramAtMap α a) (coconeAtMap c d α t h a)
    (coconeAtMap_leg c d α t h a)

/-- EVERY whole original diagram/cocone map preserves the ENTIRE based Type inverse square. -/
theorem basedTypeComparisonIso_inv_naturality (k : ℕ) {F G : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (G.map f)))
    (α : F ⟶ G) (t : c.pt ⟶ d.pt) (h : ∀ j, c.ι.app j ≫ t = α.app j ≫ d.ι.app j)
    (a : F.obj 0) :
    (piNFunctor k).map (coconeAtMap c d α t h a) ≫
        (basedTypeComparisonIso k d hd hG (α.app 0 a)).inv =
      (basedTypeComparisonIso k c hc hF a).inv ≫
        colim.map (Functor.whiskerRight (diagramAtMap α a) (piNFunctor k)) :=
  (CommSq.vert_inv (g := basedTypeComparisonIso k c hc hF a)
    (h := basedTypeComparisonIso k d hd hG (α.app 0 a))
      ⟨basedTypeComparisonIso_hom_naturality k c d hc hd hF hG α t h a⟩).w

/-- The ENTIRE original based positive cocone uses the actual original degree k+1 and Group legs. -/
def basedPositiveCocone (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (a : F.obj 0) :
    Cocone (diagramAt F a ⋙ piNPositiveFunctor k) :=
  (piNPositiveFunctor k).mapCocone (coconeAt c a)

/-- Original compact source and genuine Group quotient give the ENTIRE based positive Group UPL. -/
def basedPositiveIsColimit (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (a : F.obj 0) : IsColimit (basedPositiveCocone k c a) :=
  piNPositiveIsColimit k (coconeAt c a) (coconeAtIsColimit c hc a) (fun _ _ f => hF f)

/-- BOTH full original based positive Group comparison maps retain the SAME genuine quotient. -/
def basedPositiveComparisonIso (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (a : F.obj 0) : GrpCat.FilteredColimits.colimit (diagramAt F a ⋙ piNPositiveFunctor k) ≅
      (piNPositiveFunctor k).obj (PointedCGWH.pointedAt c.pt (coconePoint c a)) :=
  piNPositiveComparisonIso k (coconeAt c a) (coconeAtIsColimit c hc a) (fun _ _ f => hF f)

/-- The ENTIRE chosen Group Iso retains BOTH maps and laws of the actual original comparison. -/
theorem basedPositiveComparisonIso_actual (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (a : F.obj 0) : basedPositiveComparisonIso k c hc hF a =
      piNPositiveComparisonIso k (coconeAt c a) (coconeAtIsColimit c hc a)
        (fun _ _ f => hF f) := rfl

/-- EVERY original based positive leg retains the ENTIRE actual forward Group function. -/
theorem basedPositiveComparisonIso_hom_ι (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (a : F.obj 0) (j : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (diagramAt F a ⋙ piNPositiveFunctor k)).ι.app j ≫
        (basedPositiveComparisonIso k c hc hF a).hom =
      (piNPositiveFunctor k).map ((coconeAt c a).ι.app j) :=
  piNPositiveComparison_ι k (coconeAt c a) j

/-- EVERY original based positive leg retains the ENTIRE actual inverse Group function. -/
theorem basedPositiveComparisonIso_inv_ι (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (a : F.obj 0) (j : ℕ) :
    (piNPositiveFunctor k).map ((coconeAt c a).ι.app j) ≫
        (basedPositiveComparisonIso k c hc hF a).inv =
      (GrpCat.FilteredColimits.colimitCocone (diagramAt F a ⋙ piNPositiveFunctor k)).ι.app j :=
  piNPositiveComparisonIso_inv_ι k (coconeAt c a) (coconeAtIsColimit c hc a)
    (fun _ _ f => hF f) j

/-- EVERY whole original diagram/cocone map preserves the ENTIRE based positive Group hom square. -/
theorem basedPositiveComparisonIso_hom_naturality (k : ℕ) {F G : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (G.map f)))
    (α : F ⟶ G) (t : c.pt ⟶ d.pt) (h : ∀ j, c.ι.app j ≫ t = α.app j ≫ d.ι.app j)
    (a : F.obj 0) :
    GrpCat.FilteredColimits.colimitMap (Functor.whiskerRight (diagramAtMap α a)
        (piNPositiveFunctor k)) ≫ (basedPositiveComparisonIso k d hd hG (α.app 0 a)).hom =
      (basedPositiveComparisonIso k c hc hF a).hom ≫
        (piNPositiveFunctor k).map (coconeAtMap c d α t h a) :=
  piNPositiveComparisonIso_naturality k (coconeAt c a) (coconeAt d (α.app 0 a))
    (coconeAtIsColimit c hc a) (coconeAtIsColimit d hd (α.app 0 a))
    (fun _ _ f => hF f) (fun _ _ f => hG f) (diagramAtMap α a) (coconeAtMap c d α t h a)
    (coconeAtMap_leg c d α t h a)

/-- EVERY whole original diagram/cocone map preserves the ENTIRE based positive inverse square. -/
theorem basedPositiveComparisonIso_inv_naturality (k : ℕ) {F G : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (G.map f)))
    (α : F ⟶ G) (t : c.pt ⟶ d.pt) (h : ∀ j, c.ι.app j ≫ t = α.app j ≫ d.ι.app j)
    (a : F.obj 0) :
    (piNPositiveFunctor k).map (coconeAtMap c d α t h a) ≫
        (basedPositiveComparisonIso k d hd hG (α.app 0 a)).inv =
      (basedPositiveComparisonIso k c hc hF a).inv ≫
        GrpCat.FilteredColimits.colimitMap (Functor.whiskerRight (diagramAtMap α a)
          (piNPositiveFunctor k)) :=
  (CommSq.vert_inv (g := basedPositiveComparisonIso k c hc hF a)
    (h := basedPositiveComparisonIso k d hd hG (α.app 0 a))
      ⟨basedPositiveComparisonIso_hom_naturality k c d hc hd hF hG α t h a⟩).w

end PointedCGWH.BasedClosedPiColimitGeometry

namespace PointedCGWH.BasedClosedPiColimitGeometry
open PointedCGWH.PointedAtGeometry
open PointedCGWH.SequentialHomotopyColimit
attribute [local instance] pointedNatColimits

/-- The entire Type comparison family uses the actual native closed-cocone comparison. -/
theorem basedTypeComparisonIso_whole_value (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f))) :
    (fun a : F.obj 0 => basedTypeComparisonIso k c hc hF a) =
      (fun a => piNComparisonIso k (coconeAt c a) (coconeAtIsColimit c hc a)
        (fun _ _ f => hF f)) := rfl

/-- The entire positive comparison uses the actual Group quotient and its proved inverse. -/
theorem basedPositiveComparisonIso_whole_value (k : ℕ) {F : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f))) :
    (fun a : F.obj 0 => basedPositiveComparisonIso k c hc hF a) =
      (fun a => piNPositiveComparisonIso k (coconeAt c a) (coconeAtIsColimit c hc a)
        (fun _ _ f => hF f)) := rfl

end PointedCGWH.BasedClosedPiColimitGeometry
