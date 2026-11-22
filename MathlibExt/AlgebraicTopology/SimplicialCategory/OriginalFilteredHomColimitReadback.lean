/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredHomColimit

/-!
# Every full original filtered Hom-colimit leg is the SAME original cocone map

The genuine carrier-colimit cocone has its complete original enriched
legs. Their actual source-unit factorization and the two original cocone
endpoint equations identify each full Hom leg without replacing any map.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom
open FixedObjects

private theorem originalHomTriangle {A B C : Carrier.{u}} (E : A ⟶ B)
    (G : B ⟶ C) (H : A ⟶ C) (sq : E ≫ G = H) (a b : A)
    {x₀ x₁ : B} {z₀ z₁ : C}
    (hx₀ : E.obj a = x₀) (hx₁ : E.obj b = x₁)
    (hg₀ : G.obj x₀ = z₀) (hg₁ : G.obj x₁ = z₁)
    (hh₀ : H.obj a = z₀) (hh₁ : H.obj b = z₁) :
    E.map a b ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx₀ hx₁) ≫
      G.map x₀ x₁ ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) hg₀ hg₁) =
    H.map a b ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) hh₀ hh₁) := by
  have h := originalHomSquare E (𝟙 A) G H (sq.trans (Category.id_comp H).symm)
    a b hx₀ hx₁ rfl rfl hg₀ hg₁ hh₀ hh₁
  change E.map a b ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx₀ hx₁) ≫
    G.map x₀ x₁ ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) hg₀ hg₁) =
      𝟙 (a ⟶[SSet.{u}] b) ≫ eqToHom (congrArg₂ (fun x y : A => x ⟶[SSet.{u}] y) rfl rfl) ≫
        H.map a b ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) hh₀ hh₁) at h
  simpa only [eqToHom_refl, Category.id_comp] using h

private theorem combineTransports {A B C D E : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (p : C = D) (q : D = E) (r : C = E) :
    f ≫ (g ≫ eqToHom p) ≫ eqToHom q = f ≫ g ≫ eqToHom r := by
  simp only [Category.assoc, eqToHom_trans]

variable {J : Type u} [Category.{u} J] (F : J ⥤ Carrier.{u}) (s : Cocone F)
  (j : J) (x y : F.obj j)

/-- The original cocone leg as its complete original morphism under the SAME source. -/
def coconeUnderMap (a : Under j) :
    (sourceDiagram F j).obj a ⟶ Under.mk (s.ι.app j) :=
  Under.homMk (s.ι.app a.right) (s.w a.hom)

/-- The actual full original cocone Hom map is exactly the SAME full Hom-colimit leg. -/
theorem homCocone_leg (a : Under j) :
    (homCocone F s j x y).ι.app a =
      OriginalUnderHom.map (F.obj j) x y (coconeUnderMap F s j a) := by
  let U := CarrierLabelDiagram.leg F (CarrierColimit.labelCocone F) a.right
  let R := CarrierColimit.rawLeg F s a.right
  let lx := CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j x
  let ly := CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j y
  let hx := (congrFun (CarrierColimit.input_object_eq F s j) x).symm
  let hy := (congrFun (CarrierColimit.input_object_eq F s j) y).symm
  have h := originalHomTriangle U R (s.ι.app a.right)
    (CarrierColimit.rawLeg_fac F s a.right) (image F j a x) (image F j a y)
      (unit_endpoint F j a x) (unit_endpoint F j a y)
        ((CarrierColimit.rawLeg_obj F s a.right lx).trans hx)
        ((CarrierColimit.rawLeg_obj F s a.right ly).trans hy)
          (OriginalUnderHom.endpoint (F.obj j) (coconeUnderMap F s j a) x)
          (OriginalUnderHom.endpoint (F.obj j) (coconeUnderMap F s j a) y)
  let L := CarrierColimit.fixedLeg F s a.right
  let tu := congrArg₂ (fun b c : ((CarrierColimit.stages F).obj a.right).val => b ⟶[SSet.{u}] c)
    (unit_endpoint F j a x) (unit_endpoint F j a y)
  let tl := congrArg₂
    (fun b c : (CarrierReindexing.object s.pt (CarrierColimit.targetLabels F s)).val => b ⟶[SSet.{u}] c)
      (map_vertex L lx) (map_vertex L ly)
  let tt := congrArg₂ (fun b c : s.pt => b ⟶[SSet.{u}] c) hx hy
  let tr := congrArg₂ (fun b c : s.pt => b ⟶[SSet.{u}] c)
    ((CarrierColimit.rawLeg_obj F s a.right lx).trans hx)
    ((CarrierColimit.rawLeg_obj F s a.right ly).trans hy)
  let tc := congrArg₂ (fun b c : s.pt => b ⟶[SSet.{u}] c)
    (OriginalUnderHom.endpoint (F.obj j) (coconeUnderMap F s j a) x)
    (OriginalUnderHom.endpoint (F.obj j) (coconeUnderMap F s j a) y)
  change (U.map (image F j a x) (image F j a y) ≫ eqToHom tu) ≫
    (L.val.map (vertex ((CarrierColimit.stages F).obj a.right) lx)
      (vertex ((CarrierColimit.stages F).obj a.right) ly) ≫ eqToHom tl) ≫ eqToHom tt =
        (s.ι.app a.right).map (image F j a x) (image F j a y) ≫ eqToHom tc
  change U.map (image F j a x) (image F j a y) ≫ eqToHom tu ≫
    (L.val.map (vertex ((CarrierColimit.stages F).obj a.right) lx)
      (vertex ((CarrierColimit.stages F).obj a.right) ly) ≫ 𝟙 _) ≫ eqToHom tr =
        (s.ι.app a.right).map (image F j a x) (image F j a y) ≫ eqToHom tc at h
  have h' : (U.map (image F j a x) (image F j a y) ≫ eqToHom tu) ≫
      L.val.map (vertex ((CarrierColimit.stages F).obj a.right) lx)
        (vertex ((CarrierColimit.stages F).obj a.right) ly) ≫ eqToHom tr =
          (s.ι.app a.right).map (image F j a x) (image F j a y) ≫ eqToHom tc := by
    simpa only [Category.comp_id, Category.assoc] using h
  exact (combineTransports (U.map (image F j a x) (image F j a y) ≫ eqToHom tu)
    (L.val.map (vertex ((CarrierColimit.stages F).obj a.right) lx)
      (vertex ((CarrierColimit.stages F).obj a.right) ly)) tl tt tr).trans h'

end CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom
