/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomColimit

/-!
# The SAME original Hom functor retains the whole actual filtered cocone

Each complete original coefficient leg is exactly the original enriched
cocone map under the original root. The genuine source-unit triangle
and its true original endpoints retain every map. The resulting
universal property belongs to the original functor's actual mapCocone.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalUnderHomColimit
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

variable {C : Carrier.{u}} {J : Type u} [Category.{u} J] [IsFiltered J]
  (U : J ⥤ Under C) (s : Cocone U) (hs : IsColimit s) (x y : C)

/-- Every full original coefficient leg is exactly the SAME original cocone Hom map under its root. -/
theorem homCocone_leg (i : J) :
    (homCocone U s hs x y).ι.app i = OriginalUnderHom.map C x y (s.ι.app i) := by
  let F := carrierDiagram U
  let c := carrierCocone U s
  let E := CarrierLabelDiagram.leg F (CarrierColimit.labelCocone F) i
  let R := CarrierColimit.rawLeg F c i
  let lx := rootLabel U s hs x
  let ly := rootLabel U s hs y
  let hx := rootLabel_target U s hs x
  let hy := rootLabel_target U s hs y
  have h := originalHomTriangle E R (s.ι.app i).right (CarrierColimit.rawLeg_fac F c i)
    ((U.obj i).hom.obj x) ((U.obj i).hom.obj y)
      (unit_endpoint U s hs i x) (unit_endpoint U s hs i y)
        ((CarrierColimit.rawLeg_obj F c i lx).trans hx)
        ((CarrierColimit.rawLeg_obj F c i ly).trans hy)
          (OriginalUnderHom.endpoint C (s.ι.app i) x) (OriginalUnderHom.endpoint C (s.ι.app i) y)
  let L := CarrierColimit.fixedLeg F c i
  let tu := congrArg₂ (fun a b : ((CarrierColimit.stages F).obj i).val => a ⟶[SSet.{u}] b)
    (unit_endpoint U s hs i x) (unit_endpoint U s hs i y)
  let tl := congrArg₂
    (fun a b : (CarrierReindexing.object c.pt (CarrierColimit.targetLabels F c)).val => a ⟶[SSet.{u}] b)
      (map_vertex L lx) (map_vertex L ly)
  let tt := congrArg₂ (fun a b : c.pt => a ⟶[SSet.{u}] b) hx hy
  let tr := congrArg₂ (fun a b : c.pt => a ⟶[SSet.{u}] b)
    ((CarrierColimit.rawLeg_obj F c i lx).trans hx) ((CarrierColimit.rawLeg_obj F c i ly).trans hy)
  let tc := congrArg₂ (fun a b : s.pt.right => a ⟶[SSet.{u}] b)
    (OriginalUnderHom.endpoint C (s.ι.app i) x) (OriginalUnderHom.endpoint C (s.ι.app i) y)
  change (E.map ((U.obj i).hom.obj x) ((U.obj i).hom.obj y) ≫ eqToHom tu) ≫
    (L.val.map (vertex ((CarrierColimit.stages F).obj i) lx)
      (vertex ((CarrierColimit.stages F).obj i) ly) ≫ eqToHom tl) ≫ eqToHom tt =
        (s.ι.app i).right.map ((U.obj i).hom.obj x) ((U.obj i).hom.obj y) ≫ eqToHom tc
  change E.map ((U.obj i).hom.obj x) ((U.obj i).hom.obj y) ≫ eqToHom tu ≫
    (L.val.map (vertex ((CarrierColimit.stages F).obj i) lx)
      (vertex ((CarrierColimit.stages F).obj i) ly) ≫ 𝟙 _) ≫ eqToHom tr =
        (s.ι.app i).right.map ((U.obj i).hom.obj x) ((U.obj i).hom.obj y) ≫ eqToHom tc at h
  have h' : (E.map ((U.obj i).hom.obj x) ((U.obj i).hom.obj y) ≫ eqToHom tu) ≫
      L.val.map (vertex ((CarrierColimit.stages F).obj i) lx)
        (vertex ((CarrierColimit.stages F).obj i) ly) ≫ eqToHom tr =
          (s.ι.app i).right.map ((U.obj i).hom.obj x) ((U.obj i).hom.obj y) ≫ eqToHom tc := by
    simpa only [Category.comp_id, Category.assoc] using h
  exact (combineTransports (E.map ((U.obj i).hom.obj x) ((U.obj i).hom.obj y) ≫ eqToHom tu)
    (L.val.map (vertex ((CarrierColimit.stages F).obj i) lx)
      (vertex ((CarrierColimit.stages F).obj i) ly)) tl tt tr).trans h'

/-- The actual original Hom functor's SAME full mapped cocone is genuinely colimiting. -/
def originalIsColimit
    (h : ∀ {i j : J} (f : i ⟶ j), Function.Injective (U.map f).right.obj) :
    IsColimit ((OriginalUnderHom.functor C x y).mapCocone s) :=
  IsColimit.ofIsoColimit (homIsColimit U s hs x y h)
    (Cocone.ext (Iso.refl _) (fun i => (Category.comp_id _).trans (homCocone_leg U s hs x y i)))

end CategoryTheory.SimplicialEnrichment.OriginalUnderHomColimit
