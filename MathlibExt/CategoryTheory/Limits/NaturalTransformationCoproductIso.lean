/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# General natural-transformation coproduct Arrow comparisons

Preservation maps a caller cofan to its actual image cofan. Naturality gives
the isomorphism between the coproduct of transformation components and the
component at the original coproduct point, retaining both Arrow maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w uD vD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {P Q : C ⥤ D} (α : P ⟶ Q) {J : Type w}
  [HasColimitsOfShape (Discrete J) D]
  [PreservesColimitsOfShape (Discrete J) P] [PreservesColimitsOfShape (Discrete J) Q]

/-- The pointwise Arrow of any natural transformation commutes with every actual caller
coproduct. -/
def coproductArrowIso (F : J → C) (c : Cofan F) (hc : IsColimit c) :
    Arrow.mk (Limits.Sigma.map (fun j => α.app (F j))) ≅ Arrow.mk (α.app c.pt) := by
  have cIso : c ≅ Cofan.mk c.pt (fun j => c.inj j) :=
    Cocone.ext (Iso.refl _) (fun j => by
      change c.ι.app j ≫ 𝟙 c.pt = c.inj j.as
      exact (CategoryTheory.Category.comp_id (c.ι.app j)).trans (by cases j; rfl))
  have hcMk : IsColimit (Cofan.mk c.pt (fun j => c.inj j) : Cofan F) :=
    IsColimit.ofIsoColimit hc cIso
  let imageP : Cofan (fun j => P.obj (F j)) :=
    Cofan.mk (P.obj c.pt) (fun j => P.map (c.inj j))
  have imagePIsColimit : IsColimit imageP :=
    isColimitCofanMkObjOfIsColimit P F (fun j => c.inj j) hcMk
  let eX : (∐ fun j => P.obj (F j)) ≅ P.obj c.pt :=
    (colimit.isColimit (Discrete.functor (fun j => P.obj (F j)))).coconePointUniqueUpToIso
      imagePIsColimit
  let image : Cofan (fun j => Q.obj (F j)) :=
    Cofan.mk (Q.obj c.pt) (fun j => Q.map (c.inj j))
  have imageIsColimit : IsColimit image :=
    isColimitCofanMkObjOfIsColimit Q F (fun j => c.inj j) hcMk
  let eY : (∐ fun j => Q.obj (F j)) ≅ Q.obj c.pt :=
    (colimit.isColimit (Discrete.functor (fun j => Q.obj (F j)))).coconePointUniqueUpToIso
      imageIsColimit
  refine Arrow.isoMk eX eY ?_
  apply Limits.Sigma.hom_ext
  intro j
  have hX : Limits.Sigma.ι (fun j => P.obj (F j)) j ≫ eX.hom = P.map (c.inj j) :=
    colimit.comp_coconePointUniqueUpToIso_hom imagePIsColimit (Discrete.mk j)
  have hY : Limits.Sigma.ι (fun j => Q.obj (F j)) j ≫ eY.hom = Q.map (c.inj j) :=
    colimit.comp_coconePointUniqueUpToIso_hom imageIsColimit (Discrete.mk j)
  calc
    Limits.Sigma.ι (fun j => P.obj (F j)) j ≫ eX.hom ≫ α.app c.pt = P.map (c.inj j)
      ≫ α.app c.pt := by
      rw [← CategoryTheory.Category.assoc, hX]
    _ = α.app (F j) ≫ Q.map (c.inj j) := α.naturality (c.inj j)
    _ = α.app (F j) ≫ Limits.Sigma.ι (fun j => Q.obj (F j)) j ≫ eY.hom := by rw [hY]
    _ = Limits.Sigma.ι (fun j => P.obj (F j)) j ≫ Limits.Sigma.map (fun j =>
      α.app (F j)) ≫ eY.hom := by
      rw [Limits.Sigma.ι_map_assoc]

/-- The forward source map sends every original coproduct injection to its preserved leg. -/
@[reassoc]
theorem coproductArrowIso_hom_left_injection
    (F : J → C) (c : Cofan F) (hc : IsColimit c) (j : J) :
    Limits.Sigma.ι (fun j => P.obj (F j)) j ≫ (coproductArrowIso α F c hc).hom.left =
      P.map (c.inj j) := by
  have cIso : c ≅ Cofan.mk c.pt (fun j => c.inj j) :=
    Cocone.ext (Iso.refl _) (fun j => by
      change c.ι.app j ≫ 𝟙 c.pt = c.inj j.as
      exact (Category.comp_id (c.ι.app j)).trans (by cases j; rfl))
  have hcMk : IsColimit (Cofan.mk c.pt (fun j => c.inj j) : Cofan F) :=
    IsColimit.ofIsoColimit hc cIso
  let image : Cofan (fun j => P.obj (F j)) :=
    Cofan.mk (P.obj c.pt) (fun j => P.map (c.inj j))
  have hImage : IsColimit image :=
    isColimitCofanMkObjOfIsColimit P F (fun j => c.inj j) hcMk
  change Limits.Sigma.ι (fun j => P.obj (F j)) j ≫
      ((colimit.isColimit (Discrete.functor (fun j => P.obj (F j)))).coconePointUniqueUpToIso
        hImage).hom = P.map (c.inj j)
  exact colimit.comp_coconePointUniqueUpToIso_hom hImage (Discrete.mk j)

/-- The forward target map sends every original coproduct injection to its preserved leg. -/
@[reassoc]
theorem coproductArrowIso_hom_right_injection
    (F : J → C) (c : Cofan F) (hc : IsColimit c) (j : J) :
    Limits.Sigma.ι (fun j => Q.obj (F j)) j ≫ (coproductArrowIso α F c hc).hom.right =
      Q.map (c.inj j) := by
  have cIso : c ≅ Cofan.mk c.pt (fun j => c.inj j) :=
    Cocone.ext (Iso.refl _) (fun j => by
      change c.ι.app j ≫ 𝟙 c.pt = c.inj j.as
      exact (Category.comp_id (c.ι.app j)).trans (by cases j; rfl))
  have hcMk : IsColimit (Cofan.mk c.pt (fun j => c.inj j) : Cofan F) :=
    IsColimit.ofIsoColimit hc cIso
  let image : Cofan (fun j => Q.obj (F j)) :=
    Cofan.mk (Q.obj c.pt) (fun j => Q.map (c.inj j))
  have hImage : IsColimit image :=
    isColimitCofanMkObjOfIsColimit Q F (fun j => c.inj j) hcMk
  change Limits.Sigma.ι (fun j => Q.obj (F j)) j ≫
      ((colimit.isColimit (Discrete.functor (fun j => Q.obj (F j)))).coconePointUniqueUpToIso
        hImage).hom = Q.map (c.inj j)
  exact colimit.comp_coconePointUniqueUpToIso_hom hImage (Discrete.mk j)

/-- The inverse source map takes each preserved leg back to its original coproduct injection. -/
@[reassoc]
theorem coproductArrowIso_inv_left_injection
    (F : J → C) (c : Cofan F) (hc : IsColimit c) (j : J) :
    P.map (c.inj j) ≫ (coproductArrowIso α F c hc).inv.left =
      Limits.Sigma.ι (fun j => P.obj (F j)) j := by
  rw [← coproductArrowIso_hom_left_injection α F c hc j, Category.assoc]
  have h := congrArg Arrow.Hom.left (coproductArrowIso α F c hc).hom_inv_id
  change (coproductArrowIso α F c hc).hom.left ≫ (coproductArrowIso α F c hc).inv.left = 𝟙 _ at h
  rw [h]
  change Limits.Sigma.ι (fun j => P.obj (F j)) j ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The inverse target map takes each preserved leg back to its original coproduct injection. -/
@[reassoc]
theorem coproductArrowIso_inv_right_injection
    (F : J → C) (c : Cofan F) (hc : IsColimit c) (j : J) :
    Q.map (c.inj j) ≫ (coproductArrowIso α F c hc).inv.right =
      Limits.Sigma.ι (fun j => Q.obj (F j)) j := by
  rw [← coproductArrowIso_hom_right_injection α F c hc j, Category.assoc]
  have h := congrArg Arrow.Hom.right (coproductArrowIso α F c hc).hom_inv_id
  change (coproductArrowIso α F c hc).hom.right ≫ (coproductArrowIso α F c hc).inv.right = 𝟙 _ at h
  rw [h]
  change Limits.Sigma.ι (fun j => Q.obj (F j)) j ≫ 𝟙 _ = _
  exact Category.comp_id _

end CategoryTheory.NatTrans
