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

public import MathlibExt.Algebra.Category.Grp.FilteredUnderlyingTypeColimit

/-!
# Source Type diagrams and the actual filtered group quotient

A genuine natural comparison of a group-valued functor with a Type-valued
functor induces the corresponding comparison on every natural-number
diagram. Both original colimit legs and all diagram maps are retained.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC v

open CategoryTheory CategoryTheory.Limits

namespace GrpCat.FilteredColimits

private theorem inverseSquare {A A' B B' : Type v} (a : A ≅ A') (b : B ≅ B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : f ≫ b.hom = a.hom ≫ g) :
    g ≫ b.inv = a.inv ≫ f :=
  ((a.inv_comp_eq).mpr
    (((b.comp_inv_eq).mpr h.symm).symm.trans (Category.assoc _ _ _))).symm

variable {C : Type uC} [Category.{vC} C]
  (F : C ⥤ GrpCat.{v}) (G : C ⥤ Type v) (e : F ⋙ forget GrpCat.{v} ≅ G)

/-- The original natural comparison, whiskered along the actual input diagram. -/
def sourceTypeDiagramIso (D : ℕ ⥤ C) :
    D ⋙ G ≅ (D ⋙ F) ⋙ forget GrpCat.{v} :=
  Functor.isoWhiskerLeft D e.symm ≪≫ (Functor.associator D F (forget GrpCat.{v})).symm

/-- Its forward leg uses the original inverse source-comparison component. -/
theorem sourceTypeDiagramIso_hom_app (D : ℕ ⥤ C) (n : ℕ) :
    (sourceTypeDiagramIso F G e D).hom.app n = e.inv.app (D.obj n) := by
  simp only [sourceTypeDiagramIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Category.comp_id]

/-- Its inverse leg uses the same original forward source-comparison component. -/
theorem sourceTypeDiagramIso_inv_app (D : ℕ ⥤ C) (n : ℕ) :
    (sourceTypeDiagramIso F G e D).inv.app n = e.hom.app (D.obj n) := by
  simp only [sourceTypeDiagramIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp]

/-- The complete chosen source Type colimit is the underlying original group colimit. -/
def sourceTypeColimitIso (D : ℕ ⥤ C) :
    CategoryTheory.Limits.colimit (D ⋙ G) ≅
      (forget GrpCat.{v}).obj (GrpCat.FilteredColimits.colimit (D ⋙ F)) :=
  colim.mapIso (sourceTypeDiagramIso F G e D) ≪≫ underlyingTypeColimitIso (D ⋙ F)

/-- Every Type leg reaches its original group leg through the given source comparison. -/
@[reassoc]
theorem sourceTypeColimitIso_ι_hom (D : ℕ ⥤ C) (n : ℕ) :
    CategoryTheory.Limits.colimit.ι (D ⋙ G) n ≫ (sourceTypeColimitIso F G e D).hom =
      e.inv.app (D.obj n) ≫ (forget GrpCat.{v}).map ((colimitCocone (D ⋙ F)).ι.app n) := by
  change CategoryTheory.Limits.colimit.ι (D ⋙ G) n ≫
      colim.map (sourceTypeDiagramIso F G e D).hom ≫
        (underlyingTypeColimitIso (D ⋙ F)).hom = _
  erw [CategoryTheory.Limits.colimit.ι_map_assoc, underlyingTypeColimitIso_ι_hom,
    sourceTypeDiagramIso_hom_app]
  rfl

/-- The original group leg returns through the same forward source-comparison component. -/
@[reassoc]
theorem sourceTypeColimitIso_ι_inv (D : ℕ ⥤ C) (n : ℕ) :
    (forget GrpCat.{v}).map ((colimitCocone (D ⋙ F)).ι.app n) ≫
        (sourceTypeColimitIso F G e D).inv =
      e.hom.app (D.obj n) ≫ CategoryTheory.Limits.colimit.ι (D ⋙ G) n := by
  apply (cancel_mono (sourceTypeColimitIso F G e D).hom).1
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    sourceTypeColimitIso_ι_hom, ← Category.assoc, e.hom_inv_id_app, Category.id_comp]

/-- The given comparison retains the entire square of original input-diagram maps. -/
theorem sourceTypeDiagramIso_hom_naturality {D E : ℕ ⥤ C} (α : D ⟶ E) :
    Functor.whiskerRight α G ≫ (sourceTypeDiagramIso F G e E).hom =
      (sourceTypeDiagramIso F G e D).hom ≫
        Functor.whiskerRight (Functor.whiskerRight α F) (forget GrpCat.{v}) := by
  apply NatTrans.ext
  funext n
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, sourceTypeDiagramIso_hom_app]
  exact e.inv.naturality (α.app n)

/-- The whole diagram map preserves the actual source Type/group-colimit square. -/
@[reassoc]
theorem sourceTypeColimitIso_hom_naturality {D E : ℕ ⥤ C} (α : D ⟶ E) :
    colim.map (Functor.whiskerRight α G) ≫ (sourceTypeColimitIso F G e E).hom =
      (sourceTypeColimitIso F G e D).hom ≫
        (forget GrpCat.{v}).map (((colimitCoconeIsColimit (D ⋙ F)).map
          (colimitCocone (E ⋙ F)) (Functor.whiskerRight α F))) := by
  have h := congrArg (fun t => colim.map t)
    (sourceTypeDiagramIso_hom_naturality F G e α)
  rw [Functor.map_comp, Functor.map_comp] at h
  let g : (forget GrpCat.{v}).obj (GrpCat.FilteredColimits.colimit (D ⋙ F)) ⟶
      (forget GrpCat.{v}).obj (GrpCat.FilteredColimits.colimit (E ⋙ F)) :=
    (forget GrpCat.{v}).map (((colimitCoconeIsColimit (D ⋙ F)).map
          (colimitCocone (E ⋙ F)) (Functor.whiskerRight α F)))
  have hb : colim.map (Functor.whiskerRight (Functor.whiskerRight α F) (forget GrpCat.{v})) ≫
      (underlyingTypeColimitIso (E ⋙ F)).hom = (underlyingTypeColimitIso (D ⋙ F)).hom ≫ g :=
    underlyingTypeColimitIso_hom_naturality (Functor.whiskerRight α F)
  change colim.map (Functor.whiskerRight α G) ≫
      (colim.map (sourceTypeDiagramIso F G e E).hom ≫
        (underlyingTypeColimitIso (E ⋙ F)).hom) =
    (colim.map (sourceTypeDiagramIso F G e D).hom ≫
      (underlyingTypeColimitIso (D ⋙ F)).hom) ≫
        g
  calc
    _ = (colim.map (Functor.whiskerRight α G) ≫
        colim.map (sourceTypeDiagramIso F G e E).hom) ≫
          (underlyingTypeColimitIso (E ⋙ F)).hom := (Category.assoc _ _ _).symm
    _ = (colim.map (sourceTypeDiagramIso F G e D).hom ≫
        colim.map (Functor.whiskerRight (Functor.whiskerRight α F) (forget GrpCat.{v}))) ≫
          (underlyingTypeColimitIso (E ⋙ F)).hom :=
      congrArg (fun t => t ≫ (underlyingTypeColimitIso (E ⋙ F)).hom) h
    _ = colim.map (sourceTypeDiagramIso F G e D).hom ≫
        (colim.map (Functor.whiskerRight (Functor.whiskerRight α F) (forget GrpCat.{v})) ≫
          (underlyingTypeColimitIso (E ⋙ F)).hom) := Category.assoc _ _ _
    _ = colim.map (sourceTypeDiagramIso F G e D).hom ≫
        ((underlyingTypeColimitIso (D ⋙ F)).hom ≫
          g) :=
      congrArg (fun t => colim.map (sourceTypeDiagramIso F G e D).hom ≫ t)
        hb
    _ = _ := (Category.assoc _ _ _).symm

/-- The inverse square retains the same original source functors and diagram map. -/
@[reassoc]
theorem sourceTypeColimitIso_inv_naturality {D E : ℕ ⥤ C} (α : D ⟶ E) :
    (forget GrpCat.{v}).map (((colimitCoconeIsColimit (D ⋙ F)).map
          (colimitCocone (E ⋙ F)) (Functor.whiskerRight α F))) ≫
        (sourceTypeColimitIso F G e E).inv =
      (sourceTypeColimitIso F G e D).inv ≫ colim.map (Functor.whiskerRight α G) := by
  exact inverseSquare (sourceTypeColimitIso F G e D) (sourceTypeColimitIso F G e E)
    (colim.map (Functor.whiskerRight α G))
    ((forget GrpCat.{v}).map (((colimitCoconeIsColimit (D ⋙ F)).map
          (colimitCocone (E ⋙ F)) (Functor.whiskerRight α F))))
    (sourceTypeColimitIso_hom_naturality F G e α)

include e in
/-- An isomorphism of the actual group-colimit map gives the original source Type map. -/
theorem sourceTypeColimitMap_isIso {D E : ℕ ⥤ C} (α : D ⟶ E)
    [IsIso (((colimitCoconeIsColimit (D ⋙ F)).map
          (colimitCocone (E ⋙ F)) (Functor.whiskerRight α F)))] :
    IsIso (colim.map (Functor.whiskerRight α G)) := by
  let _ : IsIso (colim.map (Functor.whiskerRight
      (Functor.whiskerRight α F) (forget GrpCat.{v}))) :=
    underlyingTypeColimitMap_isIso (Functor.whiskerRight α F)
  let i := asIso (colim.map (Functor.whiskerRight
    (Functor.whiskerRight α F) (forget GrpCat.{v})))
  let q : CategoryTheory.Limits.colimit (D ⋙ G) ≅ CategoryTheory.Limits.colimit (E ⋙ G) :=
    colim.mapIso (sourceTypeDiagramIso F G e D) ≪≫ i ≪≫
      (colim.mapIso (sourceTypeDiagramIso F G e E)).symm
  have hs := congrArg (fun t => colim.map t)
    (sourceTypeDiagramIso_hom_naturality F G e α)
  rw [Functor.map_comp, Functor.map_comp] at hs
  have h : colim.map (Functor.whiskerRight α G) = q.hom := by
    have ht : (colim.mapIso (sourceTypeDiagramIso F G e D)).hom ≫ i.hom =
        colim.map (Functor.whiskerRight α G) ≫
          (colim.mapIso (sourceTypeDiagramIso F G e E)).hom := hs.symm
    exact (((colim.mapIso (sourceTypeDiagramIso F G e E)).comp_inv_eq).mpr ht).symm.trans
      (Category.assoc _ _ _)
  rw [h]
  infer_instance

end GrpCat.FilteredColimits
