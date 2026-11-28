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

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# The actual filtered group quotient and its underlying Type colimit

For a natural-number diagram of groups, the forgetful image of its original
filtered group cocone is a Type colimit. Its comparison with the chosen Type
colimit retains every original leg and every natural transformation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe v

open CategoryTheory CategoryTheory.Limits

namespace GrpCat.FilteredColimits

/-- The original group colimit cocone, mapped through the genuine forgetful functor. -/
def underlyingTypeColimitCocone (D : ℕ ⥤ GrpCat.{v}) :
    ColimitCocone (D ⋙ forget GrpCat.{v}) := by
  let _ : PreservesFilteredColimitsOfSize.{0, 0} (forget GrpCat.{v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{v, v, 0, 0} (forget GrpCat.{v})
  exact ⟨(forget GrpCat.{v}).mapCocone (colimitCocone D),
    isColimitOfPreserves (forget GrpCat.{v}) (colimitCoconeIsColimit D)⟩

/-- Both complete maps compare the chosen Type colimit with the actual original group quotient. -/
def underlyingTypeColimitIso (D : ℕ ⥤ GrpCat.{v}) :
    CategoryTheory.Limits.colimit (D ⋙ forget GrpCat.{v}) ≅
      (forget GrpCat.{v}).obj (colimit D) :=
  CategoryTheory.Limits.colimit.isoColimitCocone (underlyingTypeColimitCocone D)

/-- Every chosen Type-colimit leg maps to the same original group-colimit leg. -/
@[reassoc]
theorem underlyingTypeColimitIso_ι_hom (D : ℕ ⥤ GrpCat.{v}) (n : ℕ) :
    CategoryTheory.Limits.colimit.ι (D ⋙ forget GrpCat.{v}) n ≫
        (underlyingTypeColimitIso D).hom =
      (forget GrpCat.{v}).map ((colimitCocone D).ι.app n) :=
  CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom
    (underlyingTypeColimitCocone D) n

/-- Every original group-colimit leg returns to the same chosen Type-colimit leg. -/
@[reassoc]
theorem underlyingTypeColimitIso_ι_inv (D : ℕ ⥤ GrpCat.{v}) (n : ℕ) :
    (forget GrpCat.{v}).map ((colimitCocone D).ι.app n) ≫
        (underlyingTypeColimitIso D).inv =
      CategoryTheory.Limits.colimit.ι (D ⋙ forget GrpCat.{v}) n :=
  CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv
    (underlyingTypeColimitCocone D) n

/-- The whole actual group-colimit map commutes with the forward Type comparison. -/
@[reassoc]
theorem underlyingTypeColimitIso_hom_naturality
    {D E : ℕ ⥤ GrpCat.{v}} (α : D ⟶ E) :
    colim.map (Functor.whiskerRight α (forget GrpCat.{v})) ≫
        (underlyingTypeColimitIso E).hom =
      (underlyingTypeColimitIso D).hom ≫
        (forget GrpCat.{v}).map ((colimitCoconeIsColimit D).map (colimitCocone E) α) := by
  apply CategoryTheory.Limits.colimit.hom_ext
  intro n
  erw [CategoryTheory.Limits.colimit.ι_map_assoc,
    underlyingTypeColimitIso_ι_hom, ← Category.assoc,
    underlyingTypeColimitIso_ι_hom]
  change (forget GrpCat.{v}).map (α.app n) ≫
      (forget GrpCat.{v}).map ((colimitCocone E).ι.app n) =
    (forget GrpCat.{v}).map ((colimitCocone D).ι.app n) ≫
      (forget GrpCat.{v}).map ((colimitCoconeIsColimit D).map (colimitCocone E) α)
  erw [← Functor.map_comp, ← Functor.map_comp, IsColimit.ι_map]

/-- The inverse Type comparison retains the same entire original group-colimit map. -/
@[reassoc]
theorem underlyingTypeColimitIso_inv_naturality
    {D E : ℕ ⥤ GrpCat.{v}} (α : D ⟶ E) :
    (forget GrpCat.{v}).map ((colimitCoconeIsColimit D).map (colimitCocone E) α) ≫
        (underlyingTypeColimitIso E).inv =
      (underlyingTypeColimitIso D).inv ≫
        colim.map (Functor.whiskerRight α (forget GrpCat.{v})) := by
  apply (cancel_mono (underlyingTypeColimitIso E).hom).1
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    underlyingTypeColimitIso_hom_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  rfl

/-- An isomorphism of the actual group-colimit map gives the exact original Type-colimit map. -/
theorem underlyingTypeColimitMap_isIso {D E : ℕ ⥤ GrpCat.{v}} (α : D ⟶ E)
    [IsIso ((colimitCoconeIsColimit D).map (colimitCocone E) α)] :
    IsIso (colim.map (Functor.whiskerRight α (forget GrpCat.{v}))) := by
  have h : colim.map (Functor.whiskerRight α (forget GrpCat.{v})) =
      (underlyingTypeColimitIso D).hom ≫
        (forget GrpCat.{v}).map ((colimitCoconeIsColimit D).map (colimitCocone E) α) ≫
        (underlyingTypeColimitIso E).inv := by
    apply (cancel_mono (underlyingTypeColimitIso E).hom).1
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact underlyingTypeColimitIso_hom_naturality α
  let i : (colimitCocone D).pt ≅ (colimitCocone E).pt :=
    asIso ((colimitCoconeIsColimit D).map (colimitCocone E) α)
  let e : CategoryTheory.Limits.colimit (D ⋙ forget GrpCat.{v}) ≅
      CategoryTheory.Limits.colimit (E ⋙ forget GrpCat.{v}) :=
    underlyingTypeColimitIso D ≪≫
      (forget GrpCat.{v}).mapIso i ≪≫
        (underlyingTypeColimitIso E).symm
  have he : e.hom = colim.map (Functor.whiskerRight α (forget GrpCat.{v})) := by
    dsimp only [e, i, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
    exact h.symm
  rw [← he]
  infer_instance

end GrpCat.FilteredColimits
