/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFunctoriality

/-!
# Natural-isomorphism transport for stage maps

For exact categories `C` and `D` over independent universes with their
local standard Waldhausen structures (`ExactCategory.waldhausenCategory`),
an isomorphism `e : F ≅ G` between additive exact functors induces
`mapStageNatIso F G e n : mapStage C D F n ≅ mapStage C D G n` by
postcomposition/whiskering, and `mapStageWeakNatIso F G e n` by restriction
to the pointwise weak-equivalence categories.

Reuse map: `ObjectProperty.isoMk` for the stage bundle,
`Functor.isoWhiskerLeft` for the underlying `Ar n ⥤ D` iso, existing
`mapStage_obj`/`mapStage_map` computation laws for
naturality, `mem_stageWeak` plus `IsIso` preservation (`inferInstance`) for
the weak side, and `WideSubcategory.isoMk` for the weak lift.

Cross-universe scope: `C : Type u₁` with `Category.{v₁}` and
`D : Type u₂` with `Category.{v₂}`. Upper
simplicial/nerve/diagonal transport, nerve homotopies, and Quillen span
machinery are not in this file.

Nonclaims: no nerve, realization, pointed maps, additivity theorem, `π₀`/K₀,
G-theory, spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u₁) [Category.{v₁} C]
  [Preadditive C]
  [Limits.HasZeroObject C]
  [HasBinaryBiproducts C]
  [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D]
  [Preadditive D]
  [Limits.HasZeroObject D]
  [HasBinaryBiproducts D]
  [ExactCategory D]
variable (F G : C ⥤ D) [F.Additive] [G.Additive]
  [Functor.IsExact F] [Functor.IsExact G]

/-- Natural-isomorphism transport through `mapStage` by postcomposition. -/
noncomputable def mapStageNatIso (e : F ≅ G) (n : ℕ) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      mapStage C D F n ≅ mapStage C D G n) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  refine NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ (Functor.isoWhiskerLeft X.obj e)) ?_
  intro X Y φ
  apply ObjectProperty.hom_ext
  ext A
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  exact e.hom.naturality (((forget C n).map φ).app A)

/-- Natural-isomorphism transport through `mapStageWeak` by restriction. -/
noncomputable def mapStageWeakNatIso (e : F ≅ G) (n : ℕ) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      mapStageWeak C D F n ≅ mapStageWeak C D G n) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  refine NatIso.ofComponents (fun X => ?_) ?_
  · let s := (mapStageNatIso C D F G e n).app X.obj
    have h_hom : IsIso s.hom := inferInstance
    have h_inv : IsIso s.inv := inferInstance
    refine WideSubcategory.isoMk s ?_ ?_
    · exact (stageWeak D n).of_isIso s.hom
    · exact (stageWeak D n).of_isIso s.inv
  · intro X Y φ
    apply WideSubcategory.hom_ext
    exact (mapStageNatIso C D F G e n).hom.naturality φ.hom

/-- Hom component of `mapStageNatIso` computes pointwise as `e.hom`. -/
@[simp]
theorem mapStageNatIso_hom_app
    (e : F ≅ G) (n : ℕ)
    (X : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      Stage C n)) (A : Ar n) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      ((((mapStageNatIso C D F G e n).hom.app X).hom.app A)) = e.hom.app (X.obj.obj A)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  rfl

/-- Inv component of `mapStageNatIso` computes pointwise as `e.inv`. -/
@[simp]
theorem mapStageNatIso_inv_app
    (e : F ≅ G) (n : ℕ)
    (X : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      Stage C n)) (A : Ar n) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      ((((mapStageNatIso C D F G e n).inv.app X).hom.app A)) = e.inv.app (X.obj.obj A)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  rfl

end CategoryTheory.Waldhausen.SConstruction
