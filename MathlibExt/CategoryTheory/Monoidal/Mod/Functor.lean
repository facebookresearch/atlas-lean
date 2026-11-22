/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monoidal.Mod

/-!
# Transporting internal modules along monoidal functors

A lax monoidal functor transports a module object over an internal monoid to a module object
over the image monoid. This file packages that construction on objects and morphisms as a functor
between the corresponding categories of internal modules.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory MonObj
open scoped CategoryTheory.Obj

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.LaxMonoidal]
variable (M X : C) [MonObj M] [ModObj M X]

/-- A lax monoidal functor transports an internal module object to a module object over the
image monoid. The transported action is the tensorator followed by the image of the original
action. -/
@[instance_reducible]
noncomputable def modObjObj : ModObj (F.obj M) (F.obj X) where
  smul := LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X))
  one_smul := by
    change ((LaxMonoidal.ε F ≫ F.map (MonObj.one (X := M))) ▷ F.obj X) ≫
      LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X)) =
        (MonoidalCategory.leftUnitor (F.obj X)).hom
    simp only [comp_whiskerRight, Category.assoc,
      LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, ModObj.one_smul_self,
      LaxMonoidal.left_unitality]
  mul_smul := by
    change ((LaxMonoidal.μ F M M ≫ F.map (MonObj.mul (X := M))) ▷ F.obj X) ≫
      LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X)) =
        (MonoidalCategory.associator (F.obj M) (F.obj M) (F.obj X)).hom ≫
          (F.obj M ◁ (LaxMonoidal.μ F M X ≫
            F.map (ModObj.smul (M := M) (X := X)))) ≫
          LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X))
    simp only [comp_whiskerRight, Category.assoc,
      LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, ModObj.mul_smul_self,
      MonoidalCategory.whiskerLeft_comp, LaxMonoidal.μ_natural_right_assoc]
    rw [F.map_comp, LaxMonoidal.associativity_assoc]

scoped[CategoryTheory.Obj] attribute [instance] CategoryTheory.Functor.modObjObj

/-- The action of the transported module object is the tensorator followed by the image of the
original action. -/
@[simp]
theorem modObjObj_smul :
    ModObj.smul (M := F.obj M) (X := F.obj X) =
      LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X)) :=
  rfl

variable {M X} in
/-- A lax monoidal functor maps module morphisms to module morphisms. -/
instance map.instIsModHom {Y : C} [ModObj M Y]
    (f : X ⟶ Y) [IsModHom M f] :
    IsModHom (F.obj M) (F.map f) := by
  exact
    { smul_hom := by
        simp only [modObjObj_smul]
        change (LaxMonoidal.μ F M X ≫
            F.map (ModObj.smul (M := M) (X := X))) ≫ F.map f =
          (F.obj M ◁ F.map f) ≫ LaxMonoidal.μ F M Y ≫
            F.map (ModObj.smul (M := M) (X := Y))
        calc
          _ = LaxMonoidal.μ F M X ≫
              (F.map (ModObj.smul (M := M) (X := X)) ≫ F.map f) :=
            Category.assoc _ _ _
          _ = LaxMonoidal.μ F M X ≫
              F.map (ModObj.smul (M := M) (X := X) ≫ f) := by
            rw [F.map_comp]
          _ = LaxMonoidal.μ F M X ≫
              F.map ((M ◁ f) ≫ ModObj.smul (M := M) (X := Y)) :=
            congrArg (fun g ↦ LaxMonoidal.μ F M X ≫ F.map g)
              (IsModHom.smul_hom (A := M) (f := f))
          _ = LaxMonoidal.μ F M X ≫
              (F.map (M ◁ f) ≫ F.map (ModObj.smul (M := M) (X := Y))) := by
            rw [F.map_comp]
          _ = (LaxMonoidal.μ F M X ≫ F.map (M ◁ f)) ≫
              F.map (ModObj.smul (M := M) (X := Y)) :=
            (Category.assoc _ _ _).symm
          _ = ((F.obj M ◁ F.map f) ≫ LaxMonoidal.μ F M Y) ≫
              F.map (ModObj.smul (M := M) (X := Y)) :=
            congrArg (· ≫ F.map (ModObj.smul (M := M) (X := Y)))
              (LaxMonoidal.μ_natural_right F M f).symm
          _ = _ := Category.assoc _ _ _ }

/-- A lax monoidal functor induces a functor between categories of internal modules over a
fixed monoid and its image monoid. -/
@[simps]
noncomputable def mapMod : Mod C M ⥤ Mod D (F.obj M) where
  obj X := ⟨F.obj X.X⟩
  map f := ⟨F.map f.hom⟩

/-- An isomorphism between bundled internal modules from an isomorphism of their underlying
objects whose forward map is a module morphism. -/
public abbrev _root_.CategoryTheory.Mod.isoOfUnderlyingIso
    {V : Type u₄} [Category.{v₄} V] [MonoidalCategory V]
    {A : V} [MonObj A] {P Q : Mod V A} (e : P.X ≅ Q.X)
    (h : ModObj.smul (M := A) (X := P.X) ≫ e.hom =
      (A ◁ e.hom) ≫ ModObj.smul (M := A) (X := Q.X)) : P ≅ Q := by
  letI : IsModHom A e.hom := ⟨h⟩
  exact
    { hom := ⟨e.hom⟩
      inv := ⟨e.inv⟩
      hom_inv_id := by
        apply Mod.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Mod.hom_ext
        exact e.inv_hom_id }

@[simp]
public theorem _root_.CategoryTheory.Mod.isoOfUnderlyingIso_hom_hom
    {V : Type u₄} [Category.{v₄} V] [MonoidalCategory V]
    {A : V} [MonObj A] {P Q : Mod V A} (e : P.X ≅ Q.X)
    (h : ModObj.smul (M := A) (X := P.X) ≫ e.hom =
      (A ◁ e.hom) ≫ ModObj.smul (M := A) (X := Q.X)) :
    ((Mod.isoOfUnderlyingIso e h).hom).hom = e.hom :=
  rfl

@[simp]
public theorem _root_.CategoryTheory.Mod.isoOfUnderlyingIso_inv_hom
    {V : Type u₄} [Category.{v₄} V] [MonoidalCategory V]
    {A : V} [MonObj A] {P Q : Mod V A} (e : P.X ≅ Q.X)
    (h : ModObj.smul (M := A) (X := P.X) ≫ e.hom =
      (A ◁ e.hom) ≫ ModObj.smul (M := A) (X := Q.X)) :
    ((Mod.isoOfUnderlyingIso e h).inv).hom = e.inv :=
  rfl

/-- The canonical monoid morphism used to compare module transport by the identity functor with
restriction of scalars. -/
abbrev mapModIdMonHom (M : C) [hM : MonObj M] :
    (mapMon (Functor.id C)).obj ({ X := M, mon := hM } : Mon C) ⟶
      ({ X := M, mon := hM } : Mon C) :=
  (mapMonIdIso (C := C)).hom.app ({ X := M, mon := hM } : Mon C)

@[simp]
theorem mapModIdMonHom_hom (M : C) [hM : MonObj M] :
    (mapModIdMonHom M).hom = 𝟙 M :=
  rfl

/-- The underlying map of `mapModIdMonHom` is a monoid morphism. -/
public instance mapModIdMonHom_isMonHom (M : C) [hM : MonObj M] :
    IsMonHom (mapModIdMonHom M).hom :=
  (mapModIdMonHom M).isMonHom_hom

set_option backward.isDefEq.respectTransparency false in
/-- Transporting modules along the identity lax-monoidal functor agrees with restriction along
the canonical comparison from the transported monoid to the original monoid. -/
noncomputable def mapModIdIso (M : C) [hM : MonObj M] :
    mapMod (Functor.id C) M ≅
      Mod.comap (mapModIdMonHom M).hom :=
  NatIso.ofComponents
    (fun X ↦ Mod.isoOfUnderlyingIso (Iso.refl X.X) (by
      simp only [Mod.scalarRestriction_smul, modObjObj_smul]
      simp only [mapModIdMonHom_hom]
      simp only [LaxMonoidal.id_μ, Functor.id_obj, Functor.id_map]
      simp [mapMod]))
    (by
      intro X Y f
      apply Mod.hom_ext
      change f.hom ≫ 𝟙 Y.X = 𝟙 X.X ≫ f.hom
      simp)

@[simp]
theorem mapModIdIso_hom_app_hom (M : C) [hM : MonObj M] (X : Mod C M) :
    ((mapModIdIso M).hom.app X).hom = 𝟙 X.X :=
  by
    simp [mapModIdIso]
    rfl

@[simp]
theorem mapModIdIso_inv_app_hom (M : C) [hM : MonObj M] (X : Mod C M) :
    ((mapModIdIso M).inv.app X).hom = 𝟙 X.X :=
  by
    simp [mapModIdIso]
    rfl

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- The canonical monoid morphism comparing transport by a composite with successive transport. -/
abbrev mapModCompMonHom (G : D ⥤ E) [G.LaxMonoidal]
    (M : C) [hM : MonObj M] :
    (mapMon (F ⋙ G)).obj ({ X := M, mon := hM } : Mon C) ⟶
      (mapMon F ⋙ mapMon G).obj ({ X := M, mon := hM } : Mon C) :=
  (mapMonCompIso (F := F) (G := G)).hom.app ({ X := M, mon := hM } : Mon C)

@[simp]
theorem mapModCompMonHom_hom (G : D ⥤ E) [G.LaxMonoidal]
    (M : C) [hM : MonObj M] :
    (mapModCompMonHom F G M).hom = 𝟙 (G.obj (F.obj M)) :=
  rfl

/-- The underlying map of `mapModCompMonHom` is a monoid morphism. -/
public instance mapModCompMonHom_isMonHom (G : D ⥤ E) [G.LaxMonoidal]
    (M : C) [hM : MonObj M] :
    IsMonHom (mapModCompMonHom F G M).hom :=
  (mapModCompMonHom F G M).isMonHom_hom

set_option backward.isDefEq.respectTransparency false in
/-- Transport along a composite lax-monoidal functor agrees with successive transport, followed
by restriction along the canonical comparison between the two transported monoids. -/
noncomputable def mapModCompIso (G : D ⥤ E) [G.LaxMonoidal]
    (M : C) [hM : MonObj M] :
    mapMod (F ⋙ G) M ≅
      (mapMod F M ⋙ mapMod G (F.obj M)) ⋙
        Mod.comap (mapModCompMonHom F G M).hom :=
  NatIso.ofComponents
    (fun X ↦ Mod.isoOfUnderlyingIso (Iso.refl (G.obj (F.obj X.X))) (by
      simp only [Mod.scalarRestriction_smul, modObjObj_smul]
      simp only [LaxMonoidal.comp_μ, Functor.comp_obj, Functor.comp_map]
      let Z : E :=
        ((Mod.comap (mapModCompMonHom F G M).hom).obj
          ((mapMod G (F.obj M)).obj ((mapMod F M).obj X))).X
      have hAct : MonoidalCategory.MonoidalLeftAction.actionHomLeft
          (mapModCompMonHom F G M).hom Z =
            𝟙 (G.obj (F.obj M) ⊗ Z) := by
        change ((𝟙 (G.obj (F.obj M))) ▷ Z) =
          𝟙 (G.obj (F.obj M) ⊗ Z)
        exact id_whiskerRight _ _
      rw [hAct]
      dsimp only [Z, mapMod, Mod.comap]
      have hMap : G.map (LaxMonoidal.μ F M X.X) ≫
          G.map (F.map (ModObj.smul (M := M) (X := X.X))) =
        G.map (LaxMonoidal.μ F M X.X ≫
          F.map (ModObj.smul (M := M) (X := X.X))) :=
        (G.map_comp _ _).symm
      have hLeft : G.obj (F.obj M) ◁ 𝟙 (G.obj (F.obj X.X)) =
          𝟙 (G.obj (F.obj M) ⊗ G.obj (F.obj X.X)) :=
        MonoidalCategory.whiskerLeft_id _ _
      calc
        ((LaxMonoidal.μ G (F.obj M) (F.obj X.X) ≫
            G.map (LaxMonoidal.μ F M X.X)) ≫
            G.map (F.map (ModObj.smul (M := M) (X := X.X)))) ≫ 𝟙 _ =
          LaxMonoidal.μ G (F.obj M) (F.obj X.X) ≫
            (G.map (LaxMonoidal.μ F M X.X) ≫
              G.map (F.map (ModObj.smul (M := M) (X := X.X)))) := by
                simp only [Category.comp_id, Category.assoc]
        _ = LaxMonoidal.μ G (F.obj M) (F.obj X.X) ≫
            G.map (LaxMonoidal.μ F M X.X ≫
              F.map (ModObj.smul (M := M) (X := X.X))) :=
          congrArg (LaxMonoidal.μ G (F.obj M) (F.obj X.X) ≫ ·) hMap
        _ = (G.obj (F.obj M) ◁ 𝟙 (G.obj (F.obj X.X))) ≫
            𝟙 (G.obj (F.obj M) ⊗ G.obj (F.obj X.X)) ≫
            LaxMonoidal.μ G (F.obj M) (F.obj X.X) ≫
            G.map (LaxMonoidal.μ F M X.X ≫
              F.map (ModObj.smul (M := M) (X := X.X))) := by
          rw [hLeft]
          simp only [Category.id_comp]))
    (by
      intro X Y f
      apply Mod.hom_ext
      change G.map (F.map f.hom) ≫ 𝟙 (G.obj (F.obj Y.X)) =
        𝟙 (G.obj (F.obj X.X)) ≫ G.map (F.map f.hom)
      simp)

@[simp]
theorem mapModCompIso_hom_app_hom (G : D ⥤ E) [G.LaxMonoidal]
    (M : C) [hM : MonObj M] (X : Mod C M) :
    ((mapModCompIso F G M).hom.app X).hom = 𝟙 (G.obj (F.obj X.X)) :=
  by
    simp [mapModCompIso]
    rfl

@[simp]
theorem mapModCompIso_inv_app_hom (G : D ⥤ E) [G.LaxMonoidal]
    (M : C) [hM : MonObj M] (X : Mod C M) :
    ((mapModCompIso F G M).inv.app X).hom = 𝟙 (G.obj (F.obj X.X)) :=
  by
    simp [mapModCompIso]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Lax-monoidal transport commutes with restriction of scalars along a monoid morphism. -/
noncomputable def mapModComapIso {M N : C} [MonObj M] [MonObj N]
    (f : M ⟶ N) [IsMonHom f] :
    Mod.comap f ⋙ mapMod F M ≅
      mapMod F N ⋙ Mod.comap (F.map f) :=
  NatIso.ofComponents
    (fun X ↦ Mod.isoOfUnderlyingIso (Iso.refl (F.obj X.X)) (by
      simp only [Mod.scalarRestriction_smul, modObjObj_smul]
      change (LaxMonoidal.μ F M X.X ≫
          F.map ((f ▷ X.X) ≫ ModObj.smul (M := N) (X := X.X))) ≫ 𝟙 _ =
        (F.obj M ◁ 𝟙 _) ≫
          ((F.map f ▷ F.obj X.X) ≫ LaxMonoidal.μ F N X.X ≫
            F.map (ModObj.smul (M := N) (X := X.X)))
      simp [F.map_comp, LaxMonoidal.μ_natural_left_assoc]))
    (by
      intro X Y g
      apply Mod.hom_ext
      change F.map g.hom ≫ 𝟙 (F.obj Y.X) =
        𝟙 (F.obj X.X) ≫ F.map g.hom
      simp)

@[simp]
theorem mapModComapIso_hom_app_hom {M N : C} [MonObj M] [MonObj N]
    (f : M ⟶ N) [IsMonHom f] (X : Mod C N) :
    ((mapModComapIso F f).hom.app X).hom = 𝟙 (F.obj X.X) :=
  by
    simp [mapModComapIso]
    rfl

@[simp]
theorem mapModComapIso_inv_app_hom {M N : C} [MonObj M] [MonObj N]
    (f : M ⟶ N) [IsMonHom f] (X : Mod C N) :
    ((mapModComapIso F f).inv.app X).hom = 𝟙 (F.obj X.X) :=
  by
    simp [mapModComapIso]
    rfl

end Functor
end CategoryTheory

end
