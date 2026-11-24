/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monoidal.CommutativeModuleConversion
public import MathlibExt.CategoryTheory.Monoidal.RightModulePresentation
public import MathlibExt.CategoryTheory.Monoidal.Mod.ColimitsFree
public import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section
set_option autoImplicit false
set_option linter.hashCommand false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite
open scoped CategoryTheory.MonObj

namespace CategoryTheory.RightModuleFree

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable (S : C) [MonObj S]

/-- The exact standard right action module carrier. -/
abbrev Carrier := CommutativeModuleConversion.RightModule S

/-- Unwrap an actual left module in the monoidal opposite to the standard right action. -/
def unmopModule (M : Mod (Cᴹᵒᵖ) (mop S)) : Carrier S where
  X := unmop M.X
  mod :=
    { smul := (ModObj.smul (M := mop S) (X := M.X)).unmop
      one_smul := by
        have h := ModObj.one_smul_self (mop S) M.X
        exact congrArg Quiver.Hom.unmop h
      mul_smul := by
        have h := ModObj.mul_smul_self (mop S) M.X
        exact congrArg Quiver.Hom.unmop h }

/-- Wrap the actual right action as a left module in the monoidal opposite. -/
def mopModule (M : Carrier S) : Mod (Cᴹᵒᵖ) (mop S) where
  X := mop M.X
  mod :=
    { smul := (ModObj.smul (M := mop S) (X := M.X)).mop
      one_smul := by
        have h := ModObj.one_smul (M := mop S) M.X
        exact congrArg Quiver.Hom.mop h
      mul_smul := by
        have h := ModObj.mul_smul (M := mop S) M.X
        exact congrArg Quiver.Hom.mop h }

/-- Every full module morphism unwraps with the original underlying map. -/
def unmopModules : Mod (Cᴹᵒᵖ) (mop S) ⥤ Carrier S where
  obj := unmopModule S
  map f := Mod.Hom.mk' f.hom.unmop (by
    exact congrArg Quiver.Hom.unmop (IsModHom.smul_hom (f := f.hom)))
  map_id _ := by apply Mod.hom_ext; rfl
  map_comp _ _ := by apply Mod.hom_ext; rfl

/-- Every full right module morphism wraps with the original underlying map. -/
def mopModules : Carrier S ⥤ Mod (Cᴹᵒᵖ) (mop S) where
  obj := mopModule S
  map f := Mod.Hom.mk' f.hom.mop (by
    exact congrArg Quiver.Hom.mop (IsModHom.smul_hom (f := f.hom)))
  map_id _ := by apply Mod.hom_ext; rfl
  map_comp _ _ := by apply Mod.hom_ext; rfl

/-- No module law or mapping-object value changes when the carrier wrapper is removed. -/
def moduleEquivalence : Mod (Cᴹᵒᵖ) (mop S) ≌ Carrier S where
  functor := unmopModules S
  inverse := mopModules S
  unitIso := NatIso.ofComponents (fun M =>
    { hom := Mod.Hom.mk' (𝟙 M.X) (by
        change γ[mop S, M.X] ≫ 𝟙 M.X = (mop S ◁ 𝟙 M.X) ≫ γ[mop S, M.X]
        rw [whiskerLeft_id, Category.id_comp, Category.comp_id])
      inv := Mod.Hom.mk' (𝟙 M.X) (by
        change γ[mop S, M.X] ≫ 𝟙 M.X = (mop S ◁ 𝟙 M.X) ≫ γ[mop S, M.X]
        rw [whiskerLeft_id, Category.id_comp, Category.comp_id])
      hom_inv_id := by
        apply Mod.hom_ext
        change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
        exact Category.id_comp _
      inv_hom_id := by
        apply Mod.hom_ext
        change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
        exact Category.id_comp _ }) (by
    intro M N f
    apply Mod.hom_ext
    change f.hom ≫ 𝟙 N.X = 𝟙 M.X ≫ f.hom
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun M =>
    { hom := Mod.Hom.mk' (𝟙 M.X) (by
        change γ[mop S, M.X] ≫ 𝟙 M.X = (𝟙 M.X ▷ S) ≫ γ[mop S, M.X]
        rw [id_whiskerRight, Category.id_comp, Category.comp_id])
      inv := Mod.Hom.mk' (𝟙 M.X) (by
        change γ[mop S, M.X] ≫ 𝟙 M.X = (𝟙 M.X ▷ S) ≫ γ[mop S, M.X]
        rw [id_whiskerRight, Category.id_comp, Category.comp_id])
      hom_inv_id := by
        apply Mod.hom_ext
        change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
        exact Category.id_comp _
      inv_hom_id := by
        apply Mod.hom_ext
        change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
        exact Category.id_comp _ }) (by
    intro M N f
    apply Mod.hom_ext
    change f.hom ≫ 𝟙 N.X = 𝟙 M.X ≫ f.hom
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp M := by
    apply Mod.hom_ext
    change (𝟙 (unmop M.X)) ≫ 𝟙 (unmop M.X) = 𝟙 (unmop M.X)
    exact Category.id_comp _

/-- The actual standard right free functor is existing Mod.free in the monoidal opposite. -/
def functor : C ⥤ Carrier S :=
  mopFunctor C ⋙ Mod.free (mop S) ⋙ unmopModules S

/-- Its carrier is literally the original right tensor order. -/
theorem functor_obj (X : C) : ((functor S).obj X).X = X ⊗ S := by rfl

/-- Its underlying map is the entire original right tensor map. -/
theorem functor_map {X Y : C} (f : X ⟶ Y) :
    eqToHom (functor_obj S X).symm ≫ ((functor S).map f).hom ≫
      eqToHom (functor_obj S Y) = f ▷ S := by
  change 𝟙 (X ⊗ S) ≫ (f ▷ S) ≫ 𝟙 (Y ⊗ S) = f ▷ S
  rw [Category.comp_id, Category.id_comp]

/-- Its full action is the actual original multiplication in the right order. -/
theorem functor_smul (X : C) :
    (eqToHom (functor_obj S X).symm ▷ S) ≫
      ModObj.smul (M := mop S) (X := ((functor S).obj X).X) ≫
        eqToHom (functor_obj S X) =
      (α_ X S S).hom ≫ (X ◁ (μ : S ⊗ S ⟶ S)) := by
  change (𝟙 (X ⊗ S) ▷ S) ≫
      ((α_ X S S).hom ≫ (X ◁ (μ : S ⊗ S ⟶ S))) ≫ 𝟙 (X ⊗ S) = _
  rw [id_whiskerRight, Category.comp_id, Category.id_comp]

/-- The constructed standard right functor is left adjoint to the actual forgetful functor. -/
@[no_expose]
def adjunction : functor S ⊣ Mod.forget (D := C) (mop S) := by
  let adj := ((mopEquiv C).toAdjunction.comp (Mod.freeForgetAdjunction (mop S))).comp
    (moduleEquivalence S).toAdjunction
  exact adj.ofNatIsoRight (NatIso.ofComponents (fun M => Iso.refl M.X) (by
    intro M N f
    change f.hom ≫ 𝟙 N.X = 𝟙 M.X ≫ f.hom
    exact (Category.comp_id _).trans (Category.id_comp _).symm))

/-- The comparison has both full module triangle identities. -/
theorem moduleEquivalence_functor_triangle (M : Mod (Cᴹᵒᵖ) (mop S)) :
    (unmopModules S).map ((moduleEquivalence S).unitIso.hom.app M) ≫
      (moduleEquivalence S).counitIso.hom.app ((unmopModules S).obj M) = 𝟙 _ :=
  (moduleEquivalence S).functor_unit_comp M

theorem moduleEquivalence_inverse_triangle (M : Carrier S) :
    (moduleEquivalence S).unitIso.hom.app ((mopModules S).obj M) ≫
      (mopModules S).map ((moduleEquivalence S).counitIso.hom.app M) = 𝟙 _ :=
  (moduleEquivalence S).unit_inverse_comp M

/-- The selected functor is the actual complete Mod.free construction, not a supplied free law. -/
theorem functor_eq : functor S =
    mopFunctor C ⋙ Mod.free (mop S) ⋙ unmopModules S := by rfl

/-- The standard right free and forgetful functors satisfy the complete forward triangle. -/
theorem adjunction_functor_triangle (X : C) :
    (functor S).map ((adjunction S).unit.app X) ≫
      (adjunction S).counit.app ((functor S).obj X) = 𝟙 _ :=
  (adjunction S).left_triangle_components X

/-- The complete inverse triangle holds on every actual right module. -/
theorem adjunction_forget_triangle (M : Carrier S) :
    (adjunction S).unit.app ((Mod.forget (D := C) (mop S)).obj M) ≫
      (Mod.forget (D := C) (mop S)).map ((adjunction S).counit.app M) = 𝟙 _ :=
  (adjunction S).right_triangle_components M

section Commutative

variable [SymmetricCategory C] [IsCommMonObj S]

/-- Capture the exact old left free followed by the proved right conversion. -/
@[no_expose]
def convertedLeftFree : C ⥤ Carrier S := Mod.free S ⋙
  CommutativeModuleConversion.leftToRight S

/-- The old underlying free value is unchanged before the standard right comparison. -/
theorem convertedLeftFree_eq : convertedLeftFree S =
    Mod.free S ⋙ CommutativeModuleConversion.leftToRight S := by rfl

/-- The inverse conversion retains the entire actual underlying module functor. -/
@[no_expose]
def inverseForgetIso : CommutativeModuleConversion.rightToLeft S ⋙ Mod.forget S ≅
    Mod.forget (D := C) (mop S) :=
  NatIso.ofComponents (fun M => Iso.refl M.X) (by
    intro M N f
    change (CommutativeModuleConversion.toLeftMap S f).hom ≫ 𝟙 N.X =
      𝟙 M.X ≫ f.hom
    rw [CommutativeModuleConversion.toLeftMap_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The actual original left adjunction and genuine conversion construct the second adjunction. -/
@[no_expose]
def convertedLeftAdjunction : convertedLeftFree S ⊣ Mod.forget (D := C) (mop S) :=
  ((Mod.freeForgetAdjunction S).comp
    (CommutativeModuleConversion.moduleEquivalence S).toAdjunction).ofNatIsoRight
      (inverseForgetIso S)

/-- Actual standard right free and converted left free are naturally isomorphic by uniqueness. -/
@[no_expose]
def freeComparison : convertedLeftFree S ≅ functor S :=
  Adjunction.leftAdjointUniq (convertedLeftAdjunction S) (adjunction S)

/-- The forward complete right-module adjunct preserves the original free generator. -/
theorem freeComparison_homEquiv {X : C} {M : Carrier S}
    (f : (functor S).obj X ⟶ M) :
    (convertedLeftAdjunction S).homEquiv X M ((freeComparison S).hom.app X ≫ f) =
      (adjunction S).homEquiv X M f := by
  let adj := convertedLeftAdjunction S
  let newAdj := adjunction S
  let q := freeComparison S
  have hStart := adj.homEquiv_naturality_right (q.hom.app X) f
  have hUnit : adj.homEquiv X ((functor S).obj X) (q.hom.app X) =
      newAdj.unit.app X := Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ X
  exact hStart.trans
    ((congrArg (fun z => z ≫ (Mod.forget (D := C) (mop S)).map f) hUnit).trans
      (newAdj.homEquiv_unit X M f).symm)

/-- The inverse entire adjunct recovers the same original right-module map. -/
theorem freeComparison_homEquiv_symm {X : C} {M : Carrier S}
    (f : X ⟶ (Mod.forget (D := C) (mop S)).obj M) :
    (freeComparison S).hom.app X ≫ ((adjunction S).homEquiv X M).symm f =
      ((convertedLeftAdjunction S).homEquiv X M).symm f := by
  apply ((convertedLeftAdjunction S).homEquiv X M).injective
  exact (freeComparison_homEquiv S _).trans
    ((Equiv.apply_symm_apply _ f).trans (Equiv.apply_symm_apply _ f).symm)

/-- The whole original unit is retained by the genuine standard free comparison. -/
theorem freeComparison_unit (X : C) :
    (convertedLeftAdjunction S).unit.app X ≫
      (Mod.forget (D := C) (mop S)).map ((freeComparison S).hom.app X) =
        (adjunction S).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ X

/-- The whole original counit is retained on every actual right module. -/
theorem freeComparison_counit (M : Carrier S) :
    (freeComparison S).hom.app ((Mod.forget (D := C) (mop S)).obj M) ≫
      (adjunction S).counit.app M = (convertedLeftAdjunction S).counit.app M :=
  Adjunction.leftAdjointUniq_hom_app_counit
    (convertedLeftAdjunction S) (adjunction S) M

end Commutative

end CategoryTheory.RightModuleFree

open CategoryTheory MonoidalCategory MonoidalOpposite
open CategoryTheory.CommutativeModuleConversion (RightModule)
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped CategoryTheory.MonObj

namespace CategoryTheory.RightModuleFree

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable (M : C) [MonObj M]

/-- The existing free object, with its original multiplication action. -/
abbrev freeObject (X : C) : RightModule M := (functor M).obj X

/-- The existing entire free-module map. -/
abbrev freeMap {X Y : C} (f : X ⟶ Y) : freeObject M X ⟶ freeObject M Y :=
  (functor M).map f

/-- The complete free carrier is the original right tensor order. -/
theorem freeObject_X (X : C) : (freeObject M X).X = X ⊗ M := functor_obj M X

/-- The original action is the actual associator followed by multiplication. -/
theorem freeObject_action (X : C) :
    (freeObject M X).action = (α_ X M M).hom ≫ (X ◁ μ[M]) := by rfl

/-- Every original free map is literal right tensoring on carriers. -/
@[simp]
theorem freeMap_hom {X Y : C} (f : X ⟶ Y) : (freeMap M f).hom = f ▷ M := by rfl

/-- The original wrapping equivalence unit retains the entire carrier identity. -/
theorem moduleEquivalence_unit_hom (X : Mod (Cᴹᵒᵖ) (mop M)) :
    ((moduleEquivalence M).unitIso.hom.app X).hom = 𝟙 X.X := by rfl

/-- Its original counit retains the entire right-module carrier identity. -/
theorem moduleEquivalence_counit_hom (X : RightModule M) :
    ((moduleEquivalence M).counitIso.hom.app X).hom = 𝟙 X.X := by rfl

/-- The selected free adjunction inserts the original monoid unit on the right. -/
theorem adjunction_unit_app (X : C) :
    (adjunction M).unit.app X = (ρ_ X).inv ≫ (X ◁ η[M]) := by
  have h := congrArg Quiver.Hom.unmop
    (Mod.freeForgetAdjunction_unit_app (mop M) (mop X))
  change ((Mod.freeForgetAdjunction (mop M)).unit.app (mop X)).unmop =
    (ρ_ X).inv ≫ (X ◁ η[M]) ≫ 𝟙 (X ⊗ M) at h
  unfold adjunction
  rw [Adjunction.ofNatIsoRight_unit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  change ((𝟙 X ≫ ((Mod.freeForgetAdjunction (mop M)).unit.app (mop X)).unmop) ≫
    𝟙 (X ⊗ M)) ≫ 𝟙 (X ⊗ M) = _
  rw [h]
  change ((𝟙 X ≫ ((ρ_ X).inv ≫ (X ◁ η[M]) ≫ 𝟙 (X ⊗ M))) ≫
    𝟙 (X ⊗ M)) ≫ 𝟙 (X ⊗ M) = (ρ_ X).inv ≫ (X ◁ η[M])
  simp only [Category.id_comp, Category.comp_id]

/-- The selected free adjunction counit is the original whole right action. -/
theorem adjunction_counit_app_hom (Y : RightModule M) :
    ((adjunction M).counit.app Y).hom = Y.action := by
  have h := congrArg Quiver.Hom.unmop
    (Mod.freeForgetAdjunction_counit_app_hom (mop M) ((mopModules M).obj Y))
  change (((Mod.freeForgetAdjunction (mop M)).counit.app
    ((mopModules M).obj Y)).hom).unmop = 𝟙 (Y.X ⊗ M) ≫ Y.action at h
  unfold adjunction
  rw [Adjunction.ofNatIsoRight_counit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [Adjunction.comp_counit_app, Adjunction.comp_counit_app]
  change (𝟙 Y.X ▷ M) ≫ (((𝟙 Y.X ▷ M) ≫
    (((Mod.freeForgetAdjunction (mop M)).counit.app
      ((mopModules M).obj Y)).hom).unmop) ≫ 𝟙 Y.X) = Y.action
  rw [h]
  simp only [id_whiskerRight, Category.id_comp]
  exact (Category.comp_id (𝟙 (Y.X ⊗ M) ≫ Y.action)).trans (Category.id_comp Y.action)

/-- The actual monoid-unit insertion, identified with the selected adjunction unit. -/
def freeGenerator (X : C) : X ⟶ (freeObject M X).X :=
  (ρ_ X).inv ≫ (X ◁ η[M])

/-- The complete original unit component is the generator insertion. -/
theorem adjunction_unit (X : C) :
    (adjunction M).unit.app X = freeGenerator M X := adjunction_unit_app M X

/-- The original selected counit module map. -/
abbrev actionCounit (Y : RightModule M) : freeObject M Y.X ⟶ Y :=
  (adjunction M).counit.app Y

/-- Its entire carrier value is the actual action, on every module. -/
@[simp]
theorem actionCounit_hom (Y : RightModule M) :
    (actionCounit M Y).hom = Y.action := adjunction_counit_app_hom M Y

/-- The original inverse Hom function of the selected free adjunction. -/
abbrev extendFree (X : C) (Y : RightModule M) (f : X ⟶ Y.X) :
    freeObject M X ⟶ Y := ((adjunction M).homEquiv X Y).symm f

/-- The whole extension function is the original tensored map followed by the action. -/
theorem extendFree_hom (X : C) (Y : RightModule M) :
    (fun f : X ⟶ Y.X => (extendFree M X Y f).hom) =
      (fun f => (f ▷ M) ≫ Y.action) := by
  funext f
  have h := congrArg Mod.Hom.hom ((adjunction M).homEquiv_counit X Y f)
  exact h.trans ((congrArg
    (fun k => k ≫ ((adjunction M).counit.app Y).hom) (freeMap_hom M f)).trans
      (congrArg (fun k => (f ▷ M) ≫ k) (adjunction_counit_app_hom M Y)))

/-- The original full Hom equivalence, with both original adjunction functions. -/
abbrev freeHomEquiv (X : C) (Y : RightModule M) :
    (freeObject M X ⟶ Y) ≃ (X ⟶ Y.X) := (adjunction M).homEquiv X Y

/-- Its entire forward function is generator evaluation. -/
theorem freeHomEquiv_toFun (X : C) (Y : RightModule M) :
    (freeHomEquiv M X Y).toFun =
      (fun f => freeGenerator M X ≫ f.hom) := by
  funext f
  exact ((adjunction M).homEquiv_unit X Y f).trans
    (congrArg (fun k => k ≫ f.hom) (adjunction_unit M X))

/-- Its entire inverse function is the original selected extension. -/
theorem freeHomEquiv_invFun (X : C) (Y : RightModule M) :
    (freeHomEquiv M X Y).invFun = extendFree M X Y := by rfl

/-- Extension after generator evaluation recovers the entire module morphism. -/
theorem extendFree_generator (X : C) (Y : RightModule M) (f : freeObject M X ⟶ Y) :
    extendFree M X Y (freeGenerator M X ≫ f.hom) = f := by
  exact (congrArg (extendFree M X Y)
    (congrFun (freeHomEquiv_toFun M X Y) f)).symm.trans
      ((freeHomEquiv M X Y).left_inv f)

/-- Generator evaluation after extension recovers the entire underlying arrow. -/
theorem freeGenerator_extend (X : C) (Y : RightModule M) (f : X ⟶ Y.X) :
    freeGenerator M X ≫ (extendFree M X Y f).hom = f := by
  exact (congrFun (freeHomEquiv_toFun M X Y) (extendFree M X Y f)).symm.trans
    ((freeHomEquiv M X Y).right_inv f)

/-- The original inverse Hom function is natural in its coefficient. -/
theorem freeHomEquiv_naturality_left {X X' : C} (f : X' ⟶ X)
    (Y : RightModule M) (g : X ⟶ Y.X) :
    (freeHomEquiv M X' Y).symm (f ≫ g) =
      freeMap M f ≫ (freeHomEquiv M X Y).symm g :=
  (adjunction M).homEquiv_naturality_left_symm f g

/-- The original forward Hom function is natural in its target module. -/
theorem freeHomEquiv_naturality_right (X : C) {Y Y' : RightModule M}
    (f : freeObject M X ⟶ Y) (g : Y ⟶ Y') :
    freeHomEquiv M X Y' (f ≫ g) = freeHomEquiv M X Y f ≫ g.hom :=
  (adjunction M).homEquiv_naturality_right f g

end CategoryTheory.RightModuleFree
