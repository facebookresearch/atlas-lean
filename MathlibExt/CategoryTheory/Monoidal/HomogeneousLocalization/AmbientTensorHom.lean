/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Authors: @toskua, Avocado, Codex
-/

-- Authors: @toskua, Avocado, Codex
module

public import MathlibExt.CategoryTheory.Monoidal.Mod.AmbientTensor
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import MathlibExt.CategoryTheory.Monoidal.Mod.InternalHom

/-!
# Ambient tensor and internal Hom on actual associative modules

The ambient internal Hom carries the literal coefficient shuffle, evaluation
and target action.  Its two module laws use the original unit/multiplication
and braiding coherence; the coefficient monoid need not be commutative.
The construction generalizes the auxiliary action from the original module
internal-Hom source without changing its maps.  Every original target map
and contravariant tensor-coordinate map is retained.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory.HomogeneousLocalization.AmbientTensorHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] (A : C) [MonObj A]

/-- The actual associative action uses the shared original monoid auxiliary producer. -/
def cotensorModule (U : C) (N : Mod C A) : Mod C A :=
  Mod.internalHomAuxiliaryOfMonObj A U N

/-- The coefficient action retains the original shuffle, evaluation and target action. -/
theorem cotensorModule_smul (U : C) (N : Mod C A) :
    (cotensorModule A U N).mod.smul = MonoidalClosed.curry
      ((α_ U A ((ihom U).obj N.X)).inv ≫
        ((β_ U A).hom ▷ (ihom U).obj N.X) ≫
        (α_ A U ((ihom U).obj N.X)).hom ≫
        (A ◁ (ihom.ev U).app N.X) ≫ N.mod.smul) := rfl

/-- Every original target-module map is linear on the ambient internal Hom. -/
def cotensorMap (U : C) {N N' : Mod C A} (g : N ⟶ N') :
    cotensorModule A U N ⟶ cotensorModule A U N' :=
  Mod.internalHomAuxiliaryOfMonObjMap A g U

@[simp]
theorem cotensorMap_hom (U : C) {N N' : Mod C A} (g : N ⟶ N') :
    (cotensorMap A U g).hom = (ihom U).map g.hom := rfl

/-- Every target identity and composition remains in the actual internal-Hom functor. -/
def rightFunctor (U : C) : Mod C A ⥤ Mod C A where
  obj := cotensorModule A U
  map := cotensorMap A U
  map_id N := by
    apply Mod.hom_ext
    simp only [cotensorMap_hom, Mod.id_hom', Functor.map_id]
    rfl
  map_comp f g := by
    apply Mod.hom_ext
    simp only [cotensorMap_hom, Mod.comp_hom', Functor.map_comp]

/-- The underlying right functor is literally the original ambient internal-Hom functor. -/
def underlyingRightNatIso (U : C) :
    rightFunctor A U ⋙ Mod.forget A ≅ Mod.forget A ⋙ ihom U := Iso.refl _

/-- The original coefficient shuffle in both directions. -/
def exchangeIso (U X : C) : A ⊗ (U ⊗ X) ≅ U ⊗ (A ⊗ X) :=
  (α_ A U X).symm ≪≫ whiskerRightIso (β_ U A).symm X ≪≫ α_ U A X

omit [MonoidalClosed C] [MonObj A] in
/-- The inverse shuffle keeps every original input map and both tensor orders. -/
theorem exchangeIso_inv_naturality (U : C) {X Y : C} (f : X ⟶ Y) :
    (U ◁ (A ◁ f)) ≫ (exchangeIso A U Y).inv =
      (exchangeIso A U X).inv ≫ (A ◁ (U ◁ f)) := by
  dsimp only [exchangeIso, Iso.trans_inv, Iso.symm_inv, whiskerRightIso]
  slice_lhs 1 2 => rw [associator_inv_naturality_right]
  slice_lhs 2 3 => rw [whisker_exchange]
  slice_lhs 3 4 => rw [associator_naturality_right]
  monoidal

omit [MonoidalClosed C] in
/-- The ambient tensor action is the same original forward coefficient shuffle. -/
theorem tensorModule_smul_exchange (U : C) (M : Mod C A) :
    (Mod.AmbientTensor.tensorModule A U M).mod.smul =
      (exchangeIso A U M.X).hom ≫ (U ◁ M.mod.smul) := by
  rw [Mod.AmbientTensor.module_smul]
  simp only [exchangeIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso, Category.assoc]

/-- The ambient internal-Hom action uses the same inverse shuffle and evaluation. -/
theorem cotensorModule_smul_exchange (U : C) (N : Mod C A) :
    (cotensorModule A U N).mod.smul = MonoidalClosed.curry
      ((exchangeIso A U ((ihom U).obj N.X)).inv ≫
        (A ◁ (ihom.ev U).app N.X) ≫ N.mod.smul) := by
  rw [cotensorModule_smul]
  apply congrArg MonoidalClosed.curry
  simp only [exchangeIso, Iso.trans_inv, Iso.symm_inv, whiskerRightIso, Category.assoc]

/-- Original currying preserves and detects the two actual module-linearity equations. -/
theorem curry_linear_iff (U : C) (M N : Mod C A) (f : U ⊗ M.X ⟶ N.X) :
    M.mod.smul ≫ MonoidalClosed.curry f =
        (A ◁ MonoidalClosed.curry f) ≫ (cotensorModule A U N).mod.smul ↔
      (Mod.AmbientTensor.tensorModule A U M).mod.smul ≫ f = (A ◁ f) ≫ N.mod.smul := by
  have hr : MonoidalClosed.uncurry
      ((A ◁ MonoidalClosed.curry f) ≫ (cotensorModule A U N).mod.smul) =
        (exchangeIso A U M.X).inv ≫ (A ◁ f) ≫ N.mod.smul := by
    rw [MonoidalClosed.uncurry_natural_left, cotensorModule_smul_exchange,
      MonoidalClosed.uncurry_curry]
    rw [← Category.assoc, ← Category.assoc, exchangeIso_inv_naturality, Category.assoc,
      Category.assoc]
    slice_lhs 2 3 => rw [← whiskerLeft_comp, MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  constructor
  · intro h
    have h' := congrArg MonoidalClosed.uncurry h
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry, hr] at h'
    rw [tensorModule_smul_exchange]
    rw [Category.assoc, h', ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · intro h
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry, hr]
    rw [← h, tensorModule_smul_exchange, ← Category.assoc, Iso.inv_hom_id_assoc]

/-- The original tensor-Hom curry is an actual associative module map. -/
def curryMap (U : C) {M N : Mod C A} (f : Mod.AmbientTensor.tensorModule A U M ⟶ N) :
    M ⟶ cotensorModule A U N :=
  Mod.Hom.mk' (MonoidalClosed.curry f.hom) ((curry_linear_iff A U M N f.hom).mpr
    (IsModHom.smul_hom (A := A) (f := f.hom)))

/-- The original tensor-Hom uncurry is an actual associative module map. -/
def uncurryMap (U : C) {M N : Mod C A} (g : M ⟶ cotensorModule A U N) :
    Mod.AmbientTensor.tensorModule A U M ⟶ N :=
  Mod.Hom.mk' (MonoidalClosed.uncurry g.hom) ((curry_linear_iff A U M N
    (MonoidalClosed.uncurry g.hom)).mp (by
      rw [MonoidalClosed.curry_uncurry]
      exact IsModHom.smul_hom (A := A) (f := g.hom)))

/-- Both original tensor-Hom inverse functions retain the actual associative module actions. -/
def homEquiv (U : C) (M N : Mod C A) :
    (Mod.AmbientTensor.tensorModule A U M ⟶ N) ≃ (M ⟶ cotensorModule A U N) where
  toFun := curryMap A U
  invFun := uncurryMap A U
  left_inv f := by
    apply Mod.hom_ext
    exact MonoidalClosed.uncurry_curry f.hom
  right_inv g := by
    apply Mod.hom_ext
    exact MonoidalClosed.curry_uncurry g.hom

/-- The full forward function is the original ambient curry on the unchanged carrier map. -/
theorem homEquiv_hom (U : C) (M N : Mod C A) (f : Mod.AmbientTensor.tensorModule A U M ⟶ N) :
    (homEquiv A U M N f).hom = MonoidalClosed.curry f.hom := rfl

/-- The full inverse function is the original ambient uncurry on the same carrier map. -/
theorem homEquiv_symm_hom (U : C) (M N : Mod C A) (g : M ⟶ cotensorModule A U N) :
    ((homEquiv A U M N).symm g).hom = MonoidalClosed.uncurry g.hom := rfl

/-- The whole original ambient tensor/internal-Hom adjunction on associative modules. -/
def adjunction (U : C) : Mod.AmbientTensor.functor A U ⊣ rightFunctor A U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv A U
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        apply Mod.hom_ext
        change MonoidalClosed.uncurry (f.hom ≫ g.hom) =
          ((Mod.AmbientTensor.functor A U).map f).hom ≫ MonoidalClosed.uncurry g.hom
        rw [Mod.AmbientTensor.functor_map_hom]
        exact MonoidalClosed.uncurry_natural_left f.hom g.hom
      homEquiv_naturality_right := by
        intro M N N' f g
        apply Mod.hom_ext
        exact MonoidalClosed.curry_natural_right f.hom g.hom }

/-- The actual adjunction retains the same entire original Hom equivalence. -/
theorem adjunction_homEquiv (U : C) (M N : Mod C A) :
    (adjunction A U).homEquiv M N = homEquiv A U M N := by
  simp only [adjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- The actual module evaluation is the original whole adjunction counit. -/
def evaluation (U : C) (N : Mod C A) : Mod.AmbientTensor.tensorModule A U (cotensorModule A U N) ⟶ N :=
  (adjunction A U).counit.app N

/-- The original module evaluation retains the literal ambient evaluation map. -/
theorem evaluation_hom (U : C) (N : Mod C A) :
    (evaluation A U N).hom = (ihom.ev U).app N.X := by
  change MonoidalClosed.uncurry (𝟙 ((ihom U).obj N.X)) = _
  exact MonoidalClosed.uncurry_id_eq_ev U N.X

/-- The original module coevaluation retains the literal ambient coevaluation map. -/
theorem coevaluation_hom (U : C) (M : Mod C A) :
    ((adjunction A U).unit.app M).hom = (ihom.coev U).app M.X := by
  change MonoidalClosed.curry (𝟙 (U ⊗ M.X)) = _
  exact MonoidalClosed.curry_id_eq_coev U M.X

/-- Every original contravariant coordinate arrow is linear for the actual associative action. -/
def preMap {U V : C} (a : V ⟶ U) (N : Mod C A) :
    cotensorModule A U N ⟶ cotensorModule A V N :=
  Mod.Hom.mk' ((MonoidalClosed.pre a).app N.X) (by
    let HU := (ihom U).obj N.X
    let HV := (ihom V).obj N.X
    let qU : U ⊗ (A ⊗ HU) ⟶ N.X := (α_ U A HU).inv ≫
      ((β_ U A).hom ▷ HU) ≫ (α_ A U HU).hom ≫
      (A ◁ (ihom.ev U).app N.X) ≫ N.mod.smul
    let qV : V ⊗ (A ⊗ HV) ⟶ N.X := (α_ V A HV).inv ≫
      ((β_ V A).hom ▷ HV) ≫ (α_ A V HV).hom ≫
      (A ◁ (ihom.ev V).app N.X) ≫ N.mod.smul
    change MonoidalClosed.curry qU ≫ (MonoidalClosed.pre a).app N.X =
      (A ◁ (MonoidalClosed.pre a).app N.X) ≫ MonoidalClosed.curry qV
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
    change (a ▷ (A ⊗ HU)) ≫ qU =
      (V ◁ (A ◁ (MonoidalClosed.pre a).app N.X)) ≫ qV
    slice_rhs 1 2 => rw [associator_inv_naturality_right]
    slice_rhs 2 3 => rw [whisker_exchange]
    slice_rhs 3 4 => rw [associator_naturality_right]
    slice_rhs 4 5 => rw [← whiskerLeft_comp,
      MonoidalClosed.id_tensor_pre_app_comp_ev, whiskerLeft_comp]
    slice_lhs 1 2 => rw [associator_inv_naturality_left]
    slice_lhs 2 3 => rw [← comp_whiskerRight, braiding_naturality_left, comp_whiskerRight]
    slice_lhs 3 4 => rw [associator_naturality_middle]
    dsimp only [qU, qV, HU, HV]
    monoidal)

@[simp]
theorem preMap_hom {U V : C} (a : V ⟶ U) (N : Mod C A) :
    (preMap A a N).hom = (MonoidalClosed.pre a).app N.X := rfl

/-- All original coordinate and target arrows give the same natural internal-Hom comparison. -/
def coordinateNatTrans {U V : C} (a : V ⟶ U) : rightFunctor A U ⟶ rightFunctor A V where
  app := preMap A a
  naturality {_N _N'} g := by
    apply Mod.hom_ext
    change (ihom U).map g.hom ≫ (MonoidalClosed.pre a).app _ =
      (MonoidalClosed.pre a).app _ ≫ (ihom V).map g.hom
    exact (MonoidalClosed.pre a).naturality g.hom

/-- The original coordinate identity acts identically on every actual module. -/
theorem coordinateNatTrans_id (U : C) : coordinateNatTrans A (𝟙 U) = 𝟙 (rightFunctor A U) := by
  apply NatTrans.ext
  funext N
  apply Mod.hom_ext
  simp only [coordinateNatTrans, preMap_hom, MonoidalClosed.pre_id, NatTrans.id_app, Mod.id_hom']
  rfl

/-- The same original coordinate composition acts in its original contravariant order. -/
theorem coordinateNatTrans_comp {U V W : C} (a : W ⟶ V) (b : V ⟶ U) :
    coordinateNatTrans A (a ≫ b) = coordinateNatTrans A b ≫ coordinateNatTrans A a := by
  apply NatTrans.ext
  funext N
  apply Mod.hom_ext
  simp only [coordinateNatTrans, preMap_hom, MonoidalClosed.pre_map, NatTrans.comp_app, Mod.comp_hom']

/-- All original coordinate and target arrows form the actual ambient internal-Hom bifunctor. -/
def rightBifunctor : Cᵒᵖ ⥤ (Mod C A ⥤ Mod C A) where
  obj U := rightFunctor A U.unop
  map f := coordinateNatTrans A f.unop
  map_id U := coordinateNatTrans_id A U.unop
  map_comp f g := coordinateNatTrans_comp A g.unop f.unop

/-- The actual coordinate comparison is the mate of the same original ambient tensor arrow. -/
theorem coordinate_mate {U V : C} (a : V ⟶ U) (M N : Mod C A)
    (f : Mod.AmbientTensor.tensorModule A U M ⟶ N) :
    (homEquiv A U M N f) ≫ preMap A a N =
      homEquiv A V M N (Mod.AmbientTensor.map A a (𝟙 M) ≫ f) := by
  apply Mod.hom_ext
  change MonoidalClosed.curry f.hom ≫ (MonoidalClosed.pre a).app N.X =
    MonoidalClosed.curry ((Mod.AmbientTensor.map A a (𝟙 M)).hom ≫ f.hom)
  rw [Mod.AmbientTensor.map_hom, Mod.id_hom', tensorHom_id]
  exact MonoidalClosed.curry_pre_app a f.hom

/-- All original ambient tensor-coordinate and module arrows form the actual curried tensor functor. -/
def leftBifunctor : C ⥤ (Mod C A ⥤ Mod C A) where
  obj := Mod.AmbientTensor.functor A
  map := Mod.AmbientTensor.coefficientNatTrans A
  map_id U := by
    apply NatTrans.ext
    funext M
    exact Mod.AmbientTensor.map_id A U M
  map_comp f g := by
    apply NatTrans.ext
    funext M
    change Mod.AmbientTensor.map A (f ≫ g) (𝟙 M) =
      Mod.AmbientTensor.map A f (𝟙 M) ≫ Mod.AmbientTensor.map A g (𝟙 M)
    simpa only [Category.id_comp] using (Mod.AmbientTensor.map_comp A f g (𝟙 M) (𝟙 M))

/-- Both original right variables retain their literal ambient internal-Hom maps under forgetting. -/
def underlyingRightBifunctorIso :
    rightBifunctor A ⋙ (Functor.whiskeringRight (Mod C A) (Mod C A) C).obj (Mod.forget A) ≅
      MonoidalClosed.internalHom ⋙ (Functor.whiskeringLeft (Mod C A) C C).obj (Mod.forget A) := Iso.refl _

end CategoryTheory.HomogeneousLocalization.AmbientTensorHom
