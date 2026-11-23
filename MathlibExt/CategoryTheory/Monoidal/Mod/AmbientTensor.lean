/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.IsoTransport
public import MathlibExt.CategoryTheory.Monoidal.Mod.Functor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Ambient tensor actions on actual associative modules

The coefficient algebra is an arbitrary internal monoid.  Tensoring a module
on the right leaves its action on the original module factor.  Tensoring on the
left transports that action through the actual inverse braid.  All coefficient
and module maps are retained, and the full tensor, unit and associator maps
are constructed as module morphisms.

No commutativity, model structure, weak-equivalence preservation or derived
tensor comparison is assumed or claimed here.  These are the actual ambient
tensor actions needed by the central homogeneous localization construction.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.AmbientTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (A : C) [MonObj A]

/-- The original associative action on an ambient right tensor. -/
def rightAction (U : C) (M : Mod C A) : A ⊗ (M.X ⊗ U) ⟶ M.X ⊗ U :=
  (α_ A M.X U).inv ≫ (M.mod.smul ▷ U)

theorem rightAction_one (U : C) (M : Mod C A) :
    (η[A] ▷ (M.X ⊗ U)) ≫ rightAction A U M = (λ_ (M.X ⊗ U)).hom := by
  unfold rightAction
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight,
    ModObj.one_smul_self]
  monoidal

theorem rightAction_mul (U : C) (M : Mod C A) :
    (μ[A] ▷ (M.X ⊗ U)) ≫ rightAction A U M =
      (α_ A A (M.X ⊗ U)).hom ≫ (A ◁ rightAction A U M) ≫ rightAction A U M := by
  have hp : (α_ (A ⊗ A) M.X U).inv ≫ ((α_ A A M.X).hom ▷ U) =
      (α_ A A (M.X ⊗ U)).hom ≫ (A ◁ (α_ A M.X U).inv) ≫
        (α_ A (A ⊗ M.X) U).inv := by monoidal
  have hs : (α_ A (A ⊗ M.X) U).inv ≫ ((A ◁ M.mod.smul) ▷ U) =
      (A ◁ (M.mod.smul ▷ U)) ≫ (α_ A M.X U).inv :=
    (associator_inv_naturality_middle A M.mod.smul U).symm
  unfold rightAction
  calc
    _ = (α_ (A ⊗ A) M.X U).inv ≫
        (((μ[A] ▷ M.X) ≫ M.mod.smul) ▷ U) := by
      rw [comp_whiskerRight, ← associator_inv_naturality_left_assoc]
    _ = (α_ (A ⊗ A) M.X U).inv ≫
        (((α_ A A M.X).hom ≫ (A ◁ M.mod.smul) ≫ M.mod.smul) ▷ U) := by
      rw [ModObj.mul_smul_self]
    _ = ((α_ (A ⊗ A) M.X U).inv ≫ ((α_ A A M.X).hom ▷ U)) ≫
        ((A ◁ M.mod.smul) ▷ U) ≫ (M.mod.smul ▷ U) := by
      simp only [comp_whiskerRight, Category.assoc]
    _ = (α_ A A (M.X ⊗ U)).hom ≫ (A ◁ (α_ A M.X U).inv) ≫
        (α_ A (A ⊗ M.X) U).inv ≫ ((A ◁ M.mod.smul) ▷ U) ≫ (M.mod.smul ▷ U) := by
      rw [hp]
      simp only [Category.assoc]
    _ = _ := by
      rw [reassoc_of% hs]
      simp only [whiskerLeft_comp, Category.assoc]

/-- An actual module with carrier `M.X ⊗ U`, for an arbitrary associative A. -/
@[reducible]
def rightModule (U : C) (M : Mod C A) : Mod C A where
  X := M.X ⊗ U
  mod :=
    { smul := rightAction A U M
      one_smul := rightAction_one A U M
      mul_smul := rightAction_mul A U M }

@[simp]
theorem rightModule_smul (U : C) (M : Mod C A) :
    (rightModule A U M).mod.smul = (α_ A M.X U).inv ≫ (M.mod.smul ▷ U) := rfl

/-- Every original module map is linear on the ambient right tensor. -/
theorem rightModule_map_linear (U : C) {M N : Mod C A} (f : M ⟶ N) :
    (rightModule A U M).mod.smul ≫ (f.hom ▷ U) =
      (A ◁ (f.hom ▷ U)) ≫ (rightModule A U N).mod.smul := by
  simp only [rightModule_smul]
  simp only [Category.assoc]
  rw [← comp_whiskerRight, IsModHom.smul_hom]
  change (α_ A M.X U).inv ≫ (((A ◁ f.hom) ≫ N.mod.smul) ▷ U) = _
  rw [comp_whiskerRight, ← associator_inv_naturality_middle_assoc]

/-- Every original coefficient map is linear on the ambient right tensor. -/
theorem rightModule_coefficient_linear {U V : C} (a : U ⟶ V) (M : Mod C A) :
    (rightModule A U M).mod.smul ≫ (M.X ◁ a) =
      (A ◁ (M.X ◁ a)) ≫ (rightModule A V M).mod.smul := by
  simp only [rightModule_smul]
  simp only [Category.assoc]
  rw [← whisker_exchange]
  change (α_ A M.X U).inv ≫ ((A ⊗ M.X) ◁ a) ≫ (M.mod.smul ▷ V) = _
  rw [← associator_inv_naturality_right_assoc]

/-- The right-tensor map retains both the original module and coefficient maps. -/
def rightMap {U V : C} (a : U ⟶ V) {M N : Mod C A} (f : M ⟶ N) :
    rightModule A U M ⟶ rightModule A V N :=
  Mod.Hom.mk' (f.hom ⊗ₘ a) (by
    change (rightModule A U M).mod.smul ≫ (f.hom ⊗ₘ a) =
      (A ◁ (f.hom ⊗ₘ a)) ≫ (rightModule A V N).mod.smul
    rw [tensorHom_def]
    rw [← Category.assoc, rightModule_map_linear]
    rw [Category.assoc, rightModule_coefficient_linear]
    rw [whiskerLeft_comp]
    simp only [Category.assoc])

@[simp]
theorem rightMap_hom {U V : C} (a : U ⟶ V) {M N : Mod C A} (f : M ⟶ N) :
    (rightMap A a f).hom = f.hom ⊗ₘ a := rfl

@[simp]
theorem rightMap_id (U : C) (M : Mod C A) : rightMap A (𝟙 U) (𝟙 M) = 𝟙 _ := by
  apply Mod.hom_ext
  simp

@[simp]
theorem rightMap_comp {U V W : C} (a : U ⟶ V) (b : V ⟶ W)
    {M N P : Mod C A} (f : M ⟶ N) (g : N ⟶ P) :
    rightMap A (a ≫ b) (f ≫ g) = rightMap A a f ≫ rightMap A b g := by
  apply Mod.hom_ext
  simp only [rightMap_hom, Mod.comp_hom', tensorHom_comp_tensorHom]

/-- Ambient right tensoring is an actual functor on all associative modules. -/
def rightFunctor (U : C) : Mod C A ⥤ Mod C A where
  obj := rightModule A U
  map f := rightMap A (𝟙 U) f
  map_id M := rightMap_id A U M
  map_comp f g := by
    simpa only [Category.id_comp] using (rightMap_comp A (𝟙 U) (𝟙 U) f g)

@[simp]
theorem rightFunctor_map_hom (U : C) {M N : Mod C A} (f : M ⟶ N) :
    ((rightFunctor A U).map f).hom = f.hom ▷ U := by
  simp only [rightFunctor, rightMap_hom, tensorHom_id]

/-- The actual ambient associator is linear for the associative module action. -/
def rightAssociateIso (U V : C) (M : Mod C A) :
    rightModule A V (rightModule A U M) ≅ rightModule A (U ⊗ V) M :=
  Mod.isoOfUnderlyingIso (α_ M.X U V) (by
    have hp : (α_ A (M.X ⊗ U) V).inv ≫ ((α_ A M.X U).inv ▷ V) ≫
        (α_ (A ⊗ M.X) U V).hom =
      (A ◁ (α_ M.X U V).hom) ≫ (α_ A M.X (U ⊗ V)).inv := by monoidal
    change ((α_ A (M.X ⊗ U) V).inv ≫
        (((α_ A M.X U).inv ≫ (M.mod.smul ▷ U)) ▷ V)) ≫
          (α_ M.X U V).hom =
      (A ◁ (α_ M.X U V).hom) ≫ (α_ A M.X (U ⊗ V)).inv ≫
        (M.mod.smul ▷ (U ⊗ V))
    simp only [comp_whiskerRight, Category.assoc]
    rw [associator_naturality_left]
    change (α_ A (M.X ⊗ U) V).inv ≫ ((α_ A M.X U).inv ▷ V) ≫
        (α_ (A ⊗ M.X) U V).hom ≫ (M.mod.smul ▷ (U ⊗ V)) = _
    simpa only [Category.assoc] using
      congrArg (fun t => t ≫ (M.mod.smul ▷ (U ⊗ V))) hp)

@[simp]
theorem rightAssociateIso_hom (U V : C) (M : Mod C A) :
    (rightAssociateIso A U V M).hom.hom = (α_ M.X U V).hom := rfl

@[simp]
theorem rightAssociateIso_inv (U V : C) (M : Mod C A) :
    (rightAssociateIso A U V M).inv.hom = (α_ M.X U V).inv := rfl

/-- The full ambient unit isomorphism is linear on the original module. -/
def rightUnitIso (M : Mod C A) : rightModule A (𝟙_ C) M ≅ M :=
  Mod.isoOfUnderlyingIso (ρ_ M.X) (by
    have hp : (α_ A M.X (𝟙_ C)).inv ≫ (ρ_ (A ⊗ M.X)).hom =
        A ◁ (ρ_ M.X).hom := by monoidal
    change ((α_ A M.X (𝟙_ C)).inv ≫ (M.mod.smul ▷ (𝟙_ C))) ≫
        (ρ_ M.X).hom = (A ◁ (ρ_ M.X).hom) ≫ M.mod.smul
    rw [Category.assoc, rightUnitor_naturality]
    change (α_ A M.X (𝟙_ C)).inv ≫ (ρ_ (A ⊗ M.X)).hom ≫ M.mod.smul = _
    simpa only [Category.assoc] using congrArg (fun t => t ≫ M.mod.smul) hp)

@[simp]
theorem rightUnitIso_hom (M : Mod C A) :
    (rightUnitIso A M).hom.hom = (ρ_ M.X).hom := rfl

@[simp]
theorem rightUnitIso_inv (M : Mod C A) :
    (rightUnitIso A M).inv.hom = (ρ_ M.X).inv := rfl

/-- Every actual coefficient arrow is natural on all original module arrows. -/
def rightCoefficientNatTrans {U V : C} (a : U ⟶ V) :
    rightFunctor A U ⟶ rightFunctor A V where
  app M := rightMap A a (𝟙 M)
  naturality {M N} f := by
    apply Mod.hom_ext
    simp only [Mod.comp_hom', rightFunctor_map_hom, rightMap_hom, Mod.id_hom', id_tensorHom]
    exact (whisker_exchange f.hom a).symm

/-- A coefficient isomorphism gives the original whole natural tensor isomorphism. -/
def rightCoefficientNatIso {U V : C} (e : U ≅ V) :
    rightFunctor A U ≅ rightFunctor A V where
  hom := rightCoefficientNatTrans A e.hom
  inv := rightCoefficientNatTrans A e.inv
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    apply Mod.hom_ext
    simp only [NatTrans.comp_app, rightCoefficientNatTrans, Mod.comp_hom', rightMap_hom,
      Mod.id_hom', id_tensorHom, NatTrans.id_app]
    simp
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    apply Mod.hom_ext
    simp only [NatTrans.comp_app, rightCoefficientNatTrans, Mod.comp_hom', rightMap_hom,
      Mod.id_hom', id_tensorHom, NatTrans.id_app]
    simp
    rfl

/-- Association is natural on all actual associative modules. -/
def rightAssociateNatIso (U V : C) :
    rightFunctor A U ⋙ rightFunctor A V ≅ rightFunctor A (U ⊗ V) :=
  NatIso.ofComponents (rightAssociateIso A U V) (fun {M N} f => by
    apply Mod.hom_ext
    simp only [Mod.comp_hom', Functor.comp_map, rightFunctor_map_hom, rightAssociateIso_hom]
    exact associator_naturality_left f.hom U V)

/-- The original right unit is natural on the entire actual module category. -/
def rightUnitNatIso : rightFunctor A (𝟙_ C) ≅ 𝟭 (Mod C A) :=
  NatIso.ofComponents (rightUnitIso A) (fun {M N} f => by
    apply Mod.hom_ext
    simp only [Mod.comp_hom', rightFunctor_map_hom, rightUnitIso_hom, Functor.id_map]
    exact rightUnitor_naturality f.hom)

section Braided

variable [BraidedCategory C]

/-- Left tensoring uses the existing lawful transport through the inverse braid. -/
@[reducible]
def tensorModule (U : C) (M : Mod C A) : Mod C A where
  X := U ⊗ M.X
  mod := (NativeOmegaRecovery.ModuleIsoTransport.object A
    (rightModule A U M) (β_ U M.X).symm).mod

/-- Both full module maps of the original inverse-braid transport. -/
def rightToLeftIso (U : C) (M : Mod C A) : rightModule A U M ≅ tensorModule A U M :=
  NativeOmegaRecovery.ModuleIsoTransport.iso A (rightModule A U M) (β_ U M.X).symm

@[simp]
theorem rightToLeftIso_hom (U : C) (M : Mod C A) :
    (rightToLeftIso A U M).hom.hom = (β_ U M.X).inv := rfl

@[simp]
theorem rightToLeftIso_inv (U : C) (M : Mod C A) :
    (rightToLeftIso A U M).inv.hom = (β_ U M.X).hom := rfl

/-- The whole left action preserves the original inverse scalar braid. -/
theorem module_smul (U : C) (M : Mod C A) :
    (tensorModule A U M).mod.smul =
      (α_ A U M.X).inv ≫ ((β_ U A).inv ▷ M.X) ≫
        (α_ U A M.X).hom ≫ (U ◁ M.mod.smul) := by
  change (NativeOmegaRecovery.ModuleIsoTransport.object A (rightModule A U M)
    (β_ U M.X).symm).mod.smul = _
  rw [NativeOmegaRecovery.ModuleIsoTransport.smul, rightModule_smul]
  simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc]
  rw [braiding_inv_naturality_left (X := A ⊗ M.X) M.mod.smul U,
    braiding_tensor_right_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]

/-- Both original maps act on the left tensor through the complete braid transport. -/
def map {U V : C} (a : U ⟶ V) {M N : Mod C A} (f : M ⟶ N) :
    tensorModule A U M ⟶ tensorModule A V N :=
  (rightToLeftIso A U M).inv ≫ rightMap A a f ≫ (rightToLeftIso A V N).hom

@[simp]
theorem map_hom {U V : C} (a : U ⟶ V) {M N : Mod C A} (f : M ⟶ N) :
    (map A a f).hom = a ⊗ₘ f.hom := by
  change (β_ U M.X).hom ≫ (f.hom ⊗ₘ a) ≫ (β_ V N.X).inv = _
  rw [← braiding_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

@[simp]
theorem map_id (U : C) (M : Mod C A) : map A (𝟙 U) (𝟙 M) = 𝟙 _ := by
  apply Mod.hom_ext
  simp

@[simp]
theorem map_comp {U V W : C} (a : U ⟶ V) (b : V ⟶ W)
    {M N P : Mod C A} (f : M ⟶ N) (g : N ⟶ P) :
    map A (a ≫ b) (f ≫ g) = map A a f ≫ map A b g := by
  apply Mod.hom_ext
  change (map A (a ≫ b) (f ≫ g)).hom = (map A a f).hom ≫ (map A b g).hom
  rw [map_hom, map_hom, map_hom, Mod.comp_hom', tensorHom_comp_tensorHom]

/-- Ambient left tensoring is an actual functor on all associative modules. -/
def functor (U : C) : Mod C A ⥤ Mod C A where
  obj := tensorModule A U
  map f := map A (𝟙 U) f
  map_id M := map_id A U M
  map_comp f g := by
    simpa only [Category.id_comp] using (map_comp A (𝟙 U) (𝟙 U) f g)

@[simp]
theorem functor_map_hom (U : C) {M N : Mod C A} (f : M ⟶ N) :
    ((functor A U).map f).hom = U ◁ f.hom := by
  simp only [functor, map_hom, id_tensorHom]

/-- Every original coordinate map acts on the actual tensor modules and all original module arrows. -/
def coefficientNatTrans {U V : C} (a : U ⟶ V) : functor A U ⟶ functor A V where
  app M := map A a (𝟙 M)
  naturality {_M _N} f := by
    apply Mod.hom_ext
    simp only [Mod.comp_hom', functor_map_hom, map_hom, Mod.id_hom', tensorHom_id]
    exact whisker_exchange a f.hom

/-- Left and right ambient tensoring are identified by the same original braid. -/
def rightToLeftNatIso (U : C) : rightFunctor A U ≅ functor A U :=
  NatIso.ofComponents (rightToLeftIso A U) (fun {M N} f => by
    apply Mod.hom_ext
    simp only [Mod.comp_hom', rightFunctor_map_hom, rightToLeftIso_hom, functor_map_hom]
    exact braiding_inv_naturality_left f.hom U)

end Braided

end CategoryTheory.Mod.AmbientTensor
