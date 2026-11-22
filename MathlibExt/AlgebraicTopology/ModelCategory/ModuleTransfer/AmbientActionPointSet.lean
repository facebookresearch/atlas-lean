/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.DerivedAmbientAction
public import Mathlib.CategoryTheory.Localization.Trifunctor

/-!
# The original associative module action associator

The entire original right action is transported through the actual braid.
The resulting module morphism has precisely the ambient associator as its
underlying map, with the original module action on every coefficient.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory Functor
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.AmbientActionPointSet

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  {A : C} [MonObj A]

open CategoryTheory.HomogeneousLocalization
open CategoryTheory.HomogeneousLocalization.AmbientTensorHom

/-- The whole original right module associator gives the actual left module associator. -/
def associateNatIso (U V : C) :
    Mod.AmbientTensor.functor A V ⋙ Mod.AmbientTensor.functor A U ≅ Mod.AmbientTensor.functor A (U ⊗ V) :=
  isoWhiskerRight (Mod.AmbientTensor.rightToLeftNatIso A V).symm (Mod.AmbientTensor.functor A U) ≪≫
    isoWhiskerLeft (Mod.AmbientTensor.rightFunctor A V) (Mod.AmbientTensor.rightToLeftNatIso A U).symm ≪≫
    Mod.AmbientTensor.rightAssociateNatIso A V U ≪≫
    Mod.AmbientTensor.rightCoefficientNatIso A (β_ U V).symm ≪≫
    Mod.AmbientTensor.rightToLeftNatIso A (U ⊗ V)

/-- The full transported module associator retains precisely the original ambient inverse associator. -/
theorem associateNatIso_hom (U V : C) (N : Mod C A) :
    ((associateNatIso (A := A) U V).hom.app N).hom = (α_ U V N.X).inv := by
  have h : U ◁ (β_ V N.X).hom ≫ (β_ U (N.X ⊗ V)).hom ≫ (α_ N.X V U).hom ≫
      N.X ◁ (β_ U V).inv ≫ (β_ (U ⊗ V) N.X).inv = (α_ U V N.X).inv := by
    rw [braiding_tensor_right_hom, braiding_tensor_left_inv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      whiskerLeft_hom_inv_assoc, hom_inv_whiskerRight_assoc]
  dsimp [associateNatIso, Mod.AmbientTensor.rightToLeftNatIso,
    Mod.AmbientTensor.rightAssociateNatIso, Mod.AmbientTensor.rightCoefficientNatIso,
    Mod.AmbientTensor.rightCoefficientNatTrans]
  simp only [Mod.AmbientTensor.functor_map_hom, Mod.AmbientTensor.rightToLeftIso_inv,
    Mod.id_hom', id_tensorHom]
  exact h

/-- The inverse transported module map is exactly the original ambient associator. -/
theorem associateNatIso_inv (U V : C) (N : Mod C A) :
    ((associateNatIso (A := A) U V).inv.app N).hom = (α_ U V N.X).hom := by
  have h : (Mod.forget A).mapIso ((associateNatIso (A := A) U V).app N) = (α_ U V N.X).symm :=
    Iso.ext (associateNatIso_hom U V N)
  exact congrArg Iso.inv h

/-- The original ambient associator is an isomorphism of the actual associative modules. -/
def associate (U V : C) (N : Mod C A) :
    Mod.AmbientTensor.tensorModule A (U ⊗ V) N ≅
      Mod.AmbientTensor.tensorModule A U (Mod.AmbientTensor.tensorModule A V N) :=
  ((associateNatIso (A := A) U V).app N).symm

/-- The actual module associator has the literal ambient associator as its underlying map. -/
theorem associate_hom (U V : C) (N : Mod C A) :
    (associate (A := A) U V N).hom.hom = (α_ U V N.X).hom :=
  associateNatIso_inv U V N

/-- The entire original associator is natural on both coefficients and all associative modules. -/
def sourceAssociator :
    bifunctorComp₁₂ (curriedTensor C) (leftBifunctor A) ≅
      bifunctorComp₂₃ (leftBifunctor A) (leftBifunctor A) :=
  NatIso.ofComponents
    (fun U => NatIso.ofComponents (fun V => (associateNatIso (A := A) U V).symm) (by
      intro V V' f
      apply NatTrans.ext
      funext N
      apply Mod.hom_ext
      change (Mod.AmbientTensor.map A (U ◁ f) (𝟙 N)).hom ≫
          ((associateNatIso (A := A) U V').inv.app N).hom =
        ((associateNatIso (A := A) U V).inv.app N).hom ≫
          ((Mod.AmbientTensor.functor A U).map (Mod.AmbientTensor.map A f (𝟙 N))).hom
      simp only [Mod.AmbientTensor.map_hom, Mod.id_hom', tensorHom_id,
        Mod.AmbientTensor.functor_map_hom, associateNatIso_inv]
      exact associator_naturality_middle U f N.X)) (by
    intro U U' f
    apply NatTrans.ext
    funext V
    apply NatTrans.ext
    funext N
    apply Mod.hom_ext
    change (Mod.AmbientTensor.map A (f ▷ V) (𝟙 N)).hom ≫
        ((associateNatIso (A := A) U' V).inv.app N).hom =
      ((associateNatIso (A := A) U V).inv.app N).hom ≫
        (Mod.AmbientTensor.map A f (𝟙 (Mod.AmbientTensor.tensorModule A V N))).hom
    simp only [Mod.AmbientTensor.map_hom, Mod.id_hom', tensorHom_id, associateNatIso_inv]
    exact associator_naturality_left f V N.X)

/-- The whole three-variable natural associator keeps the actual original associator component. -/
theorem sourceAssociator_hom (U V : C) (N : Mod C A) :
    ((((sourceAssociator (A := A)).hom.app U).app V).app N).hom = (α_ U V N.X).hom :=
  associateNatIso_inv U V N

/-- The unit is the exact original module unit, constructed through its original braid. -/
def unitNatIso : Mod.AmbientTensor.functor A (𝟙_ C) ≅ 𝟭 (Mod C A) :=
  DerivedAmbientAction.pointSetLeftUnit

/-- The module unit retains the literal ambient left unitor as its underlying map. -/
theorem unitNatIso_hom (N : Mod C A) :
    ((unitNatIso (A := A)).hom.app N).hom = (λ_ N.X).hom := by
  have h : (β_ (𝟙_ C) N.X).hom ≫ (ρ_ N.X).hom = (λ_ N.X).hom := by
    rw [braiding_tensorUnit_left]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp [unitNatIso, DerivedAmbientAction.pointSetLeftUnit,
    Mod.AmbientTensor.rightToLeftNatIso, Mod.AmbientTensor.rightUnitNatIso]
  exact h

/-- The actual original module associator satisfies the full coefficient/module pentagon. -/
theorem pentagon (U V W : C) (N : Mod C A) :
    (associate (A := A) (U ⊗ V) W N).hom ≫
        (associate U V (Mod.AmbientTensor.tensorModule A W N)).hom =
      Mod.AmbientTensor.map A (α_ U V W).hom (𝟙 N) ≫
        (associate U (V ⊗ W) N).hom ≫
        (Mod.AmbientTensor.functor A U).map (associate V W N).hom := by
  have h : (α_ (U ⊗ V) W N.X).hom ≫ (α_ U V (W ⊗ N.X)).hom =
      (α_ U V W).hom ▷ N.X ≫ (α_ U (V ⊗ W) N.X).hom ≫ U ◁ (α_ V W N.X).hom := by
    monoidal
  apply Mod.hom_ext
  simp only [Mod.comp_hom', associate_hom, Mod.AmbientTensor.map_hom,
    Mod.id_hom', tensorHom_id, Mod.AmbientTensor.functor_map_hom]
  exact h

/-- The original coefficient left unit agrees with the actual module unit and associator. -/
theorem left_unit (U : C) (N : Mod C A) :
    (associate (A := A) (𝟙_ C) U N).hom ≫
        (unitNatIso (A := A)).hom.app (Mod.AmbientTensor.tensorModule A U N) =
      Mod.AmbientTensor.map A (λ_ U).hom (𝟙 N) := by
  have h : (α_ (𝟙_ C) U N.X).hom ≫ (λ_ (U ⊗ N.X)).hom = (λ_ U).hom ▷ N.X := by
    monoidal
  apply Mod.hom_ext
  simp only [Mod.comp_hom', associate_hom, unitNatIso_hom,
    Mod.AmbientTensor.map_hom, Mod.id_hom', tensorHom_id]
  exact h

/-- The original coefficient right unit agrees with the actual module unit and associator. -/
theorem right_unit (U : C) (N : Mod C A) :
    (associate (A := A) U (𝟙_ C) N).hom ≫
        (Mod.AmbientTensor.functor A U).map ((unitNatIso (A := A)).hom.app N) =
      Mod.AmbientTensor.map A (ρ_ U).hom (𝟙 N) := by
  have h : (α_ U (𝟙_ C) N.X).hom ≫ U ◁ (λ_ N.X).hom = (ρ_ U).hom ▷ N.X := by
    monoidal
  apply Mod.hom_ext
  simp only [Mod.comp_hom', associate_hom, Mod.AmbientTensor.functor_map_hom,
    unitNatIso_hom, Mod.AmbientTensor.map_hom, Mod.id_hom', tensorHom_id]
  exact h

end HomotopicalAlgebra.ModuleTransfer.AmbientActionPointSet
