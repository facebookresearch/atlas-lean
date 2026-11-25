/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Bimodule
public import MathlibExt.Algebra.Module.NatInt

/-!
# Original actions of native enveloping-module objects

An object of `ModuleCat (R ⊗[ℤ] Rᵐᵒᵖ)` has its two actual endpoint actions
by restriction along the native tensor inclusions. Their recombination by
`TensorProduct.Algebra.module` recovers the stored original module. No new
bimodule category, action model, or comparison is given as data.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe r v

namespace ModuleCat.Bimodule

variable (R : Type r) [Ring R]

/-- The original left action is restriction along the first native tensor inclusion. -/
def leftModule (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) : Module R X :=
  Module.compHom X
    (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℤ] Rᵐᵒᵖ)

/-- The original right action is restriction along the second native tensor inclusion. -/
def rightModule (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) : Module Rᵐᵒᵖ X :=
  Module.compHom X
    (Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[ℤ] R ⊗[ℤ] Rᵐᵒᵖ).toRingHom

/-- The endpoint restrictions of the given native enveloping action commute. -/
theorem commute (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    letI := leftModule R X
    letI := rightModule R X
    SMulCommClass R Rᵐᵒᵖ X := by
  let := leftModule R X
  let := rightModule R X
  refine ⟨fun a b x => ?_⟩
  change (a ⊗ₜ[ℤ] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[ℤ] b) • x) =
    ((1 : R) ⊗ₜ[ℤ] b) • ((a ⊗ₜ[ℤ] (1 : Rᵐᵒᵖ)) • x)
  rw [← mul_smul, ← mul_smul]
  apply congrArg (fun z : R ⊗[ℤ] Rᵐᵒᵖ => z • x)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The original stored pure enveloping scalar is the two actual endpoint actions. -/
theorem smul_tmul (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ))
    (a : R) (b : Rᵐᵒᵖ) (x : X) :
    (leftModule R X).smul a ((rightModule R X).smul b x) =
      X.isModule.smul (a ⊗ₜ[ℤ] b) x := by
  change (a ⊗ₜ[ℤ] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[ℤ] b) • x) = (a ⊗ₜ[ℤ] b) • x
  rw [← mul_smul]
  apply congrArg (fun z : R ⊗[ℤ] Rᵐᵒᵖ => z • x)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Recombine the actual endpoint restrictions with the native module constructor. -/
def reconstructedModule (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    Module (R ⊗[ℤ] Rᵐᵒᵖ) X := by
  letI := leftModule R X
  letI := rightModule R X
  letI := commute R X
  exact TensorProduct.Algebra.module

/-- The native reconstructed module acts by the original stored scalar function. -/
theorem reconstructedModule_smul (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ))
    (z : R ⊗[ℤ] Rᵐᵒᵖ) (x : X) :
    (reconstructedModule R X).smul z x = X.isModule.smul z x := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change (a ⊗ₜ[ℤ] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[ℤ] b) • x) =
      (a ⊗ₜ[ℤ] b) • x
    rw [← mul_smul]
    apply congrArg (fun z : R ⊗[ℤ] Rᵐᵒᵖ => z • x)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add z w hz hw =>
    calc
      (reconstructedModule R X).smul (z + w) x =
          (reconstructedModule R X).smul z x + (reconstructedModule R X).smul w x :=
        (reconstructedModule R X).add_smul z w x
      _ = X.isModule.smul z x + X.isModule.smul w x := congrArg₂ (· + ·) hz hw
      _ = X.isModule.smul (z + w) x := (X.isModule.add_smul z w x).symm

/-- Equality of the actual stored native module data is earned from its original action. -/
theorem reconstructedModule_eq (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    reconstructedModule R X = X.isModule :=
  Module.ext' _ _ (reconstructedModule_smul R X)

/-- The native category object with the same carrier and the recombined module. -/
def reconstructedObject (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ) :=
  letI := reconstructedModule R X
  ModuleCat.of (R ⊗[ℤ] Rᵐᵒᵖ) X

/-- The actual identity-coordinate iso to the original native object. -/
def reconstructedIso (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    reconstructedObject R X ≅ X where
  hom := @ModuleCat.ofHom (R ⊗[ℤ] Rᵐᵒᵖ) _
    (reconstructedObject R X).carrier X.carrier
    (reconstructedObject R X).isAddCommGroup (reconstructedObject R X).isModule
    X.isAddCommGroup X.isModule
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun z x => reconstructedModule_smul R X z x }
  inv := @ModuleCat.ofHom (R ⊗[ℤ] Rᵐᵒᵖ) _
    X.carrier (reconstructedObject R X).carrier
    X.isAddCommGroup X.isModule
    (reconstructedObject R X).isAddCommGroup (reconstructedObject R X).isModule
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun z x => (reconstructedModule_smul R X z x).symm }
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

@[simp]
theorem reconstructedIso_hom_apply (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) (x : X) :
    (reconstructedIso R X).hom.hom x = x := rfl

@[simp]
theorem reconstructedIso_inv_apply (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) (x : X) :
    (reconstructedIso R X).inv.hom x = x := rfl

/-- The actual original morphism transported to the recombined native modules. -/
def reconstructedMap {X Y : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    reconstructedObject R X ⟶ reconstructedObject R Y :=
  (reconstructedIso R X).hom ≫ f ≫ (reconstructedIso R Y).inv

@[simp]
theorem reconstructedMap_apply {X Y : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)}
    (f : X ⟶ Y) (x : X) : (reconstructedMap R f).hom x = f.hom x := rfl

/-- The native algebra ground field and the original supplied integer
module field are compatible with the fixed original ring action. -/
theorem int_isScalarTower (M : Type v) [AddCommGroup M]
    [d : Module ℤ M] [dRM : Module R M] :
    @IsScalarTower ℤ R M (Algebra.toModule : Module ℤ R).toSMul
      dRM.toSMul d.toSMul :=
  Module.intModule_isScalarTower (dRM := dRM)
    (Algebra.toModule : Module ℤ R) d

section GivenActions

variable (M : Type v) [AddCommGroup M] [givenIntegerModule : Module ℤ M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
  [IsScalarTower ℤ R M] [IsScalarTower ℤ Rᵐᵒᵖ M]

include givenIntegerModule

omit [IsScalarTower ℤ R M] [IsScalarTower ℤ Rᵐᵒᵖ M] in
/-- The first restriction of the native tensor module recovers the given left action. -/
theorem leftModule_ofTensor :
    letI : IsScalarTower ℤ R M := AddCommGroup.intIsScalarTower
    letI : IsScalarTower ℤ Rᵐᵒᵖ M := AddCommGroup.intIsScalarTower
    letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) M := @TensorProduct.Algebra.module ℤ R Rᵐᵒᵖ M
      inferInstance (inferInstance : AddCommMonoid M) givenIntegerModule
      inferInstance inferInstance (inferInstance : Module R M)
      (inferInstance : Module Rᵐᵒᵖ M) inferInstance inferInstance
      (@int_isScalarTower R _ M _ givenIntegerModule (inferInstance : Module R M))
      (@int_isScalarTower Rᵐᵒᵖ _ M _ givenIntegerModule (inferInstance : Module Rᵐᵒᵖ M))
      inferInstance
    leftModule R (ModuleCat.of (R ⊗[ℤ] Rᵐᵒᵖ) M) = (inferInstance : Module R M) := by
  let : IsScalarTower ℤ R M := AddCommGroup.intIsScalarTower
  let : IsScalarTower ℤ Rᵐᵒᵖ M := AddCommGroup.intIsScalarTower
  let : Module (R ⊗[ℤ] Rᵐᵒᵖ) M := @TensorProduct.Algebra.module ℤ R Rᵐᵒᵖ M
      inferInstance (inferInstance : AddCommMonoid M) givenIntegerModule
      inferInstance inferInstance (inferInstance : Module R M)
      (inferInstance : Module Rᵐᵒᵖ M) inferInstance inferInstance
      (@int_isScalarTower R _ M _ givenIntegerModule (inferInstance : Module R M))
      (@int_isScalarTower Rᵐᵒᵖ _ M _ givenIntegerModule (inferInstance : Module Rᵐᵒᵖ M))
      inferInstance
  apply Module.ext'
  intro r m
  change r • ((1 : Rᵐᵒᵖ) • m) = r • m
  exact congrArg (fun x : M => r • x) (one_smul Rᵐᵒᵖ m)

omit [IsScalarTower ℤ R M] [IsScalarTower ℤ Rᵐᵒᵖ M] in
/-- The second restriction likewise recovers the original right action. -/
theorem rightModule_ofTensor :
    letI : IsScalarTower ℤ R M := AddCommGroup.intIsScalarTower
    letI : IsScalarTower ℤ Rᵐᵒᵖ M := AddCommGroup.intIsScalarTower
    letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) M := @TensorProduct.Algebra.module ℤ R Rᵐᵒᵖ M
      inferInstance (inferInstance : AddCommMonoid M) givenIntegerModule
      inferInstance inferInstance (inferInstance : Module R M)
      (inferInstance : Module Rᵐᵒᵖ M) inferInstance inferInstance
      (@int_isScalarTower R _ M _ givenIntegerModule (inferInstance : Module R M))
      (@int_isScalarTower Rᵐᵒᵖ _ M _ givenIntegerModule (inferInstance : Module Rᵐᵒᵖ M))
      inferInstance
    rightModule R (ModuleCat.of (R ⊗[ℤ] Rᵐᵒᵖ) M) =
      (inferInstance : Module Rᵐᵒᵖ M) := by
  let : IsScalarTower ℤ R M := AddCommGroup.intIsScalarTower
  let : IsScalarTower ℤ Rᵐᵒᵖ M := AddCommGroup.intIsScalarTower
  let : Module (R ⊗[ℤ] Rᵐᵒᵖ) M := @TensorProduct.Algebra.module ℤ R Rᵐᵒᵖ M
      inferInstance (inferInstance : AddCommMonoid M) givenIntegerModule
      inferInstance inferInstance (inferInstance : Module R M)
      (inferInstance : Module Rᵐᵒᵖ M) inferInstance inferInstance
      (@int_isScalarTower R _ M _ givenIntegerModule (inferInstance : Module R M))
      (@int_isScalarTower Rᵐᵒᵖ _ M _ givenIntegerModule (inferInstance : Module Rᵐᵒᵖ M))
      inferInstance
  apply Module.ext'
  intro r m
  change (1 : R) • (r • m) = r • m
  exact one_smul R (r • m)

end GivenActions

end ModuleCat.Bimodule
