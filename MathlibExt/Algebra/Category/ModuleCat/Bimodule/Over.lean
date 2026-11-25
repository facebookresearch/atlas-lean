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
public import Mathlib.Algebra.Algebra.Tower

/-!
# Original actions of native k-enveloping modules

The three restrictions of a native k-enveloping module recover its actual
ground, left and right actions. Recombination recovers the stored module.
All comparisons below are earned from those actions, including the ground
module equality for arbitrary k. The categories remain native ModuleCat.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe u r v

namespace ModuleCat.Bimodule.Over

variable (k : Type u) [CommRing k] (R : Type r) [Ring R] [Algebra k R]

/-- Restrict the original stored action along the ground algebra map. -/
def groundModule (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) : Module k X :=
  Module.compHom X (algebraMap k (R ⊗[k] Rᵐᵒᵖ))

/-- Restrict the original action along the first tensor inclusion. -/
def leftModule (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) : Module R X :=
  Module.compHom X
    (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] Rᵐᵒᵖ)

/-- Restrict the original action along the second tensor inclusion. -/
def rightModule (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) : Module Rᵐᵒᵖ X :=
  Module.compHom X
    (Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k] R ⊗[k] Rᵐᵒᵖ).toRingHom

/-- The first restriction has the original ground action. -/
theorem leftTower (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    letI := groundModule k R X
    letI := leftModule k R X
    IsScalarTower k R X := by
  let := groundModule k R X
  let := leftModule k R X
  apply IsScalarTower.of_algebraMap_smul (R := k) (A := R) (M := X)
  intro a x
  change X.isModule.smul ((algebraMap k R a) ⊗ₜ[k] (1 : Rᵐᵒᵖ)) x =
    X.isModule.smul (algebraMap k (R ⊗[k] Rᵐᵒᵖ) a) x
  exact congrArg (fun z : R ⊗[k] Rᵐᵒᵖ => X.isModule.smul z x)
    (Algebra.TensorProduct.algebraMap_apply (R := k) (S := k)
      (A := R) (B := Rᵐᵒᵖ) a).symm

/-- The second restriction has that same ground action. -/
theorem rightTower (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    letI := groundModule k R X
    letI := rightModule k R X
    IsScalarTower k Rᵐᵒᵖ X := by
  let := groundModule k R X
  let := rightModule k R X
  apply IsScalarTower.of_algebraMap_smul (R := k) (A := Rᵐᵒᵖ) (M := X)
  intro a x
  change X.isModule.smul ((1 : R) ⊗ₜ[k] algebraMap k Rᵐᵒᵖ a) x =
    X.isModule.smul (algebraMap k (R ⊗[k] Rᵐᵒᵖ) a) x
  exact congrArg (fun z : R ⊗[k] Rᵐᵒᵖ => X.isModule.smul z x)
    (Algebra.TensorProduct.algebraMap_apply' (R := k) (A := R)
      (B := Rᵐᵒᵖ) a).symm

/-- The two restrictions of the original enveloping action commute. -/
theorem commute (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    letI := leftModule k R X
    letI := rightModule k R X
    SMulCommClass R Rᵐᵒᵖ X := by
  let := leftModule k R X
  let := rightModule k R X
  refine ⟨fun a b x => ?_⟩
  change (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[k] b) • x) =
    ((1 : R) ⊗ₜ[k] b) • ((a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • x)
  rw [← mul_smul, ← mul_smul]
  apply congrArg (fun z : R ⊗[k] Rᵐᵒᵖ => z • x)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The pure enveloping action is the original ordered two-sided action. -/
theorem smul_tmul (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ))
    (a : R) (b : Rᵐᵒᵖ) (x : X) :
    (leftModule k R X).smul a ((rightModule k R X).smul b x) =
      X.isModule.smul (a ⊗ₜ[k] b) x := by
  change (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[k] b) • x) = (a ⊗ₜ[k] b) • x
  rw [← mul_smul]
  apply congrArg (fun z : R ⊗[k] Rᵐᵒᵖ => z • x)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Recombine the original restrictions with the native module constructor. -/
def reconstructedModule (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    Module (R ⊗[k] Rᵐᵒᵖ) X := by
  letI := groundModule k R X
  letI := leftModule k R X
  letI := rightModule k R X
  letI := leftTower k R X
  letI := rightTower k R X
  letI := commute k R X
  exact TensorProduct.Algebra.module

/-- Native recombination acts by the original stored scalar function. -/
theorem reconstructedModule_smul (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ))
    (z : R ⊗[k] Rᵐᵒᵖ) (x : X) :
    (reconstructedModule k R X).smul z x = X.isModule.smul z x := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[k] b) • x) =
      (a ⊗ₜ[k] b) • x
    rw [← mul_smul]
    apply congrArg (fun z : R ⊗[k] Rᵐᵒᵖ => z • x)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add z w hz hw =>
    exact ((reconstructedModule k R X).add_smul z w x).trans
      ((congrArg₂ (· + ·) hz hw).trans (X.isModule.add_smul z w x).symm)

/-- Equality of the actual native module data follows from its scalar function. -/
theorem reconstructedModule_eq (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    reconstructedModule k R X = X.isModule :=
  Module.ext' _ _ (reconstructedModule_smul k R X)

/-- Bundle the same carrier with the reconstructed native action. -/
def reconstructedObject (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ) :=
  letI := reconstructedModule k R X
  ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) X

/-- The comparison is the actual identity function in both directions. -/
def reconstructedIso (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    reconstructedObject k R X ≅ X where
  hom := @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _
    (reconstructedObject k R X).carrier X.carrier
    (reconstructedObject k R X).isAddCommGroup (reconstructedObject k R X).isModule
    X.isAddCommGroup X.isModule
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun z x => reconstructedModule_smul k R X z x }
  inv := @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _
    X.carrier (reconstructedObject k R X).carrier
    X.isAddCommGroup X.isModule
    (reconstructedObject k R X).isAddCommGroup (reconstructedObject k R X).isModule
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun z x => (reconstructedModule_smul k R X z x).symm }
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
theorem reconstructedIso_hom_apply (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) (x : X) :
    (reconstructedIso k R X).hom.hom x = x := rfl

@[simp]
theorem reconstructedIso_inv_apply (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) (x : X) :
    (reconstructedIso k R X).inv.hom x = x := rfl

/-- Transport the original morphism using those identity-coordinate isos. -/
def reconstructedMap {X Y : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    reconstructedObject k R X ⟶ reconstructedObject k R Y :=
  (reconstructedIso k R X).hom ≫ f ≫ (reconstructedIso k R Y).inv

@[simp]
theorem reconstructedMap_apply {X Y : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) (x : X) : (reconstructedMap k R f).hom x = f.hom x := rfl

section GivenActions

variable (M : Type v) [AddCommGroup M] [dM : Module k M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]

/-- The k-action recovered from a compatible tensor module is the supplied one. -/
theorem groundModule_ofTensor :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    groundModule k R (ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) M) = dM := by
  let : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  apply Module.ext'
  intro a m
  change (algebraMap k (R ⊗[k] Rᵐᵒᵖ) a) • m = a • m
  rw [Algebra.TensorProduct.algebraMap_apply]
  change (algebraMap k R a) • ((1 : Rᵐᵒᵖ) • m) = a • m
  rw [one_smul]
  exact IsScalarTower.algebraMap_smul (R := k) (A := R) (M := M) a m

/-- The first restriction recovers the original left action. -/
theorem leftModule_ofTensor :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    leftModule k R (ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) M) = (inferInstance : Module R M) := by
  let : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  apply Module.ext'
  intro r m
  change r • ((1 : Rᵐᵒᵖ) • m) = r • m
  exact congrArg (fun x : M => r • x) (one_smul Rᵐᵒᵖ m)

/-- The second restriction recovers the original right action. -/
theorem rightModule_ofTensor :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    rightModule k R (ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) M) =
      (inferInstance : Module Rᵐᵒᵖ M) := by
  let : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  apply Module.ext'
  intro r m
  change (1 : R) • (r • m) = r • m
  exact one_smul R (r • m)

end GivenActions

end ModuleCat.Bimodule.Over
