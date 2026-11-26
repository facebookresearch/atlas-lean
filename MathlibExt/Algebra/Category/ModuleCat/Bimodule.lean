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
# Endpoint actions of enveloping-ring modules

Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ its bimodule enveloping ring. An E_R-module X with
carrier in universe v has left R-action a•x=(a⊗1)•x and right R-action x•b=(1⊗op(b))•x. These
endpoint actions commute, and their combined action on a pure tensor recovers (a⊗op(b))•x.

Recombining the restricted actions gives the same E_R-module action. The corresponding module
objects are isomorphic by identity coefficient maps, and morphisms transport through these
isomorphisms with the same values. Conversely, commuting left and right R-actions on an abelian
group induce an E_R-action whose endpoint restrictions recover those given actions. Integer
scalar compatibility follows from the canonical integer action on an abelian group.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe r v

namespace ModuleCat.Bimodule

variable (R : Type r) [Ring R]

/-- Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ. Let X be an E_R-module with carrier in an
independent universe v. The left R-module structure is restriction along a↦a⊗1:R→E_R. Thus a
acts on x by the E_R-scalar a⊗1, with the same additive carrier as X. -/
def leftModule (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) : Module R X :=
  Module.compHom X
    (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℤ] Rᵐᵒᵖ)

/-- Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ. Let X be an E_R-module with carrier in an
independent universe v. The Rᵒᵖ-module structure is restriction along b↦1⊗b:Rᵒᵖ→E_R. For
b=op(c), this is the right R-action x•c=(1⊗op(c))•x on the same carrier. -/
def rightModule (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) : Module Rᵐᵒᵖ X :=
  Module.compHom X
    (Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[ℤ] R ⊗[ℤ] Rᵐᵒᵖ).toRingHom

/-- Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ. Let X be an E_R-module with carrier in an
independent universe v. Let L_a(x)=(a⊗1)•x and R_b(x)=(1⊗b)•x for a∈R,b∈Rᵒᵖ. Then
L_a(R_b(x))=R_b(L_a(x)) for every x∈X, giving commuting scalar actions of R and Rᵒᵖ. -/
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

/-- Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ. Let X be an E_R-module with carrier in an
independent universe v. For a∈R,b∈Rᵒᵖ,x∈X, the restricted endpoint actions satisfy
L_a(R_b(x))=(a⊗b)•x. The right-hand action is the E_R-module action of X. -/
theorem smul_tmul (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ))
    (a : R) (b : Rᵐᵒᵖ) (x : X) :
    (leftModule R X).smul a ((rightModule R X).smul b x) =
      X.isModule.smul (a ⊗ₜ[ℤ] b) x := by
  change (a ⊗ₜ[ℤ] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[ℤ] b) • x) = (a ⊗ₜ[ℤ] b) • x
  rw [← mul_smul]
  apply congrArg (fun z : R ⊗[ℤ] Rᵐᵒᵖ => z • x)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ. Let X be an E_R-module with carrier in an
independent universe v. Combine the left and right restricted actions to define an E_R-module on
the same abelian group. Its pure-tensor action is (a⊗b)•x=L_a(R_b(x)); the commuting endpoint
actions make this a module action. -/
def reconstructedModule (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    Module (R ⊗[ℤ] Rᵐᵒᵖ) X := by
  letI := leftModule R X
  letI := rightModule R X
  letI := commute R X
  exact TensorProduct.Algebra.module

/-- Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ. Let X be an E_R-module with carrier in an
independent universe v. For every z∈E_R and x∈X, the action reconstructed from the endpoint
restrictions satisfies z•_{rec}x=z•_X x. The identity holds for all tensor scalars, extending
the pure-tensor formula by additivity. -/
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

/-- Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ. Let X be an E_R-module with carrier in an
independent universe v. The E_R-module structure obtained by combining the left and right
restrictions is equal to the E_R-module structure of X. Both structures use the same additive
group and the same scalar function on every z∈E_R. -/
theorem reconstructedModule_eq (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    reconstructedModule R X = X.isModule :=
  Module.ext' _ _ (reconstructedModule_smul R X)

/-- Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ. Let X be an E_R-module with carrier in an
independent universe v. Regard the carrier of X as an E_R-module by combining its endpoint
restrictions. This produces an object X_rec∈ModuleCat_v(E_R), with the same additive coefficient
group and carrier universe. -/
def reconstructedObject (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ) :=
  letI := reconstructedModule R X
  ModuleCat.of (R ⊗[ℤ] Rᵐᵒᵖ) X

/-- Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ. Let X be an E_R-module with carrier in an
independent universe v. There is an isomorphism e_X:X_rec≅X whose forward and inverse maps send
x to x. The equality of the reconstructed and given scalar actions makes both identity
coefficient maps E_R-linear. -/
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

/-- Let R be a ring in universe r and E_R=R⊗_ℤRᵒᵖ. Let X be an E_R-module with carrier in an
independent universe v. For an E_R-module morphism f:X→Y, the induced morphism X_rec→Y_rec is
e_X.hom≫f≫e_Y.inv, where e_X,e_Y are the identity-coefficient reconstruction isomorphisms. Its
value on every x is f(x). -/
def reconstructedMap {X Y : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    reconstructedObject R X ⟶ reconstructedObject R Y :=
  (reconstructedIso R X).hom ≫ f ≫ (reconstructedIso R Y).inv

@[simp]
theorem reconstructedMap_apply {X Y : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)}
    (f : X ⟶ Y) (x : X) : (reconstructedMap R f).hom x = f.hom x := rfl

/-- Let R be a ring in universe r and M an abelian group in universe v with a chosen ℤ-module
structure and an R-module structure. The integer scalar tower ℤ→R→M is compatible:
(n•r)•m=n•(r•m) for n∈ℤ,r∈R,m∈M, with the canonical integer action on R. This holds for the
supplied integer action on M. -/
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
/-- Let R be a ring in universe r and M an abelian group in universe v with an integer module
structure and commuting R- and Rᵒᵖ-module structures. Combine these actions into an
R⊗_ℤRᵒᵖ-module. Restriction along a↦a⊗1 is equal to the given R-module structure on M. -/
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
/-- Let R be a ring in universe r and M an abelian group in universe v with an integer module
structure and commuting R- and Rᵒᵖ-module structures. The combined R⊗_ℤRᵒᵖ-module restricts
along b↦1⊗b to exactly the given Rᵒᵖ-module structure. -/
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
