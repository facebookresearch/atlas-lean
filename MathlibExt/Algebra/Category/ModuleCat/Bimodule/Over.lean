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
# Ground and endpoint actions of relative enveloping modules

Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and X a module over
E_R^k=R⊗_kRᵒᵖ with carrier universe v. Restriction along the ground algebra map and the two
tensor inclusions gives its k-, left R-, and right R-actions.

Both endpoint actions restrict to the same ground k-action and commute with each other. Their
combined pure-tensor action equals the E_R^k-action, and recombination recovers the same module
structure. The reconstruction isomorphism is the identity on the coefficient carrier and
transports every morphism with its values unchanged.

Conversely, a k-module with commuting left and right R-actions compatible with that k-action
defines an E_R^k-module. Ground and endpoint restriction recover all three chosen actions.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe u r v

namespace ModuleCat.Bimodule.Over

variable (k : Type u) [CommRing k] (R : Type r) [Ring R] [Algebra k R]

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. The k-module structure is
restriction along the algebra map k→E_R^k. Thus c∈k acts on x through the enveloping scalar
algebraMap(c), preserving the same additive carrier. -/
def groundModule (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) : Module k X :=
  Module.compHom X (algebraMap k (R ⊗[k] Rᵐᵒᵖ))

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. Restriction along a↦a⊗1:R→E_R^k
gives the left R-module structure on X. Its scalar function is a•x=(a⊗1)•_X x. -/
def leftModule (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) : Module R X :=
  Module.compHom X
    (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] Rᵐᵒᵖ)

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. Restriction along
b↦1⊗b:Rᵒᵖ→E_R^k gives the Rᵒᵖ-module structure. For b=op(a), this is the right R-action
x•a=(1⊗op(a))•_X x. -/
def rightModule (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) : Module Rᵐᵒᵖ X :=
  Module.compHom X
    (Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k] R ⊗[k] Rᵐᵒᵖ).toRingHom

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. The ground and left
restrictions form a compatible scalar tower k→R→X. For c∈k and x∈X, algebraMap_k^R(c)•_left
x=c•_ground x, so (c•a)•x=c•(a•x) for a∈R. -/
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

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. The ground and Rᵒᵖ restrictions
form a compatible scalar tower k→Rᵒᵖ→X. The action of algebraMap_k^{Rᵒᵖ}(c) equals c•_ground x
for each c∈k,x∈X. -/
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

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. For a∈R,b∈Rᵒᵖ,x∈X, the
restricted scalar functions satisfy a•_left(b•_right x)=b•_right(a•_left x). Their two
tensor-inclusion scalars commute in E_R^k. -/
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

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. For a∈R,b∈Rᵒᵖ,x∈X,
a•_left(b•_right x)=(a⊗_k b)•_X x. The tensor scalar uses the relative enveloping ring and the
endpoint restrictions of the same module. -/
theorem smul_tmul (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ))
    (a : R) (b : Rᵐᵒᵖ) (x : X) :
    (leftModule k R X).smul a ((rightModule k R X).smul b x) =
      X.isModule.smul (a ⊗ₜ[k] b) x := by
  change (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[k] b) • x) = (a ⊗ₜ[k] b) • x
  rw [← mul_smul]
  apply congrArg (fun z : R ⊗[k] Rᵐᵒᵖ => z • x)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. Combine the ground k-action and
the commuting endpoint R-actions to obtain an E_R^k-module on the same carrier. Its pure action
is (a⊗b)•x=a•_left(b•_right x), with both scalar towers compatible with k. -/
def reconstructedModule (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    Module (R ⊗[k] Rᵐᵒᵖ) X := by
  letI := groundModule k R X
  letI := leftModule k R X
  letI := rightModule k R X
  letI := leftTower k R X
  letI := rightTower k R X
  letI := commute k R X
  exact TensorProduct.Algebra.module

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. For z∈E_R^k and x∈X, the scalar
function reconstructed from the ground and endpoint restrictions satisfies z•_{rec}x=z•_X x.
This holds for every tensor scalar, extending the pure-tensor formula by additivity. -/
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

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. The E_R^k-module structure
reconstructed from its ground and endpoint restrictions equals the module structure of X. The
additive group and scalar function are the same. -/
theorem reconstructedModule_eq (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    reconstructedModule k R X = X.isModule :=
  Module.ext' _ _ (reconstructedModule_smul k R X)

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. The reconstructed object
X_rec∈ModuleCat_v(E_R^k) uses the carrier of X with the recombined enveloping action. Its ground
and two endpoint scalar actions are the restrictions of X. -/
def reconstructedObject (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ) :=
  letI := reconstructedModule k R X
  ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) X

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. There is an E_R^k-module
isomorphism e_X:X_rec≅X whose forward and inverse maps are x↦x. Equality of the reconstructed
and given scalar actions makes these identity coefficient maps linear. -/
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

/-- Let k be a commutative ring in universe u, R a k-algebra ring in universe r, and E_R^k=R⊗_kRᵒᵖ.
Let X be an E_R^k-module with carrier in independent universe v. For an E_R^k-linear morphism
f:X→Y, its reconstruction map X_rec→Y_rec is e_X.hom≫f≫e_Y.inv. It has value f(x) on each
coefficient x and preserves the ground and endpoint actions. -/
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

/-- Let k be a commutative ring in u, R a k-algebra ring in r, and M an abelian group in v with a
chosen k-action and commuting R- and Rᵒᵖ-actions. Assume both endpoint actions restrict along
their algebra maps to the chosen k-action. After combining the actions into a module over
R⊗_kRᵒᵖ, restriction along k→R⊗_kRᵒᵖ is equal to the chosen k-module structure on M. -/
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

/-- Let k be a commutative ring in u, R a k-algebra ring in r, and M an abelian group in v with a
chosen k-action and commuting R- and Rᵒᵖ-actions. Assume both endpoint actions restrict along
their algebra maps to the chosen k-action. The combined relative enveloping module restricts
along a↦a⊗1 to exactly the given R-module structure on M. The unit in the second factor leaves
each coefficient unchanged. -/
theorem leftModule_ofTensor :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    leftModule k R (ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) M) = (inferInstance : Module R M) := by
  let : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  apply Module.ext'
  intro r m
  change r • ((1 : Rᵐᵒᵖ) • m) = r • m
  exact congrArg (fun x : M => r • x) (one_smul Rᵐᵒᵖ m)

/-- Let k be a commutative ring in u, R a k-algebra ring in r, and M an abelian group in v with a
chosen k-action and commuting R- and Rᵒᵖ-actions. Assume both endpoint actions restrict along
their algebra maps to the chosen k-action. Restriction of the combined R⊗_kRᵒᵖ-module along
b↦1⊗b gives the chosen Rᵒᵖ-module structure on M. The unit in the first factor leaves every
right action value unchanged. -/
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
