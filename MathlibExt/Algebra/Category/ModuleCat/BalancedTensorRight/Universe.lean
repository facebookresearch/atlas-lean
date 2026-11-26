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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.Derived
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.LiftCoordinates
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.CoefficientIsomorphisms
public import MathlibExt.Algebra.Category.ModuleCat.UliftCoherence
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Balanced tensor with independently sized source and coefficient modules

Let R,S be arbitrary rings and B an (R,S)-bimodule: R acts on the left,
S on the right, and these actions commute. For a right R-module X,
the balanced product X⊗_R B is formed as an abelian-group tensor
quotient with relation (x·r)⊗b=x⊗(r·b). It is a right S-module by
(x⊗b)·s=x⊗(b·s).

The ring, source and coefficient worlds r,s,a,b are independent.
The unlifted quotient has carrier world max(a,b). For an additional
height z, put Γ=max(r,a,b,z). Lifting both input carriers gives the
tensor functor from source world a to right S-modules in world Γ.
The ring S need not fit in Γ.

Down/up on both factors give an S-linear carrier equivalence.
After lifting the entire unlifted quotient to Γ, they give a natural
categorical isomorphism. Increasing Γ to Γ′=max(r,a,b,z,t) is
compatible with tensoring and with flattening the two coefficient
lifts; all comparisons retain the ordered pure balanced classes.
-/

@[expose] public section
noncomputable section

open CategoryTheory MulOpposite

universe zGlobal rGlobal sGlobal aGlobal bGlobal

namespace ModuleCat.BalancedTensorRight

variable (R : Type rGlobal) (S : Type sGlobal) [Ring R] [Ring S]
  (B : Type bGlobal) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

/-- For rings R,S and an (R,S)-bimodule B, put
Γ=max(r,a,b,z). The common-height tensor functor sends
X∈ModuleCat^Γ(Rᵒᵖ) to X⊗_R ULift^Γ B in ModuleCat^Γ(Sᵒᵖ).
The output right S-action is carried by the coefficient B,
independently of the ring world s. -/
def largeTensorFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    ModuleCat.{max r a b z} Rᵐᵒᵖ ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ :=
  tensorFunctor R S (ULift.{max r a b z} B)

/-- For rings R,S and an (R,S)-bimodule B, the height-Γ
tensor functor sends a right R-module X in world a to
ULift^Γ X⊗_R ULift^Γ B, Γ=max(r,a,b,z).
Its target is ModuleCat^Γ(Sᵒᵖ), and source lifting imposes no
projective-resolution hypothesis in world a. -/
def tensorFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    ModuleCat.{a} Rᵐᵒᵖ ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ :=
  ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ ⋙
    largeTensorFunctorAt.{z, r, s, a, b} R S B

/-- For rings R,S, an (R,S)-bimodule B and a right R-module
X in world a, the chosen-height object is
ULift^Γ X⊗_R ULift^Γ B, with Γ=max(r,a,b,z).
It is a right S-module in carrier world Γ. -/
abbrev tensorObjAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) :
    ModuleCat.{max r a b z} Sᵐᵒᵖ :=
  (tensorFunctorAt.{z, r, s, a, b} R S B).obj X

/-- For rings R,S, an (R,S)-bimodule B in world b and a
right R-module X in world a, the unlifted tensor object is
X⊗_R B with right S-action on B.
Its carrier has world max(a,b), independently of the ring worlds. -/
def originalTensorObj (X : ModuleCat.{aGlobal} Rᵐᵒᵖ) : ModuleCat.{max aGlobal bGlobal} Sᵐᵒᵖ :=
  letI := TensorProduct.Balanced.rightModule ℤ R S X B
  ModuleCat.of Sᵐᵒᵖ (TensorProduct.Balanced ℤ R X B)

/-- For a right R-module X and an (R,S)-bimodule B,
the pure representative [x⊗b] lies in the unlifted right
S-module X⊗_R B. It is the class in the abelian-group quotient
imposing the R-balancing relation. -/
def originalTensorMk (X : ModuleCat.{aGlobal} Rᵐᵒᵖ) (x : X) (y : B) :
    originalTensorObj R S B X :=
  TensorProduct.Balanced.mk ℤ R X B x y

/-- For a right R-module X, an (R,S)-bimodule B, r∈R,
x∈X and b∈B, the pure classes satisfy
[(x·r)⊗b]=[x⊗(r·b)] in X⊗_R B.
The multiplication order is the right action on X followed
by the left action on B. -/
theorem originalTensorMk_balance (X : ModuleCat.{aGlobal} Rᵐᵒᵖ)
    (rGlobal : R) (x : X) (y : B) :
    originalTensorMk R S B X (op rGlobal • x) y =
      originalTensorMk R S B X x (rGlobal • y) :=
  TensorProduct.Balanced.balance ℤ R X B rGlobal x y

/-- For a right R-module X and an (R,S)-bimodule B,
t∈Sᵒᵖ acts on the balanced class by
t•[x⊗b]=[x⊗(t•b)].
The commuting coefficient actions make this action compatible
with the R-balancing relation. -/
theorem originalTensorMk_smul (X : ModuleCat.{aGlobal} Rᵐᵒᵖ)
    (t : Sᵐᵒᵖ) (x : X) (y : B) :
    t • originalTensorMk R S B X x y =
      originalTensorMk R S B X x (t • y) := by
  exact TensorProduct.Balanced.rightModule_smul_mk ℤ R S X B t x y

/-- For rings R,S, an (R,S)-bimodule B and a right
R-linear map f:X→Y between source modules in world a,
the unlifted tensor map X⊗_R B→Y⊗_R B applies f to the first
factor. It is right S-linear. -/
def originalTensorMap {X Y : ModuleCat.{aGlobal} Rᵐᵒᵖ} (f : X ⟶ Y) :
    originalTensorObj R S B X ⟶ originalTensorObj R S B Y := by
  letI := TensorProduct.Balanced.rightModule ℤ R S X B
  letI := TensorProduct.Balanced.rightModule ℤ R S Y B
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.CoefficientHom.tensorMap
      (R := R) (S := S) (B := B) (A := X) (A' := Y) f.hom)

/-- For a right R-linear map f:X→Y and an (R,S)-bimodule B,
the induced map on unlifted balanced products satisfies
(f⊗id)([x⊗b])=[f(x)⊗b].
The coefficient and its outer right S-action are fixed. -/
theorem originalTensorMap_mk {X Y : ModuleCat.{aGlobal} Rᵐᵒᵖ}
    (f : X ⟶ Y) (x : X) (y : B) :
    (originalTensorMap R S B f).hom (originalTensorMk R S B X x y) =
      originalTensorMk R S B Y (f.hom x) y := by
  exact TensorProduct.Balanced.CoefficientHom.tensorMap_mk
    (R := R) (S := S) (B := B) (A := X) (A' := Y) f.hom x y

/-- For rings R,S and an (R,S)-bimodule B in world b,
X↦X⊗_R B defines a functor
ModuleCat^a(Rᵒᵖ)→ModuleCat^max(a,b)(Sᵒᵖ).
Its morphisms apply the input right R-linear map to the first factor. -/
def originalTensorFunctor :
    ModuleCat.{aGlobal} Rᵐᵒᵖ ⥤ ModuleCat.{max aGlobal bGlobal} Sᵐᵒᵖ where
  obj := originalTensorObj R S B
  map := originalTensorMap R S B
  map_id X := by
    let := TensorProduct.Balanced.rightModule ℤ R S X B
    apply ModuleCat.hom_ext
    change TensorProduct.Balanced.CoefficientHom.tensorMap
        (R := R) (S := S) (B := B) (A := X) (A' := X)
          (𝟙 X : ModuleCat.Hom X X).hom =
      LinearMap.id
    rw [ModuleCat.hom_id]
    exact TensorProduct.Balanced.CoefficientHom.tensorMap_id
      (R := R) (S := S) (B := B) (A := X)
  map_comp {X Y Z} f g := by
    let := TensorProduct.Balanced.rightModule ℤ R S X B
    let := TensorProduct.Balanced.rightModule ℤ R S Y B
    let := TensorProduct.Balanced.rightModule ℤ R S Z B
    apply ModuleCat.hom_ext
    change TensorProduct.Balanced.CoefficientHom.tensorMap
        (R := R) (S := S) (B := B) (A := X) (A' := Z) (f ≫ g).hom =
      (TensorProduct.Balanced.CoefficientHom.tensorMap
        (R := R) (S := S) (B := B) (A := Y) (A' := Z) g.hom).comp
        (TensorProduct.Balanced.CoefficientHom.tensorMap
          (R := R) (S := S) (B := B) (A := X) (A' := Y) f.hom)
    rw [ModuleCat.hom_comp]
    exact TensorProduct.Balanced.CoefficientHom.tensorMap_comp
      (R := R) (S := S) (B := B) (A := X) (A' := Y) (A'' := Z) f.hom g.hom

/-- For rings R,S and an (R,S)-bimodule B, the unlifted
functor X↦X⊗_R B preserves sums of right R-linear maps.
On a pure class, (f+g)⊗id has value [f(x)⊗b]+[g(x)⊗b]. -/
theorem originalTensorFunctor_additive : (originalTensorFunctor R S B).Additive := by
  refine ⟨?_⟩
  intro X Y f g
  let := TensorProduct.Balanced.rightModule ℤ R S X B
  let := TensorProduct.Balanced.rightModule ℤ R S Y B
  apply ModuleCat.hom_ext
  change TensorProduct.Balanced.CoefficientHom.tensorMap
      (R := R) (S := S) (B := B) (A := X) (A' := Y) (f + g).hom =
    TensorProduct.Balanced.CoefficientHom.tensorMap
      (R := R) (S := S) (B := B) (A := X) (A' := Y) f.hom +
    TensorProduct.Balanced.CoefficientHom.tensorMap
      (R := R) (S := S) (B := B) (A := X) (A' := Y) g.hom
  rw [ModuleCat.hom_add]
  exact TensorProduct.Balanced.CoefficientHom.tensorMap_add
    (R := R) (S := S) (B := B) (A := X) (A' := Y) f.hom g.hom

/-- For rings R,S and an (R,S)-bimodule B, the functor
ModuleCat^a(Rᵒᵖ)→ModuleCat^max(a,b)(Sᵒᵖ),
X↦X⊗_R B, has its additive functor structure from the
additivity of balanced tensor maps in the source morphism. -/
def originalTensorAdditiveFunctor :
    ModuleCat.{aGlobal} Rᵐᵒᵖ ⥤+ ModuleCat.{max aGlobal bGlobal} Sᵐᵒᵖ := by
  letI := originalTensorFunctor_additive R S B
  exact AdditiveFunctor.of (originalTensorFunctor R S B)

/-- For rings R,S, an (R,S)-bimodule B and f:X→Y,
the height-Γ tensor morphism is
ULift^Γ X⊗_R ULift^Γ B→ULift^Γ Y⊗_R ULift^Γ B,
using the lifted input map on the first factor.
Here Γ=max(r,a,b,z), with the ring and carrier worlds independent. -/
def tensorMapAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] {X Y : ModuleCat.{a} Rᵐᵒᵖ} (f : X ⟶ Y) :
    tensorObjAt.{z, r, s, a, b} R S B X ⟶ tensorObjAt.{z, r, s, a, b} R S B Y :=
  (tensorFunctorAt.{z, r, s, a, b} R S B).map f

/-- For a right R-linear map f:X→Y and an (R,S)-bimodule B,
the height-Γ tensor map sends
[up(x)⊗up(b)] to [up(f(x))⊗up(b)].
Both carriers are lifted to Γ=max(r,a,b,z), while the
outer S-action stays on B. -/
theorem tensorMapAt_mk.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] {X Y : ModuleCat.{a} Rᵐᵒᵖ}
    (f : X ⟶ Y) (x : X) (y : B) :
    (tensorMapAt.{z, r, s, a, b} R S B f).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) (ULift.up x) (ULift.up y)) =
      TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} Y)
        (ULift.{max r a b z} B) (ULift.up (f.hom x)) (ULift.up y) := by
  change (tensorMap R S (ULift.{max r a b z} B)
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).map f)).hom _ = _
  have h := tensorMap_mk R S (ULift.{max r a b z} B)
    (A := (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)
    (A' := (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj Y)
    ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).map f)
    (ULift.up x) (ULift.up y)
  exact h

/-- For a right R-module X and an (R,S)-bimodule B,
down on both factors gives the Sᵒᵖ-linear map
ULift^Γ X⊗_R ULift^Γ B→X⊗_R B.
It sends each lifted pure class to the class of its two
underlying factors. -/
def tensorUnliftAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) :
    (tensorObjAt.{z, r, s, a, b} R S B X).carrier →ₗ[Sᵐᵒᵖ]
      (originalTensorObj R S B X).carrier := by
  letI := TensorProduct.Balanced.rightModule ℤ R S (ULift.{max r a b z} X)
    (ULift.{max r a b z} B)
  letI := TensorProduct.Balanced.rightModule ℤ R S X B
  let e : TensorProduct.Balanced ℤ R (ULift.{max r a b z} X)
      (ULift.{max r a b z} B) ≃ₗ[Sᵐᵒᵖ] TensorProduct.Balanced ℤ R X B :=
    TensorProduct.Balanced.uliftRightCarrierEquiv ℤ R S X B
  exact e.toLinearMap

/-- For a right R-module X and an (R,S)-bimodule B,
up on both factors gives the Sᵒᵖ-linear map
X⊗_R B→ULift^Γ X⊗_R ULift^Γ B.
It is inverse to down on both tensor factors. -/
def tensorLiftAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) :
    (originalTensorObj R S B X).carrier →ₗ[Sᵐᵒᵖ]
      (tensorObjAt.{z, r, s, a, b} R S B X).carrier := by
  letI := TensorProduct.Balanced.rightModule ℤ R S X B
  letI := TensorProduct.Balanced.rightModule ℤ R S (ULift.{max r a b z} X)
    (ULift.{max r a b z} B)
  let e : TensorProduct.Balanced ℤ R (ULift.{max r a b z} X)
      (ULift.{max r a b z} B) ≃ₗ[Sᵐᵒᵖ] TensorProduct.Balanced ℤ R X B :=
    TensorProduct.Balanced.uliftRightCarrierEquiv ℤ R S X B
  exact e.symm.toLinearMap

/-- For x∈ULift^Γ X and b∈ULift^Γ B, the down map satisfies
d([x⊗b])=[x.down⊗b.down] in X⊗_R B.
The source is a right R-module and B is an (R,S)-bimodule,
so this formula preserves balancing and the right S-action. -/
theorem tensorUnliftAt_mk.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ)
    (x : ULift.{max r a b z} X) (y : ULift.{max r a b z} B) :
    tensorUnliftAt.{z, r, s, a, b} R S B X
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) x y) =
      TensorProduct.Balanced.mk ℤ R X B x.down y.down := by
  exact TensorProduct.Balanced.uliftRightCarrierEquiv_mk ℤ R S X B x y

/-- For a right R-module X and an (R,S)-bimodule B,
the inverse carrier lift satisfies
u([x⊗b])=[up(x)⊗up(b)].
The target has both carriers at Γ=max(r,a,b,z). -/
theorem tensorLiftAt_mk.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) (x : X) (y : B) :
    tensorLiftAt.{z, r, s, a, b} R S B X (TensorProduct.Balanced.mk ℤ R X B x y) =
      TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B) (ULift.up x) (ULift.up y) := by
  exact TensorProduct.Balanced.uliftRightCarrierEquiv_symm_mk ℤ R S X B x y

/-- For a right R-module X and an (R,S)-bimodule B,
down/up on both factors give
ULift^Γ X⊗_R ULift^Γ B≃ₗ[Sᵒᵖ]X⊗_R B
as carrier modules, with Γ=max(r,a,b,z) and the unlifted
carrier in world max(a,b). -/
def tensorCarrierEquivAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) :
    (tensorObjAt.{z, r, s, a, b} R S B X).carrier ≃ₗ[Sᵐᵒᵖ]
      (originalTensorObj R S B X).carrier := by
  letI := TensorProduct.Balanced.rightModule ℤ R S (ULift.{max r a b z} X)
    (ULift.{max r a b z} B)
  letI := TensorProduct.Balanced.rightModule ℤ R S X B
  exact TensorProduct.Balanced.uliftRightCarrierEquiv ℤ R S X B

/-- For a right R-module X and an (R,S)-bimodule B,
there is an isomorphism in ModuleCat^Γ(Sᵒᵖ)
ULift^Γ X⊗_R ULift^Γ B ≅ ULift^Γ(X⊗_R B).
It is the carrier down equivalence followed by lifting the
entire unlifted balanced quotient. -/
def tensorOutputLiftIsoAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) :
    tensorObjAt.{z, r, s, a, b} R S B X ≅
      (ModuleCat.uliftFunctor.{max r a b z, max a b} Sᵐᵒᵖ).obj
        (originalTensorObj R S B X) := by
  letI := TensorProduct.Balanced.rightModule ℤ R S (ULift.{max r a b z} X)
    (ULift.{max r a b z} B)
  letI := TensorProduct.Balanced.rightModule ℤ R S X B
  let e : TensorProduct.Balanced ℤ R (ULift.{max r a b z} X)
      (ULift.{max r a b z} B) ≃ₗ[Sᵐᵒᵖ]
        ULift.{max r a b z} (TensorProduct.Balanced ℤ R X B) :=
    TensorProduct.Balanced.uliftRightEquiv ℤ R S X B
  exact e.toModuleIso

/-- For a right R-module X and an (R,S)-bimodule B,
the forward output comparison sends [x⊗b], with both factors
lifted to Γ, to up([x.down⊗b.down]).
The target is the lift of the entire unlifted tensor object. -/
theorem tensorOutputLiftIsoAt_hom_mk.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (X : ModuleCat.{a} Rᵐᵒᵖ) (x : ULift.{max r a b z} X)
    (y : ULift.{max r a b z} B) :
    (tensorOutputLiftIsoAt.{z, r, s, a, b} R S B X).hom.hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) x y) =
      ULift.up (originalTensorMk R S B X x.down y.down) := by
  exact TensorProduct.Balanced.uliftRightEquiv_mk ℤ R S X B x y

/-- For a right R-module X and an (R,S)-bimodule B,
the inverse whole-output comparison sends
up([x⊗b]) to [up(x)⊗up(b)].
It identifies two lifts of the same balanced tensor class. -/
theorem tensorOutputLiftIsoAt_inv_mk.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (X : ModuleCat.{a} Rᵐᵒᵖ) (x : X) (y : B) :
    (tensorOutputLiftIsoAt.{z, r, s, a, b} R S B X).inv.hom
        (ULift.up (originalTensorMk R S B X x y)) =
      TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B) (ULift.up x) (ULift.up y) := by
  exact TensorProduct.Balanced.uliftRightEquiv_symm_mk ℤ R S X B x y

/-- For rings R,S, an (R,S)-bimodule B and a right
R-linear map f:X→Y, let e_X,e_Y compare lifted-factor tensors
with the lifts of their unlifted quotients.
They satisfy e_Y∘T_Γ(f)=ULift(f⊗id_B)∘e_X. -/
theorem tensorOutputLiftIsoAt_naturality.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    {X Y : ModuleCat.{a} Rᵐᵒᵖ} (f : X ⟶ Y) :
    tensorMapAt.{z, r, s, a, b} R S B f ≫
        (tensorOutputLiftIsoAt.{z, r, s, a, b} R S B Y).hom =
      (tensorOutputLiftIsoAt.{z, r, s, a, b} R S B X).hom ≫
        (ModuleCat.uliftFunctor.{max r a b z, max a b} Sᵐᵒᵖ).map
          (originalTensorMap R S B f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R
    (ULift.{max r a b z} X) (ULift.{max r a b z} B)
  intro x y
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  change (tensorOutputLiftIsoAt R S B Y).hom.hom
      ((tensorMapAt R S B f).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) (ULift.up x) (ULift.up y))) =
    ((ModuleCat.uliftFunctor.{max r a b z, max a b} Sᵐᵒᵖ).map
      (originalTensorMap R S B f)).hom
        ((tensorOutputLiftIsoAt R S B X).hom.hom
          (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
            (ULift.{max r a b z} B) (ULift.up x) (ULift.up y)))
  rw [tensorMapAt_mk, tensorOutputLiftIsoAt_hom_mk,
    tensorOutputLiftIsoAt_hom_mk]
  change ULift.up (originalTensorMk R S B Y (f.hom x) y) =
    ULift.up ((originalTensorMap R S B f).hom (originalTensorMk R S B X x y))
  rw [originalTensorMap_mk]

/-- For rings R,S and an (R,S)-bimodule B, the
height-Γ tensor functor is naturally isomorphic to the
unlifted functor X↦X⊗_R B followed by whole-output lifting.
The component sends [up(x)⊗up(b)] to up([x⊗b]). -/
def tensorOutputLiftNatIsoAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorFunctorAt.{z, r, s, a, b} R S B ≅
      originalTensorFunctor R S B ⋙
        ModuleCat.uliftFunctor.{max r a b z, max a b} Sᵐᵒᵖ :=
  NatIso.ofComponents (tensorOutputLiftIsoAt R S B)
    (fun {X Y} f => tensorOutputLiftIsoAt_naturality R S B f)

/-- For rings R,S and an (R,S)-bimodule C whose source and
coefficient carriers both have world v, the chosen-height
tensor functor is naturally the original common-world tensor
functor followed by lifting its output to max(r,v,z).
This comparison is underived and uses no source projectivity hypothesis. -/
def tensorOriginalLiftIsoAt.{z, r, s, v}
    (R : Type r) (S : Type s) [Ring R] [Ring S]
    (C : Type v) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
    [SMulCommClass R Sᵐᵒᵖ C] :
    tensorFunctorAt.{z, r, s, v, v} R S C ≅
      tensorFunctor R S C ⋙ ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ :=
  tensorOutputLiftNatIsoAt.{z, r, s, v, v} R S C

section Heights


/-- For a left R-module B and Γ=max(r,a,b,z),
Γ′=max(r,a,b,z,t), there is an R-linear equivalence
ULift^Γ′(ULift^Γ B)≃ULift^Γ′B.
It sends up(up(b)) to up(b), with the reverse map inserting
the inner lift. -/
def coefficientFlattenEquivAt.{t, z, r, a, b} (R : Type r) [Ring R]
    (B : Type b) [AddCommGroup B] [Module R B] :
    ULift.{max r a b z t} (ULift.{max r a b z} B) ≃ₗ[R]
      ULift.{max r a b z t} B :=
  ModuleCat.uliftFlattenEquiv.{max r a b z, max r a b z t} R B

/-- For a coefficient B with left R- and right S-actions,
the flattening map ULift^Γ′(ULift^Γ B)→ULift^Γ′B
intertwines the Sᵒᵖ-action.
Its value on s•up(up(b)) is up(s•b). -/
theorem coefficientFlattenEquivAt_outer.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    (s : Sᵐᵒᵖ) (x : ULift.{max r a b z t} (ULift.{max r a b z} B)) :
    coefficientFlattenEquivAt.{t, z, r, a, b} R B (s • x) =
      s • coefficientFlattenEquivAt.{t, z, r, a, b} R B x := rfl

/-- For rings R,S and an (R,S)-bimodule B, tensoring
with ULift^Γ′(ULift^Γ B) is naturally isomorphic to tensoring
with ULift^Γ′B on right R-modules in world Γ′.
The comparison acts by flattening the coefficient factor. -/
def tensorCoefficientFlattenIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorFunctor R S (ULift.{max r a b z t} (ULift.{max r a b z} B)) ≅
      largeTensorFunctorAt.{max z t, r, s, a, b} R S B :=
  tensorCoefficientIso R S
    (ULift.{max r a b z t} (ULift.{max r a b z} B))
    (ULift.{max r a b z t} B)
    (coefficientFlattenEquivAt.{t, z, r, a, b} R B)
    (coefficientFlattenEquivAt_outer.{t, z, r, s, a, b} R S B)

/-- For rings R,S and an (R,S)-bimodule B, put
Γ=max(r,a,b,z), Γ′=max(r,a,b,z,t).
Tensoring at Γ′ after lifting the input is naturally isomorphic
to tensoring at Γ and lifting the whole output to Γ′.
The common source is ModuleCat^Γ(Rᵒᵖ). -/
def tensorHeightIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ ⋙
        largeTensorFunctorAt.{max z t, r, s, a, b} R S B ≅
      largeTensorFunctorAt.{z, r, s, a, b} R S B ⋙
        ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ :=
  Functor.isoWhiskerLeft
      (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
      (tensorCoefficientFlattenIsoAt.{t, z, r, s, a, b} R S B).symm ≪≫
    tensorOutputLiftNatIsoAt.{max r a b z t, r, s, max r a b z, max r a b z}
      R S (ULift.{max r a b z} B)

/-- For a right R-module X in world Γ and an (R,S)-bimodule B,
the height comparison Γ→Γ′ sends
[up_(Γ′)(x)⊗up_(Γ′)(b)] to
up_(Γ′)([x⊗up_Γ(b)]).
This is its forward map to the lifted lower-height tensor output. -/
theorem tensorHeightIsoAt_hom_mk.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (X : ModuleCat.{max r a b z} Rᵐᵒᵖ) (x : X) (y : B) :
    ((tensorHeightIsoAt.{t, z, r, s, a, b} R S B).hom.app X).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
          (ULift.{max r a b z t} B) (ULift.up x) (ULift.up y)) =
      ULift.up (TensorProduct.Balanced.mk ℤ R X
        (ULift.{max r a b z} B) x (ULift.up y)) := by
  change (tensorOutputLiftIsoAt.{max r a b z t, r, s, max r a b z, max r a b z} R S (ULift.{max r a b z} B) X).hom.hom
      ((tensorCoefficientMap R S (ULift.{max r a b z t} B)
          (ULift.{max r a b z t} (ULift.{max r a b z} B))
          (coefficientFlattenEquivAt.{t, z, r, a, b} R B).symm.toLinearMap
          (coefficientEquiv_symm_outer (coefficientFlattenEquivAt.{t, z, r, a, b} R B).toEquiv
            (coefficientFlattenEquivAt_outer.{t, z, r, s, a, b} R S B))
          ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ).obj X)).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
          (ULift.{max r a b z t} B) (ULift.up x) (ULift.up y))) = _
  have hCoeff := tensorCoefficientMap_mk R S
    (ULift.{max r a b z t} B)
    (ULift.{max r a b z t} (ULift.{max r a b z} B))
    (coefficientFlattenEquivAt.{t, z, r, a, b} R B).symm.toLinearMap
    (coefficientEquiv_symm_outer
      (coefficientFlattenEquivAt.{t, z, r, a, b} R B).toEquiv
      (coefficientFlattenEquivAt_outer.{t, z, r, s, a, b} R S B))
    ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ).obj X)
    (ULift.up x) (ULift.up y)
  have hCoeff' : (tensorCoefficientMap R S (ULift.{max r a b z t} B)
      (ULift.{max r a b z t} (ULift.{max r a b z} B))
      (coefficientFlattenEquivAt.{t, z, r, a, b} R B).symm.toLinearMap
      (coefficientEquiv_symm_outer
        (coefficientFlattenEquivAt.{t, z, r, a, b} R B).toEquiv
        (coefficientFlattenEquivAt_outer.{t, z, r, s, a, b} R S B))
      ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ).obj X)).hom
      (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
        (ULift.{max r a b z t} B) (ULift.up x) (ULift.up y)) =
    TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
      (ULift.{max r a b z t} (ULift.{max r a b z} B)) (ULift.up x)
      ((coefficientFlattenEquivAt.{t, z, r, a, b} R B).symm (ULift.up y)) := hCoeff
  have hOut := tensorOutputLiftIsoAt_hom_mk.{max r a b z t, r, s, max r a b z, max r a b z}
    R S (ULift.{max r a b z} B) X (ULift.up x)
    ((coefficientFlattenEquivAt.{t, z, r, a, b} R B).symm (ULift.up y))
  exact (congrArg
    (tensorOutputLiftIsoAt.{max r a b z t, r, s, max r a b z, max r a b z}
      R S (ULift.{max r a b z} B) X).hom.hom hCoeff').trans hOut

/-- For a right R-module X in world Γ and an (R,S)-bimodule B,
the inverse height comparison sends
up_(Γ′)([x⊗up_Γ(b)]) to
[up_(Γ′)(x)⊗up_(Γ′)(b)].
The balanced class and its factor order are unchanged. -/
theorem tensorHeightIsoAt_inv_mk.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (X : ModuleCat.{max r a b z} Rᵐᵒᵖ) (x : X) (y : B) :
    ((tensorHeightIsoAt.{t, z, r, s, a, b} R S B).inv.app X).hom
        (ULift.up (TensorProduct.Balanced.mk ℤ R X
          (ULift.{max r a b z} B) x (ULift.up y))) =
      TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
        (ULift.{max r a b z t} B) (ULift.up x) (ULift.up y) := by
  apply ((tensorHeightIsoAt.{t, z, r, s, a, b} R S B).app X).toLinearEquiv.injective
  change ((tensorHeightIsoAt.{t, z, r, s, a, b} R S B).hom.app X).hom
      (((tensorHeightIsoAt.{t, z, r, s, a, b} R S B).inv.app X).hom
        (ULift.up (TensorProduct.Balanced.mk ℤ R X
          (ULift.{max r a b z} B) x (ULift.up y)))) = _
  let Y := ((largeTensorFunctorAt.{z, r, s, a, b} R S B) ⋙
    ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ).obj X
  have h := congrArg (fun f : ModuleCat.Hom Y Y => f.hom
      (ULift.up (TensorProduct.Balanced.mk ℤ R X
        (ULift.{max r a b z} B) x (ULift.up y))))
    ((tensorHeightIsoAt.{t, z, r, s, a, b} R S B).app X).inv_hom_id
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at h
  exact h.trans (tensorHeightIsoAt_hom_mk.{t, z, r, s, a, b} R S B X x y).symm

end Heights

end ModuleCat.BalancedTensorRight
