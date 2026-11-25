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
# Independent carrier universes for enriched balanced tensor

The source carrier aGlobal and coefficient carrier bGlobal need not contain
R. The working category has Gamma = max(rGlobal,aGlobal,bGlobal,zGlobal),
where free presentations supply projective resolutions. The outer ring S
need not be small in Gamma. Source maps are lifted by the module functor.
-/

@[expose] public section
noncomputable section

open CategoryTheory MulOpposite

universe zGlobal rGlobal sGlobal aGlobal bGlobal

namespace ModuleCat.BalancedTensorRight

variable (R : Type rGlobal) (S : Type sGlobal) [Ring R] [Ring S]
  (B : Type bGlobal) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

/-- The tensor functor in the common carrier category. -/
def largeTensorFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    ModuleCat.{max r a b z} Rᵐᵒᵖ ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ :=
  tensorFunctor R S (ULift.{max r a b z} B)

/-- Underived input lifting does not assume projective resolutions in the raw world. -/
def tensorFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    ModuleCat.{a} Rᵐᵒᵖ ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ :=
  ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ ⋙
    largeTensorFunctorAt.{z, r, s, a, b} R S B

/-- The object is the existing balanced quotient of both actual native lifts. -/
abbrev tensorObjAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) :
    ModuleCat.{max r a b z} Sᵐᵒᵖ :=
  (tensorFunctorAt.{z, r, s, a, b} R S B).obj X

/-- The raw quotient retains its original two carriers and computed outer action. -/
def originalTensorObj (X : ModuleCat.{aGlobal} Rᵐᵒᵖ) : ModuleCat.{max aGlobal bGlobal} Sᵐᵒᵖ :=
  letI := TensorProduct.Balanced.rightModule ℤ R S X B
  ModuleCat.of Sᵐᵒᵖ (TensorProduct.Balanced ℤ R X B)

/-- A pure representative in the original, differently sized balanced quotient. -/
def originalTensorMk (X : ModuleCat.{aGlobal} Rᵐᵒᵖ) (x : X) (y : B) :
    originalTensorObj R S B X :=
  TensorProduct.Balanced.mk ℤ R X B x y

/-- The retained quotient moves the original right R action to the left coefficient. -/
theorem originalTensorMk_balance (X : ModuleCat.{aGlobal} Rᵐᵒᵖ)
    (rGlobal : R) (x : X) (y : B) :
    originalTensorMk R S B X (op rGlobal • x) y =
      originalTensorMk R S B X x (rGlobal • y) :=
  TensorProduct.Balanced.balance ℤ R X B rGlobal x y

/-- The outer action is the original right S action on the coefficient, in order. -/
theorem originalTensorMk_smul (X : ModuleCat.{aGlobal} Rᵐᵒᵖ)
    (t : Sᵐᵒᵖ) (x : X) (y : B) :
    t • originalTensorMk R S B X x y =
      originalTensorMk R S B X x (t • y) := by
  exact TensorProduct.Balanced.rightModule_smul_mk ℤ R S X B t x y

/-- An actual input morphism acts on the original quotient before any universe lift. -/
def originalTensorMap {X Y : ModuleCat.{aGlobal} Rᵐᵒᵖ} (f : X ⟶ Y) :
    originalTensorObj R S B X ⟶ originalTensorObj R S B Y := by
  letI := TensorProduct.Balanced.rightModule ℤ R S X B
  letI := TensorProduct.Balanced.rightModule ℤ R S Y B
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.CoefficientHom.tensorMap
      (R := R) (S := S) (B := B) (A := X) (A' := Y) f.hom)

/-- The original input map changes exactly the first pure representative. -/
theorem originalTensorMap_mk {X Y : ModuleCat.{aGlobal} Rᵐᵒᵖ}
    (f : X ⟶ Y) (x : X) (y : B) :
    (originalTensorMap R S B f).hom (originalTensorMk R S B X x y) =
      originalTensorMk R S B Y (f.hom x) y := by
  exact TensorProduct.Balanced.CoefficientHom.tensorMap_mk
    (R := R) (S := S) (B := B) (A := X) (A' := Y) f.hom x y

/-- The underived original-carrier tensor functor uses native balanced maps. -/
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

/-- Additivity of the original tensor functor is earned on its actual maps. -/
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

/-- Bundle the earned additivity without registering another global action instance. -/
def originalTensorAdditiveFunctor :
    ModuleCat.{aGlobal} Rᵐᵒᵖ ⥤+ ModuleCat.{max aGlobal bGlobal} Sᵐᵒᵖ := by
  letI := originalTensorFunctor_additive R S B
  exact AdditiveFunctor.of (originalTensorFunctor R S B)

/-- The actual input map is the native tensor functor applied to native input lifting. -/
def tensorMapAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] {X Y : ModuleCat.{a} Rᵐᵒᵖ} (f : X ⟶ Y) :
    tensorObjAt.{z, r, s, a, b} R S B X ⟶ tensorObjAt.{z, r, s, a, b} R S B Y :=
  (tensorFunctorAt.{z, r, s, a, b} R S B).map f

/-- Original representatives are sent by up-f-down on the first input. -/
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

/-- Down on both factors is earned outer-linear by the original balanced map. -/
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

/-- Up on both factors is the actual inverse outer-linear quotient map. -/
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

/-- Down on pure representatives retains their original noncommutative balance. -/
theorem tensorUnliftAt_mk.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ)
    (x : ULift.{max r a b z} X) (y : ULift.{max r a b z} B) :
    tensorUnliftAt.{z, r, s, a, b} R S B X
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) x y) =
      TensorProduct.Balanced.mk ℤ R X B x.down y.down := by
  exact TensorProduct.Balanced.uliftRightCarrierEquiv_mk ℤ R S X B x y

/-- Up retains the same original pure representative. -/
theorem tensorLiftAt_mk.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) (x : X) (y : B) :
    tensorLiftAt.{z, r, s, a, b} R S B X (TensorProduct.Balanced.mk ℤ R X B x y) =
      TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B) (ULift.up x) (ULift.up y) := by
  exact TensorProduct.Balanced.uliftRightCarrierEquiv_symm_mk ℤ R S X B x y

/-- An actual linear equivalence compares the differently sized quotient carriers. -/
def tensorCarrierEquivAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) :
    (tensorObjAt.{z, r, s, a, b} R S B X).carrier ≃ₗ[Sᵐᵒᵖ]
      (originalTensorObj R S B X).carrier := by
  letI := TensorProduct.Balanced.rightModule ℤ R S (ULift.{max r a b z} X)
    (ULift.{max r a b z} B)
  letI := TensorProduct.Balanced.rightModule ℤ R S X B
  exact TensorProduct.Balanced.uliftRightCarrierEquiv ℤ R S X B

/-- A category isomorphism compares the large tensor only after lifting the whole output. -/
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

/-- The whole-output comparison sends a lifted pure tensor to the lifted original class. -/
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

/-- The inverse whole-output comparison is the actual pair of native input lifts. -/
theorem tensorOutputLiftIsoAt_inv_mk.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (X : ModuleCat.{a} Rᵐᵒᵖ) (x : X) (y : B) :
    (tensorOutputLiftIsoAt.{z, r, s, a, b} R S B X).inv.hom
        (ULift.up (originalTensorMk R S B X x y)) =
      TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B) (ULift.up x) (ULift.up y) := by
  exact TensorProduct.Balanced.uliftRightEquiv_symm_mk ℤ R S X B x y

/-- Original input maps commute with the computed whole-output universe comparison. -/
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

/-- The independent-carrier tensor is naturally the whole-output lift of the original model. -/
def tensorOutputLiftNatIsoAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorFunctorAt.{z, r, s, a, b} R S B ≅
      originalTensorFunctor R S B ⋙
        ModuleCat.uliftFunctor.{max r a b z, max a b} Sᵐᵒᵖ :=
  NatIso.ofComponents (tensorOutputLiftIsoAt R S B)
    (fun {X Y} f => tensorOutputLiftIsoAt_naturality R S B f)

/-- The original common-carrier native tensor functor is recovered through the whole-output lift. -/
def tensorOriginalLiftIsoAt.{z, r, s, v}
    (R : Type r) (S : Type s) [Ring R] [Ring S]
    (C : Type v) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
    [SMulCommClass R Sᵐᵒᵖ C] :
    tensorFunctorAt.{z, r, s, v, v} R S C ≅
      tensorFunctor R S C ⋙ ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ :=
  tensorOutputLiftNatIsoAt.{z, r, s, v, v} R S C

section Heights


/-- Flatten the actual coefficient lifts in a sufficient larger carrier world. -/
def coefficientFlattenEquivAt.{t, z, r, a, b} (R : Type r) [Ring R]
    (B : Type b) [AddCommGroup B] [Module R B] :
    ULift.{max r a b z t} (ULift.{max r a b z} B) ≃ₗ[R]
      ULift.{max r a b z t} B :=
  ModuleCat.uliftFlattenEquiv.{max r a b z, max r a b z t} R B

/-- Coefficient flattening retains the original right S action. -/
theorem coefficientFlattenEquivAt_outer.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    (s : Sᵐᵒᵖ) (x : ULift.{max r a b z t} (ULift.{max r a b z} B)) :
    coefficientFlattenEquivAt.{t, z, r, a, b} R B (s • x) =
      s • coefficientFlattenEquivAt.{t, z, r, a, b} R B x := rfl

/-- The actual tensor coefficient comparison eliminates a double coefficient lift. -/
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

/-- Increasing the working universe commutes with the actual ordered balanced tensor.
The coefficient inverse and both module lifts are constructed, not provided as data. -/
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

/-- The height comparison has the actual original pure value in the lower tensor. -/
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

/-- The inverse height comparison keeps the same two original factors. -/
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
