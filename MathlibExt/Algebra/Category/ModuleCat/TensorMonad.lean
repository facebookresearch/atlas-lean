/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import MathlibExt.CategoryTheory.Monad.BarAlgebra

/-!
# The tensor monad on right modules

For a k-algebra R, the tensor monad sends a right R-module X to R ⊗[k] X,
with the right action on X. Its unit sends x to 1 ⊗ x, and its multiplication
sends a ⊗ b ⊗ x to (a * b) ⊗ x. The ground and algebra universes are
independent; universe lifting places the modules in a common category.

References: Weibel, Homological Algebra, §9.1; Loday, Cyclic Homology, §1.1.
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct ModuleCat.Algebra ZeroObject

universe u v w

namespace ModuleCat.Algebra.Hochschild

open scoped ModuleCat.Algebra

/-- The underlying `k`-module of a right `R`-module. -/
@[implicit_reducible]
noncomputable def underlying (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) : ModuleCat.{max u v w} k := by
  letI : Module k X.carrier := Module.compHom X.carrier (algebraMap k Rᵐᵒᵖ)
  exact ModuleCat.of k X.carrier

/-- The scalar restriction on morphisms. -/
noncomputable abbrev rightUnderlyingMap (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] {X Y : ModuleCat.{max u v w} Rᵐᵒᵖ} (f : X ⟶ Y) :
    underlying k R X ⟶ underlying k R Y :=
  (ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).map f

theorem rightUnderlyingMap_map_smul (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] {X Y : ModuleCat.{max u v w} Rᵐᵒᵖ} (f : X ⟶ Y)
    (s : Rᵐᵒᵖ) (x : (underlying k R X).carrier) :
    (rightUnderlyingMap k R f).hom
        (@SMul.smul Rᵐᵒᵖ X.carrier
          X.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
          s (show X.carrier from x)) =
      @SMul.smul Rᵐᵒᵖ Y.carrier
        Y.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul s
        (show Y.carrier from
          (rightUnderlyingMap k R f).hom x) := by
  change f.hom (s • (show X.carrier from x)) =
    s • f.hom (show X.carrier from x)
  exact f.hom.map_smul s (show X.carrier from x)

/-- The original right-module dictionary, transported to the restricted
carrier without registering a competing module instance. -/
noncomputable abbrev underlyingRightModule (k : Type u) (R : Type v) [CommRing k]
    [Ring R] [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) :
    Module Rᵐᵒᵖ (underlying k R X).carrier := by
  change Module Rᵐᵒᵖ X.carrier
  exact X.isModule

/-- The right `R`-action on `R ⊗ₖ X` is carried by `X`. -/
local instance underlyingSMulCommClass (k : Type u) (R : Type v) [CommRing k]
    [Ring R] [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) :
    @SMulCommClass k Rᵐᵒᵖ (underlying k R X).carrier
      (underlying k R X).isModule.toSMul
      (show SMul Rᵐᵒᵖ (underlying k R X).carrier from
        (let sX : SMul Rᵐᵒᵖ X.carrier :=
          X.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
         sX)) := by
  let kX : SMul k (underlying k R X).carrier := (underlying k R X).isModule.toSMul
  let sX : SMul Rᵐᵒᵖ X.carrier :=
    X.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  let sU : SMul Rᵐᵒᵖ (underlying k R X).carrier :=
    show SMul Rᵐᵒᵖ (underlying k R X).carrier from sX
  refine @SMulCommClass.mk k Rᵐᵒᵖ (underlying k R X).carrier kX sU ?_
  intro c s x
  change (MulOpposite.op (algebraMap k R c) : Rᵐᵒᵖ) •
      (s • (show X.carrier from x)) =
    s • ((MulOpposite.op (algebraMap k R c) : Rᵐᵒᵖ) • (show X.carrier from x))
  rw [← mul_smul, ← mul_smul]
  apply congrArg (fun t : Rᵐᵒᵖ => t • (show X.carrier from x))
  apply MulOpposite.unop_injective
  simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using
    (Algebra.commutes c (MulOpposite.unop s)).symm

/-- The `Rᵐᵒᵖ`-action on `R ⊗[k] X` through its `X` factor, transported along
`TensorProduct.comm` from `X ⊗[k] R`. -/
noncomputable def tensorRightSMul (k : Type u) (R : Type v) [CommRing k]
    [Ring R] [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) :
    SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) := by
  let U := underlying k R X
  let B := U.carrier ⊗[k] R
  let e := TensorProduct.comm k R U.carrier
  letI : SMul Rᵐᵒᵖ B :=
    @TensorProduct.leftHasSMul k Rᵐᵒᵖ _ _ U.carrier R
      U.isAddCommGroup.toAddCommMonoid _
      (underlyingRightModule k R X).toDistribMulAction
      U.isModule (Algebra.toModule : Module k R) (underlyingSMulCommClass k R X)
  exact e.toEquiv.smul Rᵐᵒᵖ

/-- The `Rᵐᵒᵖ`-module structure on `R ⊗[k] X` extending `tensorRightSMul`, transported
along `TensorProduct.comm` from `X ⊗[k] R`. -/
noncomputable def tensorRightModule (k : Type u) (R : Type v) [CommRing k]
    [Ring R] [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) :
    letI : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightSMul k R X
    Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) := by
  let U := underlying k R X
  let A := R ⊗[k] U.carrier
  let B := U.carrier ⊗[k] R
  let e := TensorProduct.comm k R U.carrier
  letI : Module Rᵐᵒᵖ B :=
    @TensorProduct.leftModule k Rᵐᵒᵖ _ _ U.carrier R
      U.isAddCommGroup.toAddCommMonoid _ (underlyingRightModule k R X)
      U.isModule (Algebra.toModule : Module k R) (underlyingSMulCommClass k R X)
  letI : SMul Rᵐᵒᵖ A := tensorRightSMul k R X
  exact e.toAddEquiv.module Rᵐᵒᵖ

@[simp]
theorem tensorRightModule_smul_tmul (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (s : Rᵐᵒᵖ) (r : R)
    (x : (underlying k R X).carrier) :
    @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
        (tensorRightSMul k R X) s (r ⊗ₜ[k] x) =
      r ⊗ₜ[k] (show (underlying k R X).carrier from
        @SMul.smul Rᵐᵒᵖ X.carrier
          X.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
          s (show X.carrier from x)) := by
  let sx := @SMul.smul Rᵐᵒᵖ X.carrier
    X.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
    s (show X.carrier from x)
  change (TensorProduct.comm k R (underlying k R X).carrier).symm
      ((show (underlying k R X).carrier from sx) ⊗ₜ[k] r) =
        r ⊗ₜ[k] (show (underlying k R X).carrier from sx)
  exact TensorProduct.comm_symm_tmul k R
    (underlying k R X).carrier r
      (show (underlying k R X).carrier from sx)

theorem tensorRightSMul_smul_add (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (s : Rᵐᵒᵖ)
    (x y : R ⊗[k] (underlying k R X).carrier) :
    @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
        (tensorRightSMul k R X) s (x + y) =
      @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
          (tensorRightSMul k R X) s x +
        @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
          (tensorRightSMul k R X) s y := by
  let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightSMul k R X
  let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightModule k R X
  exact (tensorRightModule k R X).toDistribMulAction.smul_add s x y

/-- Object part of the tensor monad on right `R`-modules. -/
noncomputable abbrev tensorObj (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) : ModuleCat.{max u v w} Rᵐᵒᵖ := by
  letI : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightSMul k R X
  letI : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightModule k R X
  exact ModuleCat.of Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)

theorem tensorObj_smul_eq (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (s : Rᵐᵒᵖ)
    (z : (underlying k R (tensorObj k R X)).carrier) :
    (show (underlying k R (tensorObj k R X)).carrier from
      @SMul.smul Rᵐᵒᵖ (tensorObj k R X).carrier
        (tensorObj k R X).isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        s (show (tensorObj k R X).carrier from z)) =
      @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
        (tensorRightSMul k R X) s
        (show (R ⊗[k] (underlying k R X).carrier) from z) := by
  rfl

/-- `id_R ⊗ f`, as a morphism of right `R`-modules. -/
noncomputable def tensorMap (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    {X Y : ModuleCat.{max u v w} Rᵐᵒᵖ} (f : X ⟶ Y) :
    tensorObj k R X ⟶ tensorObj k R Y := by
  letI : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightSMul k R X
  letI : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
    tensorRightSMul k R Y
  letI : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightModule k R X
  letI : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
    tensorRightModule k R Y
  change ModuleCat.of Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) ⟶
    ModuleCat.of Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier)
  exact ModuleCat.ofHom
    { toFun := TensorProduct.map LinearMap.id
        (rightUnderlyingMap k R f).hom
      map_add' := by
        intro x y
        exact (TensorProduct.map (LinearMap.id : R →ₗ[k] R)
          (rightUnderlyingMap k R f).hom).map_add x y
      map_smul' := by
        intro s z
        change (TensorProduct.map LinearMap.id
            (rightUnderlyingMap k R f).hom)
              (@SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
                (tensorRightSMul k R X) s z) =
          @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier)
            (tensorRightSMul k R Y) s
              ((TensorProduct.map LinearMap.id
                (rightUnderlyingMap k R f).hom) z)
        induction z using TensorProduct.inductionOn with
        | tmul r x =>
            rw [tensorRightModule_smul_tmul k R X s r x,
              TensorProduct.map_tmul, LinearMap.id_apply]
            change r ⊗ₜ[k]
                (rightUnderlyingMap k R f).hom
                  (@SMul.smul Rᵐᵒᵖ X.carrier
                    X.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
                    s (show X.carrier from x)) =
              @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier)
                (tensorRightSMul k R Y) s
                  (r ⊗ₜ[k]
                    (rightUnderlyingMap k R f).hom x)
            rw [rightUnderlyingMap_map_smul,
              tensorRightModule_smul_tmul]
        | add x y hx hy =>
            rw [tensorRightSMul_smul_add, map_add, hx, hy, map_add,
              tensorRightSMul_smul_add] }

@[simp]
theorem tensorMap_tmul (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    {X Y : ModuleCat.{max u v w} Rᵐᵒᵖ} (f : X ⟶ Y) (r : R) (x : X.carrier) :
    (tensorMap k R f).hom (r ⊗ₜ[k] x) = r ⊗ₜ[k] f.hom x :=
  by
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightSMul k R X
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
      tensorRightSMul k R Y
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightModule k R X
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
      tensorRightModule k R Y
    change (TensorProduct.map (LinearMap.id : R →ₗ[k] R)
        (rightUnderlyingMap k R f).hom) (r ⊗ₜ[k] x) =
      r ⊗ₜ[k] f.hom x
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    rfl

/-- Tensoring on the left by `R`, with the right action retained on the
second factor. -/
noncomputable def tensorFunctor (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] : ModuleCat.{max u v w} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} Rᵐᵒᵖ where
  obj := tensorObj k R
  map := tensorMap k R
  map_id X := by
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightSMul k R X
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightModule k R X
    change tensorMap k R (𝟙 X) =
      𝟙 (ModuleCat.of Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier))
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change R ⊗[k] (underlying k R X).carrier at z
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
        change (tensorMap k R (𝟙 X)).hom (r ⊗ₜ[k] x) = r ⊗ₜ[k] x
        rw [tensorMap_tmul]
        rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  map_comp {X Y Z} f g := by
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightSMul k R X
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
      tensorRightSMul k R Y
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R Z).carrier) :=
      tensorRightSMul k R Z
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightModule k R X
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
      tensorRightModule k R Y
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R Z).carrier) :=
      tensorRightModule k R Z
    change tensorMap k R (f ≫ g) = tensorMap k R f ≫ tensorMap k R g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change R ⊗[k] (underlying k R X).carrier at z
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
        rw [tensorMap_tmul, tensorMap_tmul, tensorMap_tmul]
        rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Unit `x ↦ 1 ⊗ x` of the lifted tensor monad. -/
noncomputable def tensorUnit (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) : X ⟶ tensorObj k R X := by
  letI : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightSMul k R X
  letI : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightModule k R X
  change X ⟶ ModuleCat.of Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
  exact ModuleCat.ofHom
    { toFun := fun x => 1 ⊗ₜ[k]
        (show (underlying k R X).carrier from x)
      map_add' := by
        intro x y
        exact TensorProduct.tmul_add (1 : R)
          (show (underlying k R X).carrier from x)
          (show (underlying k R X).carrier from y)
      map_smul' := by
        intro s x
        exact (tensorRightModule_smul_tmul k R X s 1
          (show (underlying k R X).carrier from x)).symm }

@[simp]
theorem tensorUnit_apply (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (x : X.carrier) :
    (tensorUnit k R X).hom x = 1 ⊗ₜ[k] x :=
  by
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightSMul k R X
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightModule k R X
    unfold tensorUnit
    rfl

theorem tensorUnderlying_smul_eq (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (c : k)
    (z : (underlying k R (tensorObj k R X)).carrier) :
    @SMul.smul k (underlying k R (tensorObj k R X)).carrier
        (underlying k R
            (tensorObj k R X)).isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        c z =
      @SMul.smul k
        (ModuleCat.of k (R ⊗[k] (underlying k R X).carrier)).carrier
        (ModuleCat.of k
          (R ⊗[k]
              (underlying k R
                X).carrier)).isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        c (show (ModuleCat.of k
          (R ⊗[k] (underlying k R X).carrier)).carrier from z) := by
  change @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
      (tensorRightSMul k R X) (MulOpposite.op (algebraMap k R c)) z =
    c • (show R ⊗[k] (underlying k R X).carrier from z)
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
      rw [tensorRightModule_smul_tmul]
      change r ⊗ₜ[k] (c • x) = c • (r ⊗ₜ[k] x)
      exact TensorProduct.tmul_smul c r x
  | add x y hx hy =>
      rw [tensorRightSMul_smul_add, smul_add, hx, hy]

/-- Restricting the lifted right action back to `k` recovers the ordinary
tensor-product `k`-module. -/
noncomputable def tensorUnderlyingIso (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) :
    underlying k R (tensorObj k R X) ≅
      ModuleCat.of k (R ⊗[k] (underlying k R X).carrier) := by
  let A := underlying k R (tensorObj k R X)
  let B := ModuleCat.of k (R ⊗[k] (underlying k R X).carrier)
  let hom : A ⟶ B := @ModuleCat.ofHom k _ A.carrier B.carrier
    A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule
    (@LinearMap.mk k k _ _ (RingHom.id k) A.carrier B.carrier
      A.isAddCommGroup.toAddCommMonoid B.isAddCommGroup.toAddCommMonoid
      A.isModule B.isModule
      { toFun := id, map_add' := fun _ _ => rfl } (by
        intro c z
        exact tensorUnderlying_smul_eq k R X c z))
  let inv : B ⟶ A := @ModuleCat.ofHom k _ B.carrier A.carrier
    B.isAddCommGroup B.isModule A.isAddCommGroup A.isModule
    (@LinearMap.mk k k _ _ (RingHom.id k) B.carrier A.carrier
      B.isAddCommGroup.toAddCommMonoid A.isAddCommGroup.toAddCommMonoid
      B.isModule A.isModule
      { toFun := id, map_add' := fun _ _ => rfl } (by
        intro c z
        exact (tensorUnderlying_smul_eq k R X c
          (show (underlying k R (tensorObj k R X)).carrier from z)).symm))
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        rfl
      inv_hom_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        rfl }

@[simp]
theorem tensorUnderlyingIso_hom_apply (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ)
    (z : (underlying k R (tensorObj k R X)).carrier) :
    (tensorUnderlyingIso k R X).hom.hom z = z :=
  rfl

@[simp]
theorem tensorUnderlyingIso_inv_apply (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ)
    (z : R ⊗[k] (underlying k R X).carrier) :
    (tensorUnderlyingIso k R X).inv.hom z = z :=
  rfl

theorem tensorUnderlying_induction
    (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ)
    (P : (underlying k R (tensorObj k R X)).carrier → Prop)
    (ht : ∀ (r : R) (x : (underlying k R X).carrier),
      P ((tensorUnderlyingIso k R X).inv.hom (r ⊗ₜ[k] x)))
    (ha : ∀ x y, P x → P y → P (x + y))
    (z : (underlying k R (tensorObj k R X)).carrier) : P z := by
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
      have hInv : (tensorUnderlyingIso k R X).inv.hom (r ⊗ₜ[k] x) =
          (show (underlying k R (tensorObj k R X)).carrier from r ⊗ₜ[k] x) :=
        tensorUnderlyingIso_inv_apply k R X (r ⊗ₜ[k] x)
      exact (congrArg P hInv).mp (ht r x)
  | add x y hx hy => exact ha _ _ hx hy

theorem tensorUnderlyingIso_hom_map_smul
    (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (s : Rᵐᵒᵖ)
    (z : (underlying k R (tensorObj k R X)).carrier) :
    (tensorUnderlyingIso k R X).hom.hom
        (@SMul.smul Rᵐᵒᵖ (tensorObj k R X).carrier
          (tensorObj k R X).isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
          s (show (tensorObj k R X).carrier from z)) =
      @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
        (tensorRightSMul k R X) s
          ((tensorUnderlyingIso k R X).hom.hom z) := by
  rw [tensorUnderlyingIso_hom_apply, tensorUnderlyingIso_hom_apply]
  change (show (R ⊗[k] (underlying k R X).carrier) from
      @SMul.smul Rᵐᵒᵖ (tensorObj k R X).carrier
        (tensorObj k R X).isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        s (show (tensorObj k R X).carrier from z)) =
    @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
      (tensorRightSMul k R X) s
        (show (R ⊗[k] (underlying k R X).carrier) from z)
  exact tensorObj_smul_eq k R X s z

/-- Multiplication `r ⊗ (s ⊗ x) ↦ rs ⊗ x` of the lifted tensor monad. -/
noncomputable def tensorMul (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) :
    tensorObj k R (tensorObj k R X) ⟶ tensorObj k R X := by
  let TX := tensorObj k R X
  letI : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightSMul k R X
  letI : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightModule k R X
  letI : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
    tensorRightSMul k R TX
  letI : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
    tensorRightModule k R TX
  let collapse : (R ⊗[k] (underlying k R TX).carrier) →ₗ[k]
      (R ⊗[k] (underlying k R X).carrier) :=
    (TensorProduct.map (LinearMap.mul' k R) LinearMap.id).comp
      ((TensorProduct.assoc k R R
        (underlying k R X).carrier).symm.toLinearMap.comp
          (TensorProduct.map LinearMap.id
            (tensorUnderlyingIso k R X).hom.hom))
  change ModuleCat.of Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) ⟶
    ModuleCat.of Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
  exact ModuleCat.ofHom
    { toFun := collapse
      map_add' := collapse.map_add
      map_smul' := by
        intro s z
        change collapse
            (@SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier)
              (tensorRightSMul k R TX) s z) =
          @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
            (tensorRightSMul k R X) s (collapse z)
        induction z using TensorProduct.inductionOn with
        | tmul r y =>
            rw [tensorRightModule_smul_tmul k R TX s r y]
            let sy : (underlying k R TX).carrier :=
              show (underlying k R TX).carrier from
                @SMul.smul Rᵐᵒᵖ TX.carrier
                  TX.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
                  s (show TX.carrier from y)
            change collapse (r ⊗ₜ[k] sy) =
              @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
                (tensorRightSMul k R X) s (collapse (r ⊗ₜ[k] y))
            simp only [collapse, LinearMap.comp_apply, TensorProduct.map_tmul,
              LinearMap.id_apply]
            rw [show (tensorUnderlyingIso k R X).hom.hom sy =
              @SMul.smul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier)
                (tensorRightSMul k R X) s
                  ((tensorUnderlyingIso k R X).hom.hom y) by
                    exact tensorUnderlyingIso_hom_map_smul k R X s y]
            let w : R ⊗[k] (underlying k R X).carrier :=
              (tensorUnderlyingIso k R X).hom.hom y
            change (TensorProduct.map (LinearMap.mul' k R) LinearMap.id)
                ((TensorProduct.assoc k R R
                  (underlying k R X).carrier).symm
                    (r ⊗ₜ[k]
                      @SMul.smul Rᵐᵒᵖ
                        (R ⊗[k] (underlying k R X).carrier)
                        (tensorRightSMul k R X) s w)) =
              @SMul.smul Rᵐᵒᵖ
                (R ⊗[k] (underlying k R X).carrier)
                (tensorRightSMul k R X) s
                  ((TensorProduct.map (LinearMap.mul' k R) LinearMap.id)
                    ((TensorProduct.assoc k R R
                      (underlying k R X).carrier).symm (r ⊗ₜ[k] w)))
            induction w using TensorProduct.inductionOn with
            | tmul r' x =>
                rw [tensorRightModule_smul_tmul k R X s r' x]
                simp only [TensorProduct.assoc_symm_tmul,
                  TensorProduct.map_tmul, LinearMap.id_apply,
                  LinearMap.mul'_apply]
                exact (tensorRightModule_smul_tmul k R X s
                  (r * r') x).symm
            | add x y hx hy =>
                rw [tensorRightSMul_smul_add k R X,
                  TensorProduct.tmul_add, map_add, map_add, hx, hy,
                  TensorProduct.tmul_add, map_add, map_add,
                  tensorRightSMul_smul_add k R X]
        | add x y hx hy =>
            rw [tensorRightSMul_smul_add k R TX, collapse.map_add, hx, hy,
              collapse.map_add, tensorRightSMul_smul_add k R X] }

private theorem tensorMap_tmul_via_underlyingIso
    (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    {X Y : ModuleCat.{max u v w} Rᵐᵒᵖ} (f : X ⟶ Y) (r : R) (x : X.carrier) :
    (tensorMap k R f).hom
        (show (tensorObj k R X).carrier from
          (tensorUnderlyingIso k R X).inv.hom
            (r ⊗ₜ[k] (show (underlying k R X).carrier from x))) =
      (show (tensorObj k R Y).carrier from
        (tensorUnderlyingIso k R Y).inv.hom
          (r ⊗ₜ[k]
            (show (underlying k R Y).carrier from f.hom x))) := by
  let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightSMul k R X
  let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightModule k R X
  let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
    tensorRightSMul k R Y
  let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
    tensorRightModule k R Y
  rw [tensorUnderlyingIso_inv_apply, tensorUnderlyingIso_inv_apply]
  exact tensorMap_tmul k R f r x

theorem tensorMul_tmul_via_underlyingIso
    (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (r s : R) (x : X.carrier) :
    (tensorMul k R X).hom
        (r ⊗ₜ[k]
          (show (underlying k R (tensorObj k R X)).carrier from
            (tensorUnderlyingIso k R X).inv.hom
              (s ⊗ₜ[k]
                (show (underlying k R X).carrier from x)))) =
      (r * s) ⊗ₜ[k] x := by
  let TX := tensorObj k R X
  let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightSMul k R X
  let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightModule k R X
  let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
    tensorRightSMul k R TX
  let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
    tensorRightModule k R TX
  change (TensorProduct.map (LinearMap.mul' k R) LinearMap.id)
      ((TensorProduct.assoc k R R (underlying k R X).carrier).symm
        ((TensorProduct.map LinearMap.id
          (tensorUnderlyingIso k R X).hom.hom)
            (r ⊗ₜ[k] (tensorUnderlyingIso k R X).inv.hom
              (s ⊗ₜ[k]
                (show (underlying k R X).carrier from x))))) =
    (r * s) ⊗ₜ[k] (show (underlying k R X).carrier from x)
  rw [TensorProduct.map_tmul, LinearMap.id_apply,
    tensorUnderlyingIso_hom_apply, tensorUnderlyingIso_inv_apply,
    TensorProduct.assoc_symm_tmul,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mul'_apply]

@[simp]
theorem tensorMul_tmul (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (r s : R) (x : X.carrier) :
    (tensorMul k R X).hom (r ⊗ₜ[k] (s ⊗ₜ[k] x)) = (r * s) ⊗ₜ[k] x := by
  let y : R ⊗[k] (underlying k R X).carrier :=
    s ⊗ₜ[k] (show (underlying k R X).carrier from x)
  have hInv : (tensorUnderlyingIso k R X).inv.hom y =
      (show (underlying k R (tensorObj k R X)).carrier from y) :=
    tensorUnderlyingIso_inv_apply k R X y
  have hLift := congrArg
    (fun z : (underlying k R (tensorObj k R X)).carrier =>
      (tensorMul k R X).hom (r ⊗ₜ[k] z)) hInv
  exact hLift.symm.trans (tensorMul_tmul_via_underlyingIso k R X r s x)

/-- The monad `T(X) = R ⊗ₖ X` on right `R`-modules. -/
noncomputable def tensorMonad (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] : CategoryTheory.Monad (ModuleCat.{max u v w} Rᵐᵒᵖ) where
  toFunctor := tensorFunctor k R
  η :=
    { app := tensorUnit k R
      naturality := by
        intro X Y f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (tensorUnit k R Y).hom (f.hom x) =
          (tensorMap k R f).hom ((tensorUnit k R X).hom x)
        rw [tensorUnit_apply, tensorUnit_apply]
        change (1 : R) ⊗ₜ[k]
            (show (underlying k R Y).carrier from f.hom x) =
          (TensorProduct.map LinearMap.id
              (rightUnderlyingMap k R f).hom)
            ((1 : R) ⊗ₜ[k]
              (show (underlying k R X).carrier from x))
        rw [TensorProduct.map_tmul, LinearMap.id_apply]
        rfl }
  μ :=
    { app := tensorMul k R
      naturality := by
        intro X Y f
        let TX := tensorObj k R X
        let TY := tensorObj k R Y
        let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
          tensorRightSMul k R X
        let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
          tensorRightModule k R X
        let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
          tensorRightSMul k R Y
        let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
          tensorRightModule k R Y
        let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
          tensorRightSMul k R TX
        let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
          tensorRightModule k R TX
        let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R TY).carrier) :=
          tensorRightSMul k R TY
        let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R TY).carrier) :=
          tensorRightModule k R TY
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change R ⊗[k] (underlying k R TX).carrier at z
        change (tensorMul k R Y).hom
            ((tensorMap k R (tensorMap k R f)).hom z) =
          (tensorMap k R f).hom ((tensorMul k R X).hom z)
        induction z using TensorProduct.inductionOn with
        | tmul r y =>
            induction y using TensorProduct.inductionOn with
            | tmul s x =>
                let xX : X.carrier := show X.carrier from x
                let sx : (underlying k R TX).carrier :=
                  (tensorUnderlyingIso k R X).inv.hom
                    (s ⊗ₜ[k]
                      (show (underlying k R X).carrier from xX))
                let sy : (underlying k R TY).carrier :=
                  (tensorUnderlyingIso k R Y).inv.hom
                    (s ⊗ₜ[k]
                      (show (underlying k R Y).carrier from f.hom xX))
                let zX : (tensorObj k R TX).carrier :=
                  r ⊗ₜ[k] sx
                let outX : TX.carrier :=
                  show TX.carrier from
                    (r * s) ⊗ₜ[k]
                      (show (underlying k R X).carrier from xX)
                let outY : TY.carrier :=
                  show TY.carrier from
                    (r * s) ⊗ₜ[k]
                      (show (underlying k R Y).carrier from f.hom xX)
                change (tensorMul k R Y).hom
                    ((tensorMap k R (tensorMap k R f)).hom zX) =
                  (tensorMap k R f).hom ((tensorMul k R X).hom zX)
                calc
                  (tensorMul k R Y).hom
                      ((tensorMap k R (tensorMap k R f)).hom zX) =
                    (tensorMul k R Y).hom
                      (r ⊗ₜ[k]
                        (show (underlying k R TY).carrier from
                          (tensorMap k R f).hom
                            (show TX.carrier from sx))) :=
                      congrArg (tensorMul k R Y).hom
                        (tensorMap_tmul k R (tensorMap k R f) r
                          (show TX.carrier from sx))
                  _ = (tensorMul k R Y).hom
                      (r ⊗ₜ[k] sy) :=
                    congrArg (fun q =>
                      (tensorMul k R Y).hom (r ⊗ₜ[k] q))
                      (tensorMap_tmul_via_underlyingIso k R f s xX)
                  _ = outY :=
                    tensorMul_tmul_via_underlyingIso k R Y r s (f.hom xX)
                  _ = (tensorMap k R f).hom outX :=
                    (tensorMap_tmul k R f (r * s) xX).symm
                  _ = (tensorMap k R f).hom
                      ((tensorMul k R X).hom zX) :=
                    congrArg (tensorMap k R f).hom
                      (tensorMul_tmul_via_underlyingIso k R X r s xX).symm
            | add x y hx hy =>
                let ux : (underlying k R TX).carrier :=
                  show (underlying k R TX).carrier from x
                let uy : (underlying k R TX).carrier :=
                  show (underlying k R TX).carrier from y
                let zx : (tensorObj k R TX).carrier := r ⊗ₜ[k] ux
                let zy : (tensorObj k R TX).carrier := r ⊗ₜ[k] uy
                change (tensorMul k R Y).hom
                    ((tensorMap k R (tensorMap k R f)).hom
                      (r ⊗ₜ[k] (ux + uy))) =
                  (tensorMap k R f).hom
                    ((tensorMul k R X).hom (r ⊗ₜ[k] (ux + uy)))
                rw [show r ⊗ₜ[k] (ux + uy) = zx + zy by
                  exact TensorProduct.tmul_add r ux uy]
                calc
                  (tensorMul k R Y).hom
                      ((tensorMap k R (tensorMap k R f)).hom (zx + zy)) =
                    (tensorMul k R Y).hom
                      ((tensorMap k R (tensorMap k R f)).hom zx +
                        (tensorMap k R (tensorMap k R f)).hom zy) :=
                      congrArg (tensorMul k R Y).hom
                        ((tensorMap k R (tensorMap k R f)).hom.map_add zx zy)
                  _ = (tensorMul k R Y).hom
                        ((tensorMap k R (tensorMap k R f)).hom zx) +
                      (tensorMul k R Y).hom
                        ((tensorMap k R (tensorMap k R f)).hom zy) :=
                    (tensorMul k R Y).hom.map_add _ _
                  _ = (tensorMap k R f).hom ((tensorMul k R X).hom zx) +
                      (tensorMap k R f).hom ((tensorMul k R X).hom zy) :=
                    congrArg₂ (· + ·) hx hy
                  _ = (tensorMap k R f).hom
                      ((tensorMul k R X).hom zx +
                        (tensorMul k R X).hom zy) :=
                    ((tensorMap k R f).hom.map_add _ _).symm
                  _ = (tensorMap k R f).hom
                      ((tensorMul k R X).hom (zx + zy)) :=
                    congrArg (tensorMap k R f).hom
                      ((tensorMul k R X).hom.map_add zx zy).symm
        | add x y hx hy =>
            calc
              (tensorMul k R Y).hom
                  ((tensorMap k R (tensorMap k R f)).hom (x + y)) =
                (tensorMul k R Y).hom
                  ((tensorMap k R (tensorMap k R f)).hom x +
                    (tensorMap k R (tensorMap k R f)).hom y) :=
                  congrArg (tensorMul k R Y).hom
                    ((tensorMap k R (tensorMap k R f)).hom.map_add x y)
              _ = (tensorMul k R Y).hom
                    ((tensorMap k R (tensorMap k R f)).hom x) +
                  (tensorMul k R Y).hom
                    ((tensorMap k R (tensorMap k R f)).hom y) :=
                (tensorMul k R Y).hom.map_add _ _
              _ = (tensorMap k R f).hom ((tensorMul k R X).hom x) +
                  (tensorMap k R f).hom ((tensorMul k R X).hom y) :=
                congrArg₂ (· + ·) hx hy
              _ = (tensorMap k R f).hom
                  ((tensorMul k R X).hom x +
                    (tensorMul k R X).hom y) :=
                ((tensorMap k R f).hom.map_add _ _).symm
              _ = (tensorMap k R f).hom
                  ((tensorMul k R X).hom (x + y)) :=
                congrArg (tensorMap k R f).hom
                  ((tensorMul k R X).hom.map_add x y).symm }
  assoc X := by
    let TX := tensorObj k R X
    let TTX := tensorObj k R TX
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightSMul k R X
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightModule k R X
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
      tensorRightSMul k R TX
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
      tensorRightModule k R TX
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R TTX).carrier) :=
      tensorRightSMul k R TTX
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R TTX).carrier) :=
      tensorRightModule k R TTX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change R ⊗[k] (underlying k R TTX).carrier at z
    change (tensorMul k R X).hom
        ((tensorMap k R (tensorMul k R X)).hom z) =
      (tensorMul k R X).hom ((tensorMul k R (tensorObj k R X)).hom z)
    induction z using TensorProduct.inductionOn with
    | tmul r y =>
        induction y using TensorProduct.inductionOn with
        | tmul s q =>
            induction q using TensorProduct.inductionOn with
            | tmul t x =>
                let xX : X.carrier := show X.carrier from x
                let tx : (underlying k R TX).carrier :=
                  (tensorUnderlyingIso k R X).inv.hom
                    (t ⊗ₜ[k]
                      (show (underlying k R X).carrier from xX))
                let stx : (underlying k R TTX).carrier :=
                  (tensorUnderlyingIso k R TX).inv.hom
                    (s ⊗ₜ[k] tx)
                let zX : (tensorObj k R TTX).carrier := r ⊗ₜ[k] stx
                let st : (underlying k R TX).carrier :=
                  (tensorUnderlyingIso k R X).inv.hom
                    ((s * t) ⊗ₜ[k]
                      (show (underlying k R X).carrier from xX))
                let rst : TTX.carrier :=
                  show TTX.carrier from (r * s) ⊗ₜ[k] tx
                have hst :
                    (show (underlying k R TX).carrier from
                      (tensorMul k R X).hom
                        (show TTX.carrier from stx)) = st := by
                  calc
                    (show (underlying k R TX).carrier from
                        (tensorMul k R X).hom
                          (show TTX.carrier from stx)) =
                      (show (underlying k R TX).carrier from
                        (tensorMul k R X).hom
                          (s ⊗ₜ[k] tx)) := by
                            apply congrArg (fun q : TTX.carrier =>
                              show (underlying k R TX).carrier from
                                (tensorMul k R X).hom q)
                            dsimp only [stx]
                            rw [tensorUnderlyingIso_inv_apply]
                    _ = (show (underlying k R TX).carrier from
                        (s * t) ⊗ₜ[k] xX) :=
                      tensorMul_tmul_via_underlyingIso k R X s t xX
                    _ = st := by
                      dsimp only [st]
                      rw [tensorUnderlyingIso_inv_apply]
                have hrst :
                    (tensorMul k R TX).hom zX = rst := by
                  exact tensorMul_tmul_via_underlyingIso k R TX r s
                    (show TX.carrier from tx)
                change (tensorMul k R X).hom
                    ((tensorMap k R (tensorMul k R X)).hom zX) =
                  (tensorMul k R X).hom
                    ((tensorMul k R TX).hom zX)
                calc
                  (tensorMul k R X).hom
                      ((tensorMap k R (tensorMul k R X)).hom zX) =
                    (tensorMul k R X).hom
                      (r ⊗ₜ[k]
                        (show (underlying k R TX).carrier from
                          (tensorMul k R X).hom
                            (show TTX.carrier from stx))) :=
                      congrArg (tensorMul k R X).hom
                        (tensorMap_tmul k R (tensorMul k R X) r
                          (show TTX.carrier from stx))
                  _ = (tensorMul k R X).hom
                      (r ⊗ₜ[k] st) :=
                    congrArg (fun q =>
                      (tensorMul k R X).hom (r ⊗ₜ[k] q))
                      hst
                  _ = (r * (s * t)) ⊗ₜ[k] xX :=
                    tensorMul_tmul_via_underlyingIso k R X r (s * t) xX
                  _ = ((r * s) * t) ⊗ₜ[k] xX := by rw [mul_assoc]
                  _ = (tensorMul k R X).hom
                      ((r * s) ⊗ₜ[k] tx) :=
                    (tensorMul_tmul_via_underlyingIso k R X
                      (r * s) t xX).symm
                  _ = (tensorMul k R X).hom
                      ((tensorMul k R TX).hom zX) :=
                    congrArg (tensorMul k R X).hom
                      hrst.symm
            | add x y hx hy =>
                let ux : (underlying k R TX).carrier :=
                  show (underlying k R TX).carrier from x
                let uy : (underlying k R TX).carrier :=
                  show (underlying k R TX).carrier from y
                let sx : (underlying k R TTX).carrier :=
                  (tensorUnderlyingIso k R TX).inv.hom (s ⊗ₜ[k] ux)
                let sy : (underlying k R TTX).carrier :=
                  (tensorUnderlyingIso k R TX).inv.hom (s ⊗ₜ[k] uy)
                let sxy : (underlying k R TTX).carrier :=
                  (tensorUnderlyingIso k R TX).inv.hom
                    (s ⊗ₜ[k] (ux + uy))
                let zx : (tensorObj k R TTX).carrier := r ⊗ₜ[k] sx
                let zy : (tensorObj k R TTX).carrier := r ⊗ₜ[k] sy
                let zxy : (tensorObj k R TTX).carrier := r ⊗ₜ[k] sxy
                change (tensorMul k R X).hom
                    ((tensorMap k R (tensorMul k R X)).hom zxy) =
                  (tensorMul k R X).hom
                    ((tensorMul k R TX).hom zxy)
                have hsxy : sxy = sx + sy := by
                  dsimp only [sxy, sx, sy]
                  rw [TensorProduct.tmul_add,
                    (tensorUnderlyingIso k R TX).inv.hom.map_add]
                dsimp only [zxy]
                rw [hsxy, TensorProduct.tmul_add]
                calc
                  (tensorMul k R X).hom
                      ((tensorMap k R (tensorMul k R X)).hom (zx + zy)) =
                    (tensorMul k R X).hom
                      ((tensorMap k R (tensorMul k R X)).hom zx +
                        (tensorMap k R (tensorMul k R X)).hom zy) :=
                      congrArg (tensorMul k R X).hom
                        ((tensorMap k R (tensorMul k R X)).hom.map_add zx zy)
                  _ = (tensorMul k R X).hom
                        ((tensorMap k R (tensorMul k R X)).hom zx) +
                      (tensorMul k R X).hom
                        ((tensorMap k R (tensorMul k R X)).hom zy) :=
                    (tensorMul k R X).hom.map_add _ _
                  _ = (tensorMul k R X).hom
                        ((tensorMul k R TX).hom zx) +
                      (tensorMul k R X).hom
                        ((tensorMul k R TX).hom zy) :=
                    congrArg₂ (· + ·) hx hy
                  _ = (tensorMul k R X).hom
                      ((tensorMul k R TX).hom zx +
                        (tensorMul k R TX).hom zy) :=
                    ((tensorMul k R X).hom.map_add _ _).symm
                  _ = (tensorMul k R X).hom
                      ((tensorMul k R TX).hom (zx + zy)) :=
                    congrArg (tensorMul k R X).hom
                      ((tensorMul k R TX).hom.map_add zx zy).symm
        | add x y hx hy =>
            let ux : (underlying k R TTX).carrier :=
              show (underlying k R TTX).carrier from x
            let uy : (underlying k R TTX).carrier :=
              show (underlying k R TTX).carrier from y
            let zx : (tensorObj k R TTX).carrier := r ⊗ₜ[k] ux
            let zy : (tensorObj k R TTX).carrier := r ⊗ₜ[k] uy
            change (tensorMul k R X).hom
                ((tensorMap k R (tensorMul k R X)).hom
                  (r ⊗ₜ[k] (ux + uy))) =
              (tensorMul k R X).hom
                ((tensorMul k R TX).hom (r ⊗ₜ[k] (ux + uy)))
            rw [show r ⊗ₜ[k] (ux + uy) = zx + zy by
              exact TensorProduct.tmul_add r ux uy]
            calc
              (tensorMul k R X).hom
                  ((tensorMap k R (tensorMul k R X)).hom (zx + zy)) =
                (tensorMul k R X).hom
                  ((tensorMap k R (tensorMul k R X)).hom zx +
                    (tensorMap k R (tensorMul k R X)).hom zy) :=
                  congrArg (tensorMul k R X).hom
                    ((tensorMap k R (tensorMul k R X)).hom.map_add zx zy)
              _ = (tensorMul k R X).hom
                    ((tensorMap k R (tensorMul k R X)).hom zx) +
                  (tensorMul k R X).hom
                    ((tensorMap k R (tensorMul k R X)).hom zy) :=
                (tensorMul k R X).hom.map_add _ _
              _ = (tensorMul k R X).hom ((tensorMul k R TX).hom zx) +
                  (tensorMul k R X).hom ((tensorMul k R TX).hom zy) :=
                congrArg₂ (· + ·) hx hy
              _ = (tensorMul k R X).hom
                  ((tensorMul k R TX).hom zx +
                    (tensorMul k R TX).hom zy) :=
                ((tensorMul k R X).hom.map_add _ _).symm
              _ = (tensorMul k R X).hom
                  ((tensorMul k R TX).hom (zx + zy)) :=
                congrArg (tensorMul k R X).hom
                  ((tensorMul k R TX).hom.map_add zx zy).symm
    | add x y hx hy =>
        calc
          (tensorMul k R X).hom
              ((tensorMap k R (tensorMul k R X)).hom (x + y)) =
            (tensorMul k R X).hom
              ((tensorMap k R (tensorMul k R X)).hom x +
                (tensorMap k R (tensorMul k R X)).hom y) :=
              congrArg (tensorMul k R X).hom
                ((tensorMap k R (tensorMul k R X)).hom.map_add x y)
          _ = (tensorMul k R X).hom
                ((tensorMap k R (tensorMul k R X)).hom x) +
              (tensorMul k R X).hom
                ((tensorMap k R (tensorMul k R X)).hom y) :=
            (tensorMul k R X).hom.map_add _ _
          _ = (tensorMul k R X).hom ((tensorMul k R TX).hom x) +
              (tensorMul k R X).hom ((tensorMul k R TX).hom y) :=
            congrArg₂ (· + ·) hx hy
          _ = (tensorMul k R X).hom
              ((tensorMul k R TX).hom x +
                (tensorMul k R TX).hom y) :=
            ((tensorMul k R X).hom.map_add _ _).symm
          _ = (tensorMul k R X).hom
              ((tensorMul k R TX).hom (x + y)) :=
            congrArg (tensorMul k R X).hom
              ((tensorMul k R TX).hom.map_add x y).symm
  left_unit X := by
    let TX := tensorObj k R X
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightSMul k R X
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightModule k R X
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
      tensorRightSMul k R TX
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
      tensorRightModule k R TX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change R ⊗[k] (underlying k R X).carrier at z
    change (tensorMul k R X).hom
      ((tensorUnit k R (tensorObj k R X)).hom z) = z
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
        let xX : X.carrier := show X.carrier from x
        let zX : TX.carrier :=
          show TX.carrier from
            r ⊗ₜ[k] (show (underlying k R X).carrier from xX)
        let rx : (underlying k R TX).carrier :=
          (tensorUnderlyingIso k R X).inv.hom
            (r ⊗ₜ[k] (show (underlying k R X).carrier from xX))
        have hrx : (show (underlying k R TX).carrier from zX) = rx := by
          change (r ⊗ₜ[k]
              (show (underlying k R X).carrier from xX)) =
            (tensorUnderlyingIso k R X).inv.hom
              (r ⊗ₜ[k]
                (show (underlying k R X).carrier from xX))
          rw [tensorUnderlyingIso_inv_apply]
        change (tensorMul k R X).hom
          ((tensorUnit k R TX).hom zX) = zX
        calc
          (tensorMul k R X).hom
              ((tensorUnit k R TX).hom zX) =
            (tensorMul k R X).hom
              (1 ⊗ₜ[k]
                (show (underlying k R TX).carrier from zX)) :=
              congrArg (tensorMul k R X).hom
                (tensorUnit_apply k R TX zX)
          _ = (tensorMul k R X).hom (1 ⊗ₜ[k] rx) :=
            congrArg (fun q =>
              (tensorMul k R X).hom (1 ⊗ₜ[k] q)) hrx
          _ = (1 * r) ⊗ₜ[k] xX :=
            tensorMul_tmul_via_underlyingIso k R X 1 r xX
          _ = zX := by
            dsimp only [zX]
            rw [one_mul]
    | add x y hx hy =>
        calc
          (tensorMul k R X).hom ((tensorUnit k R TX).hom (x + y)) =
            (tensorMul k R X).hom
              ((tensorUnit k R TX).hom x +
                (tensorUnit k R TX).hom y) :=
              congrArg (tensorMul k R X).hom
                ((tensorUnit k R TX).hom.map_add x y)
          _ = (tensorMul k R X).hom ((tensorUnit k R TX).hom x) +
              (tensorMul k R X).hom ((tensorUnit k R TX).hom y) :=
            (tensorMul k R X).hom.map_add _ _
          _ = x + y := congrArg₂ (· + ·) hx hy
  right_unit X := by
    let TX := tensorObj k R X
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightSMul k R X
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightModule k R X
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
      tensorRightSMul k R TX
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
      tensorRightModule k R TX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change R ⊗[k] (underlying k R X).carrier at z
    change (tensorMul k R X).hom
      ((tensorMap k R (tensorUnit k R X)).hom z) = z
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
        let xX : X.carrier := show X.carrier from x
        let zX : TX.carrier :=
          show TX.carrier from
            r ⊗ₜ[k] (show (underlying k R X).carrier from xX)
        let oneX : (underlying k R TX).carrier :=
          (tensorUnderlyingIso k R X).inv.hom
            (1 ⊗ₜ[k] (show (underlying k R X).carrier from xX))
        have hone :
            (show (underlying k R TX).carrier from
              (tensorUnit k R X).hom xX) = oneX := by
          change (tensorUnit k R X).hom xX =
            (tensorUnderlyingIso k R X).inv.hom
              (1 ⊗ₜ[k]
                (show (underlying k R X).carrier from xX))
          rw [tensorUnit_apply, tensorUnderlyingIso_inv_apply]
        have hmap :
            (tensorMap k R (tensorUnit k R X)).hom zX =
              (show (tensorObj k R TX).carrier from r ⊗ₜ[k] oneX) := by
          calc
            (tensorMap k R (tensorUnit k R X)).hom zX =
                r ⊗ₜ[k]
                  (show (underlying k R TX).carrier from
                    (tensorUnit k R X).hom xX) :=
              tensorMap_tmul k R (tensorUnit k R X) r xX
            _ = (show (tensorObj k R TX).carrier from
                r ⊗ₜ[k] oneX) :=
              congrArg (fun q : (underlying k R TX).carrier =>
                (show (tensorObj k R TX).carrier from r ⊗ₜ[k] q)) hone
        change (tensorMul k R X).hom
          ((tensorMap k R (tensorUnit k R X)).hom zX) = zX
        calc
          (tensorMul k R X).hom
              ((tensorMap k R (tensorUnit k R X)).hom zX) =
            (tensorMul k R X).hom
              (show (tensorObj k R TX).carrier from r ⊗ₜ[k] oneX) :=
              congrArg (tensorMul k R X).hom hmap
          _ = (r * 1) ⊗ₜ[k] xX :=
            tensorMul_tmul_via_underlyingIso k R X r 1 xX
          _ = zX := by
            dsimp only [zX]
            rw [mul_one]
    | add x y hx hy =>
        calc
          (tensorMul k R X).hom
              ((tensorMap k R (tensorUnit k R X)).hom (x + y)) =
            (tensorMul k R X).hom
              ((tensorMap k R (tensorUnit k R X)).hom x +
                (tensorMap k R (tensorUnit k R X)).hom y) :=
              congrArg (tensorMul k R X).hom
                ((tensorMap k R (tensorUnit k R X)).hom.map_add x y)
          _ = (tensorMul k R X).hom
                ((tensorMap k R (tensorUnit k R X)).hom x) +
              (tensorMul k R X).hom
                ((tensorMap k R (tensorUnit k R X)).hom y) :=
            (tensorMul k R X).hom.map_add _ _
          _ = x + y := congrArg₂ (· + ·) hx hy

/-- The forgetful functor from right `R`-modules to `k`-modules. -/
noncomputable abbrev forgetRight (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] : ModuleCat.{max u v w} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} k where
  obj := underlying k R
  map := rightUnderlyingMap k R
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private theorem forgetRight_eq_restrictScalars
    (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R] :
    (forgetRight k R : ModuleCat.{max u v w} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} k) =
      ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ) := rfl

/-- The right-module action `R ⊗ X ⟶ X`, `(r,x) ↦ x r`. -/
noncomputable def forgetAction (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) :
    (forgetRight k R).obj ((tensorMonad k R).obj X) ⟶
      (forgetRight k R).obj X :=
  (tensorUnderlyingIso k R X).hom ≫
    ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ k
      (fun (r : R) (x : (underlying k R X).carrier) =>
        (show (underlying k R X).carrier from
          (MulOpposite.op r : Rᵐᵒᵖ) • (show X.carrier from x)))
      (by
        intro r₁ r₂ x
        change (MulOpposite.op r₁ + MulOpposite.op r₂ : Rᵐᵒᵖ) •
            (show X.carrier from x) =
          MulOpposite.op r₁ • (show X.carrier from x) +
            MulOpposite.op r₂ • (show X.carrier from x)
        exact add_smul (MulOpposite.op r₁ : Rᵐᵒᵖ)
          (MulOpposite.op r₂ : Rᵐᵒᵖ) (show X.carrier from x))
      (by
        intro c r x
        change (MulOpposite.op (c • r) : Rᵐᵒᵖ) • (show X.carrier from x) =
          (MulOpposite.op (algebraMap k R c) : Rᵐᵒᵖ) •
            ((MulOpposite.op r : Rᵐᵒᵖ) • (show X.carrier from x))
        rw [Algebra.smul_def, MulOpposite.op_mul, mul_smul]
        exact ((underlyingSMulCommClass k R X).smul_comm c
          (MulOpposite.op r : Rᵐᵒᵖ) x).symm)
      (by
        intro r x y
        change (MulOpposite.op r : Rᵐᵒᵖ) •
            ((show X.carrier from x) + (show X.carrier from y)) =
          MulOpposite.op r • (show X.carrier from x) +
            MulOpposite.op r • (show X.carrier from y)
        exact smul_add (MulOpposite.op r : Rᵐᵒᵖ)
          (show X.carrier from x) (show X.carrier from y))
      (by
        intro c r x
        exact ((underlyingSMulCommClass k R X).smul_comm c
          (MulOpposite.op r : Rᵐᵒᵖ) x).symm)))

@[simp]
theorem forgetAction_tmul (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (r : R) (x : X.carrier) :
    (forgetAction k R X).hom (r ⊗ₜ[k] x) = (MulOpposite.op r) • x :=
  by
    change (forgetAction k R X).hom
      (r ⊗ₜ[k] (show (underlying k R X).carrier from x)) =
        (MulOpposite.op r) • x
    rfl

/-- The forgetful functor as a right module over the lifted tensor monad. -/
noncomputable def forgetRightModule (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] :
    CategoryTheory.Monad.RightModule (tensorMonad k R) (ModuleCat.{max u v w} k) :=
  CategoryTheory.Monad.RightModule.mk (forgetRight k R)
    { app := forgetAction k R
      naturality := by
        intro X Y f
        let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
          tensorRightSMul k R X
        let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
          tensorRightModule k R X
        let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
          tensorRightSMul k R Y
        let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R Y).carrier) :=
          tensorRightModule k R Y
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change R ⊗[k] (underlying k R X).carrier at z
        induction z using TensorProduct.inductionOn with
        | tmul r x =>
            let xX : X.carrier := show X.carrier from x
            let fx : Y.carrier := f.hom xX
            let zX : (tensorObj k R X).carrier :=
              show (tensorObj k R X).carrier from
                r ⊗ₜ[k] (show (underlying k R X).carrier from xX)
            let zY : (tensorObj k R Y).carrier :=
              show (tensorObj k R Y).carrier from
                r ⊗ₜ[k] (show (underlying k R Y).carrier from fx)
            change (forgetAction k R Y).hom
                ((tensorMap k R f).hom zX) =
              f.hom ((forgetAction k R X).hom zX)
            calc
              (forgetAction k R Y).hom ((tensorMap k R f).hom zX) =
                (forgetAction k R Y).hom zY :=
                  congrArg (forgetAction k R Y).hom
                    (tensorMap_tmul k R f r xX)
              _ = (MulOpposite.op r) • fx :=
                forgetAction_tmul k R Y r fx
              _ = f.hom ((MulOpposite.op r) • xX) :=
                (f.hom.map_smul (MulOpposite.op r) xX).symm
              _ = f.hom ((forgetAction k R X).hom zX) :=
                congrArg f.hom (forgetAction_tmul k R X r xX).symm
        | add x y hx hy =>
            calc
              (forgetAction k R Y).hom
                  ((tensorMap k R f).hom (x + y)) =
                (forgetAction k R Y).hom
                  ((tensorMap k R f).hom x +
                    (tensorMap k R f).hom y) :=
                  congrArg (forgetAction k R Y).hom
                    ((tensorMap k R f).hom.map_add x y)
              _ = (forgetAction k R Y).hom ((tensorMap k R f).hom x) +
                  (forgetAction k R Y).hom ((tensorMap k R f).hom y) :=
                (forgetAction k R Y).hom.map_add _ _
              _ = f.hom ((forgetAction k R X).hom x) +
                  f.hom ((forgetAction k R X).hom y) :=
                congrArg₂ (· + ·) hx hy
              _ = f.hom ((forgetAction k R X).hom x +
                  (forgetAction k R X).hom y) :=
                (f.hom.map_add _ _).symm
              _ = f.hom ((forgetAction k R X).hom (x + y)) :=
                congrArg f.hom ((forgetAction k R X).hom.map_add x y).symm }
    (fun X => by
      let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
        tensorRightSMul k R X
      let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
        tensorRightModule k R X
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (underlying k R X).carrier at x
      let xX : X.carrier := show X.carrier from x
      let zX : (tensorObj k R X).carrier :=
        show (tensorObj k R X).carrier from
          1 ⊗ₜ[k] (show (underlying k R X).carrier from xX)
      change (forgetAction k R X).hom ((tensorUnit k R X).hom xX) = xX
      calc
        (forgetAction k R X).hom ((tensorUnit k R X).hom xX) =
          (forgetAction k R X).hom zX :=
            congrArg (forgetAction k R X).hom (tensorUnit_apply k R X xX)
        _ = (MulOpposite.op (1 : R)) • xX :=
          forgetAction_tmul k R X 1 xX
        _ = xX := one_smul Rᵐᵒᵖ xX)
    (fun X => by
      let TX := tensorObj k R X
      let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
        tensorRightSMul k R X
      let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
        tensorRightModule k R X
      let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
        tensorRightSMul k R TX
      let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
        tensorRightModule k R TX
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change R ⊗[k] (underlying k R TX).carrier at z
      change (forgetAction k R X).hom ((tensorMul k R X).hom z) =
        (forgetAction k R X).hom ((forgetAction k R TX).hom z)
      induction z using TensorProduct.inductionOn with
      | tmul r y =>
          refine tensorUnderlying_induction k R X (fun y =>
            (forgetAction k R X).hom
                ((tensorMul k R X).hom (r ⊗ₜ[k] y)) =
              (forgetAction k R X).hom
                ((forgetAction k R TX).hom (r ⊗ₜ[k] y))) ?_ ?_ y
          · intro s x
            let xX : X.carrier := show X.carrier from x
            let sx : (underlying k R TX).carrier :=
              (tensorUnderlyingIso k R X).inv.hom
                (s ⊗ₜ[k] (show (underlying k R X).carrier from xX))
            let zX : (tensorObj k R TX).carrier := r ⊗ₜ[k] sx
            have hsmul :
                @SMul.smul Rᵐᵒᵖ TX.carrier
                    TX.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
                    (MulOpposite.op r) (show TX.carrier from sx) =
                  (show TX.carrier from
                    s ⊗ₜ[k]
                      (show (underlying k R X).carrier from
                        (MulOpposite.op r : Rᵐᵒᵖ) • xX)) := by
              change @SMul.smul Rᵐᵒᵖ
                    (R ⊗[k] (underlying k R X).carrier)
                    (tensorRightSMul k R X) (MulOpposite.op r)
                    (s ⊗ₜ[k]
                      (show (underlying k R X).carrier from xX)) =
                s ⊗ₜ[k]
                  (show (underlying k R X).carrier from
                    (MulOpposite.op r : Rᵐᵒᵖ) • xX)
              exact tensorRightModule_smul_tmul k R X
                (MulOpposite.op r) s
                  (show (underlying k R X).carrier from xX)
            change (forgetAction k R X).hom
                ((tensorMul k R X).hom zX) =
              (forgetAction k R X).hom ((forgetAction k R TX).hom zX)
            calc
              (forgetAction k R X).hom ((tensorMul k R X).hom zX) =
                (forgetAction k R X).hom
                  ((r * s) ⊗ₜ[k] xX) :=
                    congrArg (forgetAction k R X).hom
                      (tensorMul_tmul_via_underlyingIso k R X r s xX)
              _ = (MulOpposite.op (r * s) : Rᵐᵒᵖ) • xX :=
                forgetAction_tmul k R X (r * s) xX
              _ = (MulOpposite.op s : Rᵐᵒᵖ) •
                  ((MulOpposite.op r : Rᵐᵒᵖ) • xX) := by
                    rw [MulOpposite.op_mul, mul_smul]
              _ = (forgetAction k R X).hom
                  (s ⊗ₜ[k]
                    ((MulOpposite.op r : Rᵐᵒᵖ) • xX)) :=
                (forgetAction_tmul k R X s
                  ((MulOpposite.op r : Rᵐᵒᵖ) • xX)).symm
              _ = (forgetAction k R X).hom
                  (@SMul.smul Rᵐᵒᵖ TX.carrier
                    TX.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
                    (MulOpposite.op r) (show TX.carrier from sx)) :=
                congrArg (forgetAction k R X).hom hsmul.symm
              _ = (forgetAction k R X).hom
                  ((forgetAction k R TX).hom zX) :=
                congrArg (forgetAction k R X).hom
                  (forgetAction_tmul k R TX r
                    (show TX.carrier from sx)).symm
          · intro x y hx hy
            rw [TensorProduct.tmul_add]
            calc
              (forgetAction k R X).hom
                  ((tensorMul k R X).hom
                    ((r ⊗ₜ[k] x) + (r ⊗ₜ[k] y))) =
                (forgetAction k R X).hom
                  ((tensorMul k R X).hom (r ⊗ₜ[k] x) +
                    (tensorMul k R X).hom (r ⊗ₜ[k] y)) :=
                      congrArg (forgetAction k R X).hom
                        ((tensorMul k R X).hom.map_add _ _)
              _ = (forgetAction k R X).hom
                    ((tensorMul k R X).hom (r ⊗ₜ[k] x)) +
                  (forgetAction k R X).hom
                    ((tensorMul k R X).hom (r ⊗ₜ[k] y)) :=
                (forgetAction k R X).hom.map_add _ _
              _ = (forgetAction k R X).hom
                    ((forgetAction k R TX).hom (r ⊗ₜ[k] x)) +
                  (forgetAction k R X).hom
                    ((forgetAction k R TX).hom (r ⊗ₜ[k] y)) :=
                congrArg₂ (· + ·) hx hy
              _ = (forgetAction k R X).hom
                  ((forgetAction k R TX).hom (r ⊗ₜ[k] x) +
                    (forgetAction k R TX).hom (r ⊗ₜ[k] y)) :=
                ((forgetAction k R X).hom.map_add _ _).symm
              _ = (forgetAction k R X).hom
                  ((forgetAction k R TX).hom
                    ((r ⊗ₜ[k] x) + (r ⊗ₜ[k] y))) :=
                congrArg (forgetAction k R X).hom
                  ((forgetAction k R TX).hom.map_add _ _).symm
      | add x y hx hy =>
          calc
            (forgetAction k R X).hom
                ((tensorMul k R X).hom (x + y)) =
              (forgetAction k R X).hom
                ((tensorMul k R X).hom x + (tensorMul k R X).hom y) :=
                  congrArg (forgetAction k R X).hom
                    ((tensorMul k R X).hom.map_add x y)
            _ = (forgetAction k R X).hom ((tensorMul k R X).hom x) +
                (forgetAction k R X).hom ((tensorMul k R X).hom y) :=
              (forgetAction k R X).hom.map_add _ _
            _ = (forgetAction k R X).hom ((forgetAction k R TX).hom x) +
                (forgetAction k R X).hom ((forgetAction k R TX).hom y) :=
              congrArg₂ (· + ·) hx hy
            _ = (forgetAction k R X).hom
                ((forgetAction k R TX).hom x +
                  (forgetAction k R TX).hom y) :=
              ((forgetAction k R X).hom.map_add _ _).symm
            _ = (forgetAction k R X).hom
                ((forgetAction k R TX).hom (x + y)) :=
              congrArg (forgetAction k R X).hom
                ((forgetAction k R TX).hom.map_add x y).symm)

end ModuleCat.Algebra.Hochschild
