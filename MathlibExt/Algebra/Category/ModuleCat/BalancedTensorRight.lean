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
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Hom

/-!
# Right-module-valued balanced tensor and Hom

Let `R` and `S` be associative rings and `B` an `R`-left, `S`-right bimodule with commuting
actions. For a right `R`-module `A`, the integer-ground balanced quotient `A ⊗_R B` has a
right `S`-action on the second factor. For a right `S`-module `C`, the group of `Sᵐᵒᵖ`-linear
maps `B → C` has a right `R`-action by precomposition, `(t • f)(b) = f(t.unop • b)`.

Balanced evaluation gives an additive equivalence `Hom_(Sᵐᵒᵖ)(A ⊗_R B, C) ≃ Hom_(Rᵐᵒᵖ)(A,
Hom_(Sᵐᵒᵖ)(B, C))`, natural in both module variables. It defines the tensor–Hom adjunction.
The coefficient, source, and target carriers here share universe `v`, independently of the two
ring universes.

Maps of right-module coefficients also give covariant transformations of integer-valued tensor
functors and contravariant precomposition transformations of their Hom functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite

universe r s v

namespace ModuleCat.BalancedTensorRight

open TensorProduct.Balanced
variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

/-- Balanced tensor object with its right S action.

For a right `R`-module `A`, bundle `Balanced ℤ R A B` as a right `S`-module using the action
induced from the right `S`-action on `B`. -/
def tensorObj (A : ModuleCat.{v} Rᵐᵒᵖ) : ModuleCat.{v} Sᵐᵒᵖ :=
  letI : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  ModuleCat.of Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B)

/-- Right-module map on the first balanced tensor factor.

A right `R`-module morphism `f : A ⟶ A'` induces a right `S`-module morphism `A ⊗_R B ⟶ A' ⊗_R
B`. -/
def tensorMap {A A' : ModuleCat.{v} Rᵐᵒᵖ} (f : A ⟶ A') :
    tensorObj R S B A ⟶ tensorObj R S B A' := by
  letI : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  letI : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A' B) := rightModule ℤ R S A' B
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.CoefficientHom.tensorMap
      (R := R) (S := S) (B := B) (A := A) (A' := A') f.hom)

/-- Right-module tensor map on pure balanced classes.

The map induced by `f : A ⟶ A'` sends `[a ⊗ b]` to `[f a ⊗ b]`. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem tensorMap_mk {A A' : ModuleCat.{v} Rᵐᵒᵖ} (f : A ⟶ A') (a : A) (b : B) :
    (tensorMap R S B f).hom (mk ℤ R A B a b) =
      mk ℤ R A' B (f.hom a) b := by
  let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A' B) := rightModule ℤ R S A' B
  change TensorProduct.Balanced.CoefficientHom.tensorMap
    (R := R) (S := S) (B := B) (A := A) (A' := A') f.hom (mk ℤ R A B a b) = _
  exact TensorProduct.Balanced.CoefficientHom.tensorMap_mk
    (R := R) (S := S) (B := B) (A := A) (A' := A') f.hom a b

/-- Tensor by a bimodule as a right-module-valued functor.

The bimodule `B` defines a functor `ModuleCat Rᵐᵒᵖ ⥤ ModuleCat Sᵐᵒᵖ`, taking `A` to `A ⊗_R B`
and acting on the first tensor factor. -/
def tensorFunctor : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} Sᵐᵒᵖ where
  obj := tensorObj R S B
  map := tensorMap R S B
  map_id A := by
    let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
    apply ModuleCat.hom_ext
    change TensorProduct.Balanced.CoefficientHom.tensorMap
      (R := R) (S := S) (B := B) (A := A) (A' := A) (𝟙 A : A ⟶ A).hom = LinearMap.id
    rw [ModuleCat.hom_id]
    exact TensorProduct.Balanced.CoefficientHom.tensorMap_id
      (R := R) (S := S) (B := B) (A := A)
  map_comp {A A' A''} f g := by
    let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
    let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A' B) := rightModule ℤ R S A' B
    let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A'' B) := rightModule ℤ R S A'' B
    apply ModuleCat.hom_ext
    change TensorProduct.Balanced.CoefficientHom.tensorMap
      (R := R) (S := S) (B := B) (A := A) (A' := A'') (f ≫ g).hom =
      (TensorProduct.Balanced.CoefficientHom.tensorMap
        (R := R) (S := S) (B := B) (A := A') (A' := A'') g.hom).comp
        (TensorProduct.Balanced.CoefficientHom.tensorMap
          (R := R) (S := S) (B := B) (A := A) (A' := A') f.hom)
    rw [ModuleCat.hom_comp]
    exact TensorProduct.Balanced.CoefficientHom.tensorMap_comp
      (R := R) (S := S) (B := B) (A := A) (A' := A') (A'' := A'') f.hom g.hom

/-- Right-module-valued tensor functor is additive.

The functor `A ↦ A ⊗_R B` preserves sums of right `R`-module morphisms. -/
instance tensorFunctor_additive : (tensorFunctor R S B).Additive where
  map_add {A A' f g} := by
    let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
    let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A' B) := rightModule ℤ R S A' B
    apply ModuleCat.hom_ext
    change TensorProduct.Balanced.CoefficientHom.tensorMap
      (R := R) (S := S) (B := B) (A := A) (A' := A') (f + g).hom =
      TensorProduct.Balanced.CoefficientHom.tensorMap
        (R := R) (S := S) (B := B) (A := A) (A' := A') f.hom +
      TensorProduct.Balanced.CoefficientHom.tensorMap
        (R := R) (S := S) (B := B) (A := A) (A' := A') g.hom
    rw [ModuleCat.hom_add]
    exact TensorProduct.Balanced.CoefficientHom.tensorMap_add
      (R := R) (S := S) (B := B) (A := A) (A' := A') f.hom g.hom

/-- Right R module of S-linear coefficient maps.

For a right `S`-module `C`, bundle the `Sᵐᵒᵖ`-linear maps `B → C` with the right `R`-action
given by precomposition with the left action on `B`. -/
def homObj (C : ModuleCat.{v} Sᵐᵒᵖ) : ModuleCat.{v} Rᵐᵒᵖ :=
  letI : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  ModuleCat.of Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C)

/-- Coefficient Hom elements evaluate as functions.

Elements of `homObj R S B C` are regarded as functions from the coefficient module `B` to the
right `S`-module `C`. -/
instance homObjCoeFun (C : ModuleCat.{v} Sᵐᵒᵖ) :
    CoeFun (homObj R S B C) (fun _ => B → C) :=
  ⟨fun f => (show TensorProduct.Balanced.CoefficientHom.Hom S B C from f)⟩

/-- Target postcomposition on the right-module Hom object.

A right `S`-module morphism `g : C ⟶ C'` induces a right `R`-module morphism from
`Hom_(Sᵐᵒᵖ)(B, C)` to `Hom_(Sᵐᵒᵖ)(B, C')` by postcomposition. -/
def homMap {C C' : ModuleCat.{v} Sᵐᵒᵖ} (g : C ⟶ C') :
    homObj R S B C ⟶ homObj R S B C' := by
  letI : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  letI : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C') :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C'
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.CoefficientHom.map R S B (C := C) (C' := C') g.hom)

/-- Right R action on coefficient Hom is domain precomposition.

For `t : Rᵐᵒᵖ`, a coefficient Hom element `f`, and `b : B`, the scalar action satisfies `(t •
f)(b) = f(t.unop • b)`. -/
@[simp]
theorem homObj_smul_apply (C : ModuleCat.{v} Sᵐᵒᵖ)
    (t : Rᵐᵒᵖ) (f : homObj R S B C) (b : B) :
    (t • f) b = f (t.unop • b) := by
  let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  exact TensorProduct.Balanced.CoefficientHom.homModule_smul_apply R S B C t f b

/-- Target Hom map evaluates by postcomposition.

For `g : C ⟶ C'`, an element `f` of the coefficient Hom object, and `b : B`, the image
evaluates as `g(f b)`. -/
@[simp]
theorem homMap_apply {C C' : ModuleCat.{v} Sᵐᵒᵖ}
    (g : C ⟶ C') (f : homObj R S B C) (b : B) :
    (homMap R S B g).hom f b = g.hom (f b) := by
  let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C') :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C'
  change TensorProduct.Balanced.CoefficientHom.map R S B (C := C) (C' := C') g.hom f b = _
  exact LinearMap.congr_fun
    (TensorProduct.Balanced.CoefficientHom.map_apply R S B (C := C) (C' := C') g.hom f) b

/-- Coefficient Hom as a right-module-valued functor.

The functor `ModuleCat Sᵐᵒᵖ ⥤ ModuleCat Rᵐᵒᵖ` takes `C` to the right `R`-module of
`Sᵐᵒᵖ`-linear maps `B → C` and sends target maps to postcomposition. -/
abbrev homFunctor : ModuleCat.{v} Sᵐᵒᵖ ⥤ ModuleCat.{v} Rᵐᵒᵖ where
  obj := homObj R S B
  map := homMap R S B
  map_id C := by
    let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
      TensorProduct.Balanced.CoefficientHom.homModule R S B C
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro b
    change (𝟙 C : C ⟶ C).hom (f b) = f b
    rfl
  map_comp {C C' C''} f g := by
    let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
      TensorProduct.Balanced.CoefficientHom.homModule R S B C
    let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C') :=
      TensorProduct.Balanced.CoefficientHom.homModule R S B C'
    let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C'') :=
      TensorProduct.Balanced.CoefficientHom.homModule R S B C''
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply LinearMap.ext
    intro b
    change (f ≫ g).hom (h b) = g.hom (f.hom (h b))
    rfl

/-- Right-module-valued Hom functor is additive.

The coefficient Hom functor preserves addition of right `S`-module morphisms. -/
instance homFunctor_additive : (homFunctor R S B).Additive where
  map_add {C C' f g} := by
    let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
      TensorProduct.Balanced.CoefficientHom.homModule R S B C
    let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C') :=
      TensorProduct.Balanced.CoefficientHom.homModule R S B C'
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply LinearMap.ext
    intro b
    change (f + g).hom (h b) = f.hom (h b) + g.hom (h b)
    simp only [ModuleCat.hom_add, LinearMap.add_apply]

/-- Additive Hom equivalence for the bimodule tensor adjunction.

Right `S`-linear maps from `A ⊗_R B` to `C` are additively equivalent to right `R`-linear maps
from `A` to the right `R`-module of `S`-linear maps `B → C`. -/
def tensorHomEquiv (A : ModuleCat.{v} Rᵐᵒᵖ) (C : ModuleCat.{v} Sᵐᵒᵖ) :
    (tensorObj R S B A ⟶ C) ≃+ (A ⟶ homObj R S B C) := by
  letI : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  letI : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  exact (ModuleCat.homAddEquiv (M := tensorObj R S B A) (N := C)).trans
    ((TensorProduct.Balanced.CoefficientHom.tensorHomEquiv R S B A C).trans
      (ModuleCat.homAddEquiv (M := A) (N := homObj R S B C)).symm)

/-- Bimodule tensor currying on elements.

The curried map of `f : A ⊗_R B ⟶ C`, evaluated at `a` and then at `b`, equals `f([a ⊗ b])`. -/
@[simp]
theorem tensorHomEquiv_apply (A : ModuleCat.{v} Rᵐᵒᵖ)
    (C : ModuleCat.{v} Sᵐᵒᵖ) (f : tensorObj R S B A ⟶ C) (a : A) (b : B) :
    (tensorHomEquiv R S B A C f).hom a b = f.hom (mk ℤ R A B a b) := by
  let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  change TensorProduct.Balanced.CoefficientHom.tensorHomEquiv R S B A C f.hom a b = _
  exact TensorProduct.Balanced.CoefficientHom.tensorHomEquiv_apply
    (R := R) (S := S) (B := B) (A := A) (C := C) f.hom a b

/-- Bimodule tensor uncurrying on pure classes.

The tensor map obtained by uncurrying `g : A ⟶ homObj R S B C` sends `[a ⊗ b]` to `(g a)(b)`. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem tensorHomEquiv_symm_mk (A : ModuleCat.{v} Rᵐᵒᵖ)
    (C : ModuleCat.{v} Sᵐᵒᵖ) (g : A ⟶ homObj R S B C) (a : A) (b : B) :
    ((tensorHomEquiv R S B A C).symm g).hom (mk ℤ R A B a b) = g.hom a b := by
  let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  change (TensorProduct.Balanced.CoefficientHom.tensorHomEquiv R S B A C).symm g.hom
    (mk ℤ R A B a b) = _
  exact TensorProduct.Balanced.CoefficientHom.tensorHomEquiv_symm_mk
    (R := R) (S := S) (B := B) (A := A) (C := C) g.hom a b

/-- Uncurrying commutes with precomposition in the source module.

For `f : A' ⟶ A` and `g : A ⟶ homObj R S B C`, uncurrying `f ≫ g` equals the tensor image of
`f` followed by the uncurried map of `g`. -/
theorem tensorHomEquiv_naturality_left_symm {A A' : ModuleCat.{v} Rᵐᵒᵖ}
    {C : ModuleCat.{v} Sᵐᵒᵖ} (f : A' ⟶ A) (g : A ⟶ homObj R S B C) :
    (tensorHomEquiv R S B A' C).symm (f ≫ g) =
      (tensorFunctor R S B).map f ≫ (tensorHomEquiv R S B A C).symm g := by
  let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A' B) := rightModule ℤ R S A' B
  let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  apply ModuleCat.hom_ext
  change (TensorProduct.Balanced.CoefficientHom.tensorHomEquiv R S B A' C).symm (g.hom.comp f.hom) =
    ((TensorProduct.Balanced.CoefficientHom.tensorHomEquiv R S B A C).symm g.hom).comp
      (TensorProduct.Balanced.CoefficientHom.tensorMap
        (R := R) (S := S) (B := B) (A := A') (A' := A) f.hom)
  exact TensorProduct.Balanced.CoefficientHom.tensorHomEquiv_naturality_left_symm
    (R := R) (S := S) (B := B) (A := A) (A' := A') (C := C) f.hom g.hom

/-- Currying commutes with postcomposition in the target module.

For `f : A ⊗_R B ⟶ C` and `g : C ⟶ C'`, currying `f ≫ g` equals the curried map of `f`
followed by the Hom functor's image of `g`. -/
theorem tensorHomEquiv_naturality_right {A : ModuleCat.{v} Rᵐᵒᵖ}
    {C C' : ModuleCat.{v} Sᵐᵒᵖ} (f : tensorObj R S B A ⟶ C) (g : C ⟶ C') :
    tensorHomEquiv R S B A C' (f ≫ g) =
      tensorHomEquiv R S B A C f ≫ (homFunctor R S B).map g := by
  let : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C') :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C'
  apply ModuleCat.hom_ext
  change TensorProduct.Balanced.CoefficientHom.tensorHomEquiv R S B A C' (g.hom.comp f.hom) =
    (TensorProduct.Balanced.CoefficientHom.map R S B (C := C) (C' := C') g.hom).comp
      (TensorProduct.Balanced.CoefficientHom.tensorHomEquiv R S B A C f.hom)
  exact TensorProduct.Balanced.CoefficientHom.tensorHomEquiv_naturality_right
    (R := R) (S := S) (B := B) (A := A) (C := C) (C' := C') f.hom g.hom

/-- Right-module bimodule tensor is left adjoint to coefficient Hom.

The natural additive tensor–Hom equivalence gives `tensorFunctor R S B ⊣ homFunctor R S B`. -/
def tensorAdjunction : tensorFunctor R S B ⊣ homFunctor R S B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A C => (tensorHomEquiv R S B A C).toEquiv
      homEquiv_naturality_left_symm := tensorHomEquiv_naturality_left_symm R S B
      homEquiv_naturality_right := tensorHomEquiv_naturality_right R S B }

/-- Right-module-valued tensor is a left adjoint.

The right-module tensor functor has right adjoint `homFunctor R S B`. -/
instance tensorFunctor_isLeftAdjoint : (tensorFunctor R S B).IsLeftAdjoint :=
  ⟨homFunctor R S B, ⟨tensorAdjunction R S B⟩⟩


section AppendixTransformations

variable {R}
  {M M' : Type v} [AddCommGroup M] [AddCommGroup M']
  [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M']

/-- Right coefficient morphism on an integer-valued tensor object.

A right `R`-linear map `h : M → M'` induces a morphism from the integer-module balanced tensor
of `M` and `N` to that of `M'` and `N`. -/
def tensorTransformationComponent (h : M →ₗ[Rᵐᵒᵖ] M') (N : ModuleCat.{v} R) :
    ModuleCat.BalancedTensor.obj ℤ R M N ⟶
      ModuleCat.BalancedTensor.obj ℤ R M' N := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let f₀ : M →ₗ[ℤ] M' := h.toAddMonoidHom.toIntLinearMap
  have hf : ∀ (r : R) (m : M), f₀ (op r • m) = op r • f₀ m := by
    intro r m
    change h (op r • m) = op r • h m
    simpa only [RingHom.id_apply] using h.map_smul (op r) m
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.map
      (k := ℤ) (R := R) (M := M) (N := N) (M' := M') (N' := N)
      f₀ (LinearMap.id : N →ₗ[ℤ] N) hf (fun _ _ => rfl))

/-- Integer-valued coefficient component on pure classes.

The tensor component induced by `h : M →ₗ[Rᵐᵒᵖ] M'` sends `[m ⊗ n]` to `[h m ⊗ n]`. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem tensorTransformationComponent_mk (h : M →ₗ[Rᵐᵒᵖ] M')
    (N : ModuleCat.{v} R) (m : M) (n : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    (tensorTransformationComponent h N).hom (mk ℤ R M N m n) =
      mk ℤ R M' N (h m) n := by
  let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let f₀ : M →ₗ[ℤ] M' := h.toAddMonoidHom.toIntLinearMap
  have hf : ∀ (r : R) (m : M), f₀ (op r • m) = op r • f₀ m := by
    intro r m
    change h (op r • m) = op r • h m
    simpa only [RingHom.id_apply] using h.map_smul (op r) m
  change TensorProduct.Balanced.map
    (k := ℤ) (R := R) (M := M) (N := N) (M' := M') (N' := N)
    f₀ (LinearMap.id : N →ₗ[ℤ] N) hf (fun _ _ => rfl) (mk ℤ R M N m n) = _
  exact TensorProduct.Balanced.map_mk
    (k := ℤ) (R := R) (M := M) (N := N) (M' := M') (N' := N)
    f₀ (LinearMap.id : N →ₗ[ℤ] N) hf (fun _ _ => rfl) m n

/-- Right coefficient morphism gives an integer-valued tensor transformation.

A right `R`-linear coefficient map `h : M → M'` induces a natural transformation between the
balanced tensor functors with coefficients `M` and `M'`, valued in integer modules. -/
def tensorTransformation (h : M →ₗ[Rᵐᵒᵖ] M') :
    ModuleCat.BalancedTensor.functor ℤ R M ⟶
      ModuleCat.BalancedTensor.functor ℤ R M' where
  app := tensorTransformationComponent h
  naturality {N N'} g := by
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    let : Module ℤ N' := Module.compHom N' (algebraMap ℤ R)
    apply ModuleCat.hom_ext
    apply TensorProduct.Balanced.hom_ext
    intro m n
    change (tensorTransformationComponent h N').hom
        ((ModuleCat.BalancedTensor.map ℤ R M g).hom (mk ℤ R M N m n)) =
      (ModuleCat.BalancedTensor.map ℤ R M' g).hom
        ((tensorTransformationComponent h N).hom (mk ℤ R M N m n))
    rw [ModuleCat.BalancedTensor.map_mk, tensorTransformationComponent_mk,
      tensorTransformationComponent_mk, ModuleCat.BalancedTensor.map_mk]

/-- Right coefficient morphism gives contravariant Hom precomposition.

A right `R`-linear map `h : M → M'` induces a natural transformation from the Hom functor with
domain coefficient `M'` to the Hom functor with domain coefficient `M`, by precomposition. -/
def homTransformation (h : M →ₗ[Rᵐᵒᵖ] M') :
    homFunctor ℤ R M' ⟶ homFunctor ℤ R M where
  app C := by
    letI : Module ℤᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom R M' C) :=
      TensorProduct.Balanced.CoefficientHom.homModule ℤ R M' C
    letI : Module ℤᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom R M C) :=
      TensorProduct.Balanced.CoefficientHom.homModule ℤ R M C
    exact ModuleCat.ofHom
      (TensorProduct.Balanced.CoefficientHom.precomp
        (R := ℤ) (S := R) (B := M) (B' := M') (C := C) h (fun z m => by
          simpa only [Int.cast_id] using map_intCast_smul h ℤ ℤ z m))
  naturality {C C'} f := by
    let : Module ℤᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom R M' C) :=
      TensorProduct.Balanced.CoefficientHom.homModule ℤ R M' C
    let : Module ℤᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom R M C) :=
      TensorProduct.Balanced.CoefficientHom.homModule ℤ R M C
    let : Module ℤᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom R M' C') :=
      TensorProduct.Balanced.CoefficientHom.homModule ℤ R M' C'
    let : Module ℤᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom R M C') :=
      TensorProduct.Balanced.CoefficientHom.homModule ℤ R M C'
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro m
    change f.hom (g (h m)) = f.hom (g (h m))
    rfl

/-- Coefficient Hom precomposition after forgetting integer scalars.

Forget the integer-opposite module structure of the coefficient Hom precomposition
transformation to obtain a natural transformation valued in additive groups. -/
def homAdditiveTransformation (h : M →ₗ[Rᵐᵒᵖ] M') :
    homFunctor ℤ R M' ⋙ forget₂ (ModuleCat.{v} ℤᵐᵒᵖ) AddCommGrpCat ⟶
      homFunctor ℤ R M ⋙ forget₂ (ModuleCat.{v} ℤᵐᵒᵖ) AddCommGrpCat :=
  Functor.whiskerRight (homTransformation h)
    (forget₂ (ModuleCat.{v} ℤᵐᵒᵖ) AddCommGrpCat)

/-- Additive coefficient precomposition evaluates as function composition.

For a right `R`-linear map `h : M → M'` and an `Rᵐᵒᵖ`-linear map `f : M' → C`, the additive
Hom transformation sends `f` to the function `m ↦ f(h m)`. -/
@[simp, nolint simpNF] -- the `show` fixes the coercion target; dsimp drops it from the LHS
theorem homAdditiveTransformation_apply (h : M →ₗ[Rᵐᵒᵖ] M')
    (C : ModuleCat.{v} Rᵐᵒᵖ) (f : M' →ₗ[Rᵐᵒᵖ] C) (m : M) :
    (show M →ₗ[Rᵐᵒᵖ] C from
      ((homAdditiveTransformation h).app C).hom f) m = f (h m) := rfl

end AppendixTransformations

end ModuleCat.BalancedTensorRight
