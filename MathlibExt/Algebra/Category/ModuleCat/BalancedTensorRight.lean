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
# Right-module balanced tensor–Hom adjunction

The coefficient B is an R-left/S-right bimodule. Tensor objects use the
integer-ground balanced quotient, and Hom objects use domain precomposition.
The target C needs no R-action. The linear maps have independent carrier
universes; the categorical adjunction uses a common carrier universe.
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

/-- The original balanced quotient bundled with the earned right S-action. -/
def tensorObj (A : ModuleCat.{v} Rᵐᵒᵖ) : ModuleCat.{v} Sᵐᵒᵖ :=
  letI : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  ModuleCat.of Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B)

/-- Actual first-factor morphisms act through the existing quotient map. -/
def tensorMap {A A' : ModuleCat.{v} Rᵐᵒᵖ} (f : A ⟶ A') :
    tensorObj R S B A ⟶ tensorObj R S B A' := by
  letI : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  letI : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A' B) := rightModule ℤ R S A' B
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.CoefficientHom.tensorMap
      (R := R) (S := S) (B := B) (A := A) (A' := A') f.hom)

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

/-- The actual tensor functor, with both functor laws proved on its maps. -/
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

/-- The actual coefficient-linear function space with native precomposition. -/
def homObj (C : ModuleCat.{v} Sᵐᵒᵖ) : ModuleCat.{v} Rᵐᵒᵖ :=
  letI : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  ModuleCat.of Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C)

/-- Evaluate the stored coefficient-linear map using its native function coercion. -/
instance homObjCoeFun (C : ModuleCat.{v} Sᵐᵒᵖ) :
    CoeFun (homObj R S B C) (fun _ => B → C) :=
  ⟨fun f => (show TensorProduct.Balanced.CoefficientHom.Hom S B C from f)⟩

/-- Postcomposition maps the actual Hom objects. -/
def homMap {C C' : ModuleCat.{v} Sᵐᵒᵖ} (g : C ⟶ C') :
    homObj R S B C ⟶ homObj R S B C' := by
  letI : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  letI : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C') :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C'
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.CoefficientHom.map R S B (C := C) (C' := C') g.hom)

@[simp]
theorem homObj_smul_apply (C : ModuleCat.{v} Sᵐᵒᵖ)
    (t : Rᵐᵒᵖ) (f : homObj R S B C) (b : B) :
    (t • f) b = f (t.unop • b) := by
  let : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  exact TensorProduct.Balanced.CoefficientHom.homModule_smul_apply R S B C t f b

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

/-- The coefficient-linear Hom functor, with actual postcomposition maps. -/
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

/-- Native categorical Hom bridges retain the additive raw correspondence. -/
def tensorHomEquiv (A : ModuleCat.{v} Rᵐᵒᵖ) (C : ModuleCat.{v} Sᵐᵒᵖ) :
    (tensorObj R S B A ⟶ C) ≃+ (A ⟶ homObj R S B C) := by
  letI : Module Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B) := rightModule ℤ R S A B
  letI : Module Rᵐᵒᵖ (TensorProduct.Balanced.CoefficientHom.Hom S B C) :=
    TensorProduct.Balanced.CoefficientHom.homModule R S B C
  exact (ModuleCat.homAddEquiv (M := tensorObj R S B A) (N := C)).trans
    ((TensorProduct.Balanced.CoefficientHom.tensorHomEquiv R S B A C).trans
      (ModuleCat.homAddEquiv (M := A) (N := homObj R S B C)).symm)

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

/-- Naturality in the original right R-module. -/
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

/-- Naturality in the coefficient target; C has no extra R-action. -/
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

/-- The actual underived tensor–Hom adjunction, with no comparison input. -/
def tensorAdjunction : tensorFunctor R S B ⊣ homFunctor R S B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A C => (tensorHomEquiv R S B A C).toEquiv
      homEquiv_naturality_left_symm := tensorHomEquiv_naturality_left_symm R S B
      homEquiv_naturality_right := tensorHomEquiv_naturality_right R S B }

instance tensorFunctor_isLeftAdjoint : (tensorFunctor R S B).IsLeftAdjoint :=
  ⟨homFunctor R S B, ⟨tensorAdjunction R S B⟩⟩


section AppendixTransformations

variable {R}
  {M M' : Type v} [AddCommGroup M] [AddCommGroup M']
  [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M']

/-- The literal tensor component of a right-module morphism, on the existing
native-restriction ground tensor functors. -/
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

/-- The actual transformation h⊗N, natural in every left R-module N. -/
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

/-- Precomposition by h is natural on the actual right-R-linear Hom groups.
The outer integer action is earned from the original additive structures. -/
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

/-- The source's additive Hom transformation, obtained by the native
forgetful functor, with no changed Hom carrier or supplied comparison. -/
def homAdditiveTransformation (h : M →ₗ[Rᵐᵒᵖ] M') :
    homFunctor ℤ R M' ⋙ forget₂ (ModuleCat.{v} ℤᵐᵒᵖ) AddCommGrpCat ⟶
      homFunctor ℤ R M ⋙ forget₂ (ModuleCat.{v} ℤᵐᵒᵖ) AddCommGrpCat :=
  Functor.whiskerRight (homTransformation h)
    (forget₂ (ModuleCat.{v} ℤᵐᵒᵖ) AddCommGrpCat)

@[simp, nolint simpNF] -- the `show` fixes the coercion target; dsimp drops it from the LHS
theorem homAdditiveTransformation_apply (h : M →ₗ[Rᵐᵒᵖ] M')
    (C : ModuleCat.{v} Rᵐᵒᵖ) (f : M' →ₗ[Rᵐᵒᵖ] C) (m : M) :
    (show M →ₗ[Rᵐᵒᵖ] C from
      ((homAdditiveTransformation h).app C).hom f) m = f (h m) := rfl

end AppendixTransformations

end ModuleCat.BalancedTensorRight
