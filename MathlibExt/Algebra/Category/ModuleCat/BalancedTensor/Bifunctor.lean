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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The actual two-variable balanced tensor functor

The object functors and right-module transformations are the existing
balanced tensor constructors. Both functor laws and additivity are proved
on their actual representatives. The acting ring need not be commutative.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite

namespace ModuleCat.BalancedTensor

universe u v

variable (R : Type u) [Ring R]

/-- The original balanced tensor, covariant in both the right and left module. -/
def bifunctor : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} R ⥤ ModuleCat.{v} ℤ where
  obj M := functor ℤ R M
  map f := ModuleCat.BalancedTensorRight.tensorTransformation f.hom
  map_id M := by
    apply NatTrans.ext
    funext N
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    apply ModuleCat.hom_ext
    apply TensorProduct.Balanced.hom_ext
    intro m n
    let h : M →ₗ[Rᵐᵒᵖ] M := ModuleCat.Hom.hom (𝟙 M : M ⟶ M)
    change (ModuleCat.BalancedTensorRight.tensorTransformationComponent h N).hom
      (TensorProduct.Balanced.mk ℤ R M N m n) = TensorProduct.Balanced.mk ℤ R M N m n
    simpa only [h, ModuleCat.hom_id, LinearMap.id_apply] using
      ModuleCat.BalancedTensorRight.tensorTransformationComponent_mk h N m n
  map_comp {M M' M''} f g := by
    apply NatTrans.ext
    funext N
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    apply ModuleCat.hom_ext
    apply TensorProduct.Balanced.hom_ext
    intro m n
    change (ModuleCat.BalancedTensorRight.tensorTransformationComponent (f ≫ g).hom N).hom
        (TensorProduct.Balanced.mk ℤ R M N m n) =
      (ModuleCat.BalancedTensorRight.tensorTransformationComponent g.hom N).hom
        ((ModuleCat.BalancedTensorRight.tensorTransformationComponent f.hom N).hom
          (TensorProduct.Balanced.mk ℤ R M N m n))
    rw [ModuleCat.BalancedTensorRight.tensorTransformationComponent_mk,
      ModuleCat.BalancedTensorRight.tensorTransformationComponent_mk,
      ModuleCat.BalancedTensorRight.tensorTransformationComponent_mk,
      ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The actual map in the right-module variable, on pure balanced representatives. -/
theorem bifunctor_map_mk {M M' : ModuleCat.{v} Rᵐᵒᵖ}
    (f : M ⟶ M') (N : ModuleCat.{v} R) (m : M) (n : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    (((bifunctor R).map f).app N).hom (TensorProduct.Balanced.mk ℤ R M N m n) =
      TensorProduct.Balanced.mk ℤ R M' N (f.hom m) n :=
  ModuleCat.BalancedTensorRight.tensorTransformationComponent_mk f.hom N m n

/-- Additivity in the first variable is earned by the original bilinear map. -/
instance bifunctor_additive :
    (bifunctor R : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} R ⥤ ModuleCat.{v} ℤ).Additive where
  map_add := by
    intro M M' f g
    apply NatTrans.ext
    funext N
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    apply ModuleCat.hom_ext
    apply TensorProduct.Balanced.hom_ext
    intro m n
    change (((bifunctor R).map (f + g)).app N).hom
        (TensorProduct.Balanced.mk ℤ R M N m n) =
      ((((bifunctor R).map f).app N).hom + (((bifunctor R).map g).app N).hom)
        (TensorProduct.Balanced.mk ℤ R M N m n)
    let A : ModuleCat.{v} ℤ := ((bifunctor R).obj M).obj N
    let B : ModuleCat.{v} ℤ := ((bifunctor R).obj M').obj N
    let z : A := TensorProduct.Balanced.mk ℤ R M N m n
    let a : B := TensorProduct.Balanced.mk ℤ R M' N (f.hom m) n
    let b : B := TensorProduct.Balanced.mk ℤ R M' N (g.hom m) n
    have hLeft : (((bifunctor R).map (f + g)).app N).hom z = a + b := by
      rw [bifunctor_map_mk, ModuleCat.hom_add, LinearMap.add_apply,
        map_add, LinearMap.add_apply]
      rfl
    have hRight :
        ((((bifunctor R).map f).app N).hom + (((bifunctor R).map g).app N).hom) z =
          a + b := by
      let F : A →ₗ[ℤ] B := (((bifunctor R).map f).app N).hom
      let G : A →ₗ[ℤ] B := (((bifunctor R).map g).app N).hom
      have hF : F z = a := bifunctor_map_mk R f N m n
      have hG : G z = b := bifunctor_map_mk R g N m n
      exact (LinearMap.add_apply F G z).trans (congrArg₂ (· + ·) hF hG)
    exact hLeft.trans hRight.symm

/-- Additivity in the left-module variable is the existing proved functor property. -/
instance bifunctor_obj_additive (M : ModuleCat.{v} Rᵐᵒᵖ) :
    ((bifunctor R).obj M).Additive := additive ℤ R M

/-- Forgetting the original ground module gives the actual abelian-group tensor bifunctor. -/
def groupBifunctor : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} R ⥤ AddCommGrpCat.{v} :=
  bifunctor R ⋙ (Functor.whiskeringRight (ModuleCat.{v} R) (ModuleCat.{v} ℤ)
    AddCommGrpCat.{v}).obj (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})

/-- Forgetting preserves the original first-variable tensor generator value. -/
theorem groupBifunctor_map_mk {M M' : ModuleCat.{v} Rᵐᵒᵖ}
    (f : M ⟶ M') (N : ModuleCat.{v} R) (m : M) (n : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    (((groupBifunctor R).map f).app N).hom (TensorProduct.Balanced.mk ℤ R M N m n) =
      TensorProduct.Balanced.mk ℤ R M' N (f.hom m) n := by
  let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  change (((bifunctor R).map f).app N).hom
    (TensorProduct.Balanced.mk ℤ R M N m n) = _
  exact bifunctor_map_mk R f N m n

/-- Forgetting preserves the original second-variable tensor generator value. -/
theorem groupBifunctor_obj_map_mk (M : ModuleCat.{v} Rᵐᵒᵖ)
    {N N' : ModuleCat.{v} R} (g : N ⟶ N') (m : M) (n : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    letI : Module ℤ N' := Module.compHom N' (algebraMap ℤ R)
    (((groupBifunctor R).obj M).map g).hom
        (TensorProduct.Balanced.mk ℤ R M N m n) =
      TensorProduct.Balanced.mk ℤ R M N' m (g.hom n) := by
  let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let : Module ℤ N' := Module.compHom N' (algebraMap ℤ R)
  change (ModuleCat.BalancedTensor.map ℤ R M g).hom
    (TensorProduct.Balanced.mk ℤ R M N m n) = _
  exact ModuleCat.BalancedTensor.map_mk ℤ R M g m n

instance groupBifunctor_additive :
    (groupBifunctor R : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} R ⥤ AddCommGrpCat.{v}).Additive := by
  change (bifunctor R ⋙ (Functor.whiskeringRight (ModuleCat.{v} R) (ModuleCat.{v} ℤ)
    AddCommGrpCat.{v}).obj (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})).Additive
  infer_instance

instance groupBifunctor_obj_additive (M : ModuleCat.{v} Rᵐᵒᵖ) :
    ((groupBifunctor R).obj M).Additive := by
  change ((bifunctor R).obj M ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).Additive
  infer_instance

end ModuleCat.BalancedTensor
