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

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Ring.Equiv
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.Bifunctor

/-!
# Integer coordinates for the two existing balanced tensor constructors

The left-module tensor functor uses restriction of scalars from R. The
coefficient adjunction uses the canonical integer action of the same group.
Integer modules on an additive commutative group are unique. The resulting
native coordinate Iso retains both original constructors and every pure class.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite

namespace ModuleCat.BalancedTensor

universe u v

variable (R : Type u) [Ring R]

/-- The pure class in the existing coefficient-adjunction tensor object. -/
def coefficientMk (M : ModuleCat.{v} Rᵐᵒᵖ) (N : ModuleCat.{v} R) (m : M) (n : N) :
    letI : Module ℤ N := AddCommGroup.toIntModule N
    letI : Module ℤᵐᵒᵖᵐᵒᵖ N :=
      Module.compHom N (RingEquiv.opOp ℤ).symm.toRingHom
    letI : SMulCommClass R ℤᵐᵒᵖᵐᵒᵖ N := by
      refine ⟨?_⟩
      intro r z x
      change r • (z.unop.unop • x) = z.unop.unop • (r • x)
      exact map_zsmul (DistribSMul.toAddMonoidHom N r) z.unop.unop x
    (forget₂ (ModuleCat.{v} ℤᵐᵒᵖᵐᵒᵖ) AddCommGrpCat.{v}).obj
      (ModuleCat.BalancedTensorRight.tensorObj R ℤᵐᵒᵖ N M) := by
  letI : Module ℤ N := AddCommGroup.toIntModule N
  exact TensorProduct.Balanced.mk ℤ R M N m n

/-- The actual integer-action identification between the two original tensor objects. -/
def coefficientCoordinates (M : ModuleCat.{v} Rᵐᵒᵖ) (N : ModuleCat.{v} R) :
    ((groupBifunctor R).obj M).obj N ≅
      letI : Module ℤ N := AddCommGroup.toIntModule N
      letI : Module ℤᵐᵒᵖᵐᵒᵖ N :=
        Module.compHom N (RingEquiv.opOp ℤ).symm.toRingHom
      letI : SMulCommClass R ℤᵐᵒᵖᵐᵒᵖ N := by
        refine ⟨?_⟩
        intro r z x
        change r • (z.unop.unop • x) = z.unop.unop • (r • x)
        exact map_zsmul (DistribSMul.toAddMonoidHom N r) z.unop.unop x
      (forget₂ (ModuleCat.{v} ℤᵐᵒᵖᵐᵒᵖ) AddCommGrpCat.{v}).obj
        (ModuleCat.BalancedTensorRight.tensorObj R ℤᵐᵒᵖ N M) := by
  let d : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let d₀ : Module ℤ N := AddCommGroup.toIntModule N
  let K : Module ℤ N → AddCommGrpCat.{v} := fun d' =>
    letI := d'
    AddCommGrpCat.of (TensorProduct.Balanced ℤ R M N)
  exact eqToIso (congrArg K (Subsingleton.elim d d₀))

/-- The earned coordinate map is the identity on actual pure representatives. -/
theorem coefficientCoordinates_mk (M : ModuleCat.{v} Rᵐᵒᵖ) (N : ModuleCat.{v} R)
    (m : M) (n : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    (coefficientCoordinates R M N).hom.hom (TensorProduct.Balanced.mk ℤ R M N m n) =
      coefficientMk R M N m n := by
  let d : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let d₀ : Module ℤ N := AddCommGroup.toIntModule N
  let K : Module ℤ N → AddCommGrpCat.{v} := fun d' =>
    letI := d'
    AddCommGrpCat.of (TensorProduct.Balanced ℤ R M N)
  let z : ∀ d' : Module ℤ N, K d' := fun d' =>
    letI := d'
    TensorProduct.Balanced.mk ℤ R M N m n
  have hz (d₁ d₂ : Module ℤ N) (h : d₁ = d₂) :
      (eqToIso (congrArg K h)).hom.hom (z d₁) = z d₂ := by
    cases h
    rfl
  exact hz d d₀ (Subsingleton.elim d d₀)

end ModuleCat.BalancedTensor
