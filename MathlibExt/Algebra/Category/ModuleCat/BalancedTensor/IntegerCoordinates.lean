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
# Integer coordinates for coefficient tensor objects

Let `M` be a right `R`-module and `N` a left `R`-module. The integer action obtained by
restricting the `R`-action on `N` agrees with the integer action of its additive group. The
integer-ground balanced tensor group therefore identifies with the additive group of the
coefficient-adjunction tensor object at the opposite integer outer ring.

The comparison preserves each pure class `[m ⊗ n]`. The double-opposite integer action on the
coefficient is transported along the ring equivalence `ℤ ≃+* ℤᵐᵒᵖᵐᵒᵖ`, with the module-carrier
universe independent of the ring universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite

namespace ModuleCat.BalancedTensor

universe u v

variable (R : Type u) [Ring R]

/-- Pure balanced class in opposite-integer coefficient coordinates.

For `m : M` and `n : N`, define `[m ⊗ n]` in the additive group underlying the coefficient
tensor object `BalancedTensorRight.tensorObj R ℤᵐᵒᵖ N M`, using the additive-group integer
action on `N`. -/
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

/-- Balanced tensor group as an opposite-integer coefficient tensor.

The group-valued balanced tensor of `M` and `N` is isomorphic to the additive group of
`BalancedTensorRight.tensorObj R ℤᵐᵒᵖ N M`. The coordinate uses equality of the two integer-
module structures on `N`. -/
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

/-- Integer tensor coordinate preserves pure representatives.

The forward map of `coefficientCoordinates R M N` sends the class `TensorProduct.Balanced.mk ℤ
R M N m n` to `coefficientMk R M N m n`. -/
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
