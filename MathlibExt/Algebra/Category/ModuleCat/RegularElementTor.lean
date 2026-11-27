/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.RegularElementResolution
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.Flat
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.LeftGroupAdjunction
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.DimensionShift
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
public import Mathlib.Algebra.Category.Grp.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Basic.UnivLE

/-!
# First Tor of a principal right quotient

Let R be an arbitrary ring and a a left-regular element. The projective
presentation R --a·→ R → R/aR identifies Tor₁ᴿ(R/aR,N) with the additive
group of n∈N satisfying a•n=0, for every left coefficient module N.

The regular balanced-tensor unitor carries the tensor of left multiplication
by a to the additive coefficient action of a. The connecting-map kernel
comparison therefore computes first Tor without a flatness or centrality
condition on N or on a. Independently sized coefficients are lifted to a
common carrier height with the regular right module.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

universe u v w t

namespace ModuleCat.RegularElement

variable (R : Type u) [Ring R]

/-- Taking unop coordinates identifies the lifted regular right carrier with
the additive group of R. -/
def rightRegularUnopEquiv : rightRegular.{u, v} R ≃+ R where
  toFun x := x.down.unop
  invFun r := ULift.up (MulOpposite.op r)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

section CommonCarrier

variable (N : ModuleCat.{max u v} R)

/-- Tensoring the regular right module with N recovers the underlying additive
group of N. A pure tensor x⊗n maps to unop(x)•n. -/
def regularTensorIso :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (rightRegular.{u, v} R)).obj N ≅
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).obj N := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let e : TensorProduct.Balanced ℤ R (rightRegular.{u, v} R) N ≃ₗ[ℤ]
      TensorProduct.Balanced ℤ R R N :=
    TensorProduct.Balanced.congr
      (rightRegularUnopEquiv.{u, v} R).toIntLinearEquiv (LinearEquiv.refl ℤ N)
      (by intro r x; rfl) (by intro r n; rfl)
  exact (forget₂ (ModuleCat.{max u v} ℤ) AddCommGrpCat.{max u v}).mapIso
    ((e.trans (TensorProduct.Balanced.leftUnitor ℤ R N)).toModuleIso)

/-- The regular tensor comparison has the prescribed pure-tensor coordinate. -/
theorem regularTensorIso_mk (x : rightRegular.{u, v} R) (n : N) :
    (regularTensorIso.{u, v} R N).hom.hom
        (ModuleCat.BalancedTensor.groupPure R (rightRegular.{u, v} R) N x n) =
      x.down.unop • n := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  change (TensorProduct.Balanced.leftUnitor ℤ R N)
    ((TensorProduct.Balanced.congr
      (rightRegularUnopEquiv.{u, v} R).toIntLinearEquiv (LinearEquiv.refl ℤ N)
      (by intro r x; rfl) (by intro r n; rfl))
        (TensorProduct.Balanced.mk ℤ R (rightRegular.{u, v} R) N x n)) = _
  rw [TensorProduct.Balanced.congr_mk, TensorProduct.Balanced.leftUnitor_mk]
  rfl

/-- Under the regular tensor comparison, the tensor of left multiplication
by a is the additive action n↦a•n on coefficients. -/
@[reassoc]
theorem regularTensorIso_leftMultiplication (a : R) :
    ((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).map
        (leftMultiplication.{u, v} R a) ≫ (regularTensorIso.{u, v} R N).hom =
      (regularTensorIso.{u, v} R N).hom ≫
        AddCommGrpCat.ofHom (coefficientAction R a N) := by
  letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  apply ModuleCat.BalancedTensor.groupHom_ext R (rightRegular.{u, v} R) N
    ((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).obj N)
  intro x n
  change (regularTensorIso.{u, v} R N).hom.hom
      ((((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).map
        (leftMultiplication.{u, v} R a)).hom
          (ModuleCat.BalancedTensor.groupPure R (rightRegular.{u, v} R) N x n)) =
    a • (regularTensorIso.{u, v} R N).hom.hom
      (ModuleCat.BalancedTensor.groupPure R (rightRegular.{u, v} R) N x n)
  rw [ModuleCat.BalancedTensor.groupBifunctor_map_mk, regularTensorIso_mk,
    regularTensorIso_mk, leftMultiplication_unop_apply]
  exact mul_smul a x.down.unop n

/-- The categorical kernel of the additive coefficient action is its concrete
annihilator additive group. -/
def coefficientKernelIso (a : R) :
    kernel (AddCommGrpCat.ofHom (coefficientAction R a N)) ≅ annihilatorGroup R a N :=
  limit.isoLimitCone
    ⟨AddCommGrpCat.kernelCone (AddCommGrpCat.ofHom (coefficientAction R a N)),
      AddCommGrpCat.kernelIsLimit (AddCommGrpCat.ofHom (coefficientAction R a N))⟩

/-- For a left-regular element a and arbitrary left coefficient N, first Tor
of the cyclic right quotient is the additive a-annihilator of N. -/
def quotientTorOneIso (a : R) (ha : IsLeftRegular a) :
    (((ModuleCat.BalancedTensor.torFirst R 1).obj (quotient.{u, v} R a)).obj N) ≅
      annihilatorGroup R a N := by
  let F : ModuleCat.{max u v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  letI : F.Additive :=
    Functor.LeftDerivedBalance.flippedObjAdditive
      (ModuleCat.BalancedTensor.groupBifunctor R) N
  let S : ShortComplex.ShortExactSequences (ModuleCat.{max u v} Rᵐᵒᵖ) :=
    ⟨sequence.{u, v} R a, sequence_shortExact.{u, v} R a ha⟩
  have h : IsZero ((F.leftDerived 1).obj S.obj.X₂) :=
    Functor.isZero_leftDerived_obj_projective_succ F 0 (rightRegular.{u, v} R)
  let e := regularTensorIso.{u, v} R N
  let k : kernel (F.map (leftMultiplication.{u, v} R a)) ≅
      kernel (AddCommGrpCat.ofHom (coefficientAction R a N)) :=
    kernel.mapIso _ _ e e (regularTensorIso_leftMultiplication.{u, v} R N a)
  exact F.leftDerivedOneIsoKernel S h ≪≫ k ≪≫ coefficientKernelIso.{u, v} R N a

end CommonCarrier

/-- Lift a left coefficient in universe w to T=max(u,w,t). The cyclic right
quotient at the same carrier height has first Tor equal to the a-annihilator
of that lifted coefficient. The ring and original coefficient universes are
independent. -/
def quotientTorOneIsoAt (a : R) (ha : IsLeftRegular a) (N : ModuleCat.{w} R) :
    let L := ModuleCat.uliftFunctor.{max u w t, w} R
    (((ModuleCat.BalancedTensor.torFirst R 1).obj
      (quotient.{u, max w t} R a)).obj (L.obj N)) ≅
        annihilatorGroup R a (L.obj N) :=
  quotientTorOneIso.{u, max w t} R
    ((ModuleCat.uliftFunctor.{max u w t, w} R).obj N) a ha

end ModuleCat.RegularElement
