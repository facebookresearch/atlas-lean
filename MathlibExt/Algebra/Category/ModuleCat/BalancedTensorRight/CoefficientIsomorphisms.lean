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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.CoefficientMaps
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Isomorphism

/-!
# Bimodule coefficient isomorphisms on tensor and Tor

Let `B` and `B'` be `R`-left, `S`-right bimodules. An `R`-linear equivalence `e : B ≃ₗ[R] B'`
preserving the right `S`-action induces a natural isomorphism between the right-module-valued
tensor functors, with `[a ⊗ b] ↦ [a ⊗ e b]`.

The inverse equivalence also preserves the outer action. Assuming the right `R`-module
category has projective resolutions, left derivation gives the corresponding natural
isomorphism on Tor in every degree. The tensor and Tor isomorphisms preserve identity
equivalences and composition. The two ring universes are independent of the common
coefficient-carrier universe.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory MulOpposite

universe r s v

namespace ModuleCat.BalancedTensorRight

/-- Inverse of an equivariant equivalence is equivariant.

For types with actions of a type `T`, let `e : X ≃ Y` satisfy `e (t • x) = t • e x`. Then
`e.symm (t • y) = t • e.symm y` for all `t` and `y`, with independent action and carrier
universes. -/
theorem coefficientEquiv_symm_outer.{s₁, v₁, w₁}
    {T : Type s₁} {X : Type v₁} {Y : Type w₁} [SMul T X] [SMul T Y]
    (e : X ≃ Y) (hT : ∀ (t : T) (x : X), e (t • x) = t • e x)
    (t : T) (y : Y) : e.symm (t • y) = t • e.symm y := by
  apply e.injective
  rw [e.apply_symm_apply, hT, e.apply_symm_apply]

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (B B' : Type v) [AddCommGroup B] [AddCommGroup B']
  [Module R B] [Module R B'] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B] [SMulCommClass R Sᵐᵒᵖ B']
  (e : B ≃ₗ[R] B')
  (hS : ∀ (s : Sᵐᵒᵖ) (x : B), e (s • x) = s • e x)

/-- Bimodule equivalence gives a right-module tensor natural isomorphism.

An `R`-linear equivalence of coefficients preserving the right `S`-action induces
`tensorFunctor R S B ≅ tensorFunctor R S B'`. The inverse transformation is induced by the
inverse coefficient equivalence. -/
def tensorCoefficientIso : tensorFunctor R S B ≅ tensorFunctor R S B' where
  hom := tensorCoefficientTransformation R S B B' e.toLinearMap hS
  inv := tensorCoefficientTransformation R S B' B e.symm.toLinearMap
    (coefficientEquiv_symm_outer e.toEquiv hS)
  hom_inv_id := by
    apply NatTrans.ext
    funext A
    let := TensorProduct.Balanced.rightModule ℤ R S A B
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext ℤ R A B
    intro a b
    change (tensorCoefficientMap R S B' B e.symm.toLinearMap
        (coefficientEquiv_symm_outer e.toEquiv hS) A).hom
        ((tensorCoefficientMap R S B B' e.toLinearMap hS A).hom
          (TensorProduct.Balanced.mk ℤ R A B a b)) =
      TensorProduct.Balanced.mk ℤ R A B a b
    rw [tensorCoefficientMap_mk, tensorCoefficientMap_mk]
    exact congrArg (TensorProduct.Balanced.mk ℤ R A B a) (e.symm_apply_apply b)
  inv_hom_id := by
    apply NatTrans.ext
    funext A
    let := TensorProduct.Balanced.rightModule ℤ R S A B'
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext ℤ R A B'
    intro a b
    change (tensorCoefficientMap R S B B' e.toLinearMap hS A).hom
        ((tensorCoefficientMap R S B' B e.symm.toLinearMap
          (coefficientEquiv_symm_outer e.toEquiv hS) A).hom
          (TensorProduct.Balanced.mk ℤ R A B' a b)) =
      TensorProduct.Balanced.mk ℤ R A B' a b
    rw [tensorCoefficientMap_mk, tensorCoefficientMap_mk]
    exact congrArg (TensorProduct.Balanced.mk ℤ R A B' a) (e.apply_symm_apply b)

/-- Tensor coefficient isomorphism on pure classes.

At a right `R`-module `A`, the forward coefficient isomorphism sends `[x ⊗ y]` to `[x ⊗ e y]`. -/
theorem tensorCoefficientIso_hom_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (x : A) (y : B) :
    ((tensorCoefficientIso R S B B' e hS).hom.app A).hom
        (TensorProduct.Balanced.mk ℤ R A B x y) =
      TensorProduct.Balanced.mk ℤ R A B' x (e y) :=
  tensorCoefficientMap_mk R S B B' e.toLinearMap hS A x y

/-- Identity coefficient equivalence gives the identity tensor isomorphism.

The tensor natural isomorphism induced by `LinearEquiv.refl R B` is the identity isomorphism
of `tensorFunctor R S B`. -/
@[simp]
theorem tensorCoefficientIso_refl :
    tensorCoefficientIso R S B B (LinearEquiv.refl R B) (fun _ _ => rfl) =
      Iso.refl (tensorFunctor R S B) := by
  apply Iso.ext
  exact tensorCoefficientTransformation_id R S B

section Composition

variable (B'' : Type v) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
  [SMulCommClass R Sᵐᵒᵖ B''] (e' : B' ≃ₗ[R] B'')
  (hS' : ∀ (s : Sᵐᵒᵖ) (x : B'), e' (s • x) = s • e' x)

/-- Tensor coefficient isomorphisms preserve equivalence composition.

The tensor isomorphism for `e`, followed by that for `e'`, equals the tensor isomorphism
induced by `e.trans e'`, with its composite right-action compatibility. -/
theorem tensorCoefficientIso_trans :
    tensorCoefficientIso R S B B' e hS ≪≫ tensorCoefficientIso R S B' B'' e' hS' =
      tensorCoefficientIso R S B B'' (e.trans e')
        (fun s x => (congrArg e' (hS s x)).trans (hS' s (e x))) := by
  apply Iso.ext
  exact tensorCoefficientTransformation_comp R S B B' e.toLinearMap hS
    B'' e'.toLinearMap hS'

end Composition

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]

/-- Bimodule equivalence gives a right-module Tor natural isomorphism.

Assuming projective resolutions for right `R`-modules, left derive the tensor coefficient
isomorphism to obtain `torFunctor R S B n ≅ torFunctor R S B' n` for every natural `n`. -/
def torCoefficientIso (n : ℕ) : torFunctor R S B n ≅ torFunctor R S B' n :=
  NatIso.leftDerived (tensorCoefficientIso R S B B' e hS) n

/-- Forward coefficient Tor isomorphism is the derived coefficient map.

The forward map of the degree-`n` Tor coefficient isomorphism is
`torCoefficientTransformation` induced by `e.toLinearMap` and its outer-action compatibility. -/
@[simp]
theorem torCoefficientIso_hom (n : ℕ) :
    (torCoefficientIso R S B B' e hS n).hom =
      torCoefficientTransformation R S B B' e.toLinearMap hS n := rfl

/-- Inverse coefficient Tor isomorphism is induced by the inverse coefficient.

The inverse degree-`n` Tor map is the coefficient transformation induced by
`e.symm.toLinearMap`, using equivariance of the inverse. -/
@[simp]
theorem torCoefficientIso_inv (n : ℕ) :
    (torCoefficientIso R S B B' e hS n).inv =
      torCoefficientTransformation R S B' B e.symm.toLinearMap
        (coefficientEquiv_symm_outer e.toEquiv hS) n := rfl

/-- Identity coefficient equivalence gives the identity Tor isomorphism.

The degree-`n` Tor coefficient isomorphism for the reflexive coefficient equivalence is the
identity of `torFunctor R S B n`. -/
@[simp]
theorem torCoefficientIso_refl (n : ℕ) :
    torCoefficientIso R S B B (LinearEquiv.refl R B) (fun _ _ => rfl) n =
      Iso.refl (torFunctor R S B n) := by
  apply Iso.ext
  change torCoefficientTransformation R S B B (LinearMap.id : B →ₗ[R] B)
      (fun _ _ => rfl) n = 𝟙 (torFunctor R S B n)
  exact torCoefficientTransformation_id R S B n

section TorComposition

variable (B'' : Type v) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
  [SMulCommClass R Sᵐᵒᵖ B''] (e' : B' ≃ₗ[R] B'')
  (hS' : ∀ (s : Sᵐᵒᵖ) (x : B'), e' (s • x) = s • e' x)

/-- Tor coefficient isomorphisms preserve equivalence composition.

The degree-`n` Tor isomorphism for `e`, followed by that for `e'`, equals the Tor isomorphism
for the composite coefficient equivalence `e.trans e'`. -/
theorem torCoefficientIso_trans (n : ℕ) :
    torCoefficientIso R S B B' e hS n ≪≫ torCoefficientIso R S B' B'' e' hS' n =
      torCoefficientIso R S B B'' (e.trans e')
        (fun s x => (congrArg e' (hS s x)).trans (hS' s (e x))) n := by
  apply Iso.ext
  change torCoefficientTransformation R S B B' e.toLinearMap hS n ≫
      torCoefficientTransformation R S B' B'' e'.toLinearMap hS' n =
    torCoefficientTransformation R S B B'' (e'.toLinearMap.comp e.toLinearMap)
      (fun s x => (congrArg e' (hS s x)).trans (hS' s (e x))) n
  exact torCoefficientTransformation_comp R S B B' e.toLinearMap hS
    B'' e'.toLinearMap hS' n

end TorComposition
end ModuleCat.BalancedTensorRight

end
