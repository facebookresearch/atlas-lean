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
# Actual enriched tensor and Tor isomorphisms of original coefficients

An original R-linear coefficient equivalence commuting with the outer
right action induces an isomorphism on the existing tensor and native Tor
models. Outer linearity of its inverse is earned from the original forward
linearity. The scalar rings have independent universes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory MulOpposite

universe r s v

namespace ModuleCat.BalancedTensorRight

/-- The inverse of an equivariant equivalence retains its original scalar action.
Only the two scalar actions and forward equivariance are needed. -/
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

/-- The original coefficient equivalence gives the actual enriched tensor isomorphism. -/
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

/-- The tensor comparison retains the actual original coefficient representative. -/
theorem tensorCoefficientIso_hom_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (x : A) (y : B) :
    ((tensorCoefficientIso R S B B' e hS).hom.app A).hom
        (TensorProduct.Balanced.mk ℤ R A B x y) =
      TensorProduct.Balanced.mk ℤ R A B' x (e y) :=
  tensorCoefficientMap_mk R S B B' e.toLinearMap hS A x y

/-- Identity coefficient equivalences retain the same enriched tensor functor. -/
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

/-- The actual tensor coefficient isomorphism preserves original equivalence composition. -/
theorem tensorCoefficientIso_trans :
    tensorCoefficientIso R S B B' e hS ≪≫ tensorCoefficientIso R S B' B'' e' hS' =
      tensorCoefficientIso R S B B'' (e.trans e')
        (fun s x => (congrArg e' (hS s x)).trans (hS' s (e x))) := by
  apply Iso.ext
  exact tensorCoefficientTransformation_comp R S B B' e.toLinearMap hS
    B'' e'.toLinearMap hS'

end Composition

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]

/-- Native left derivation retains the actual original coefficient isomorphism. -/
def torCoefficientIso (n : ℕ) : torFunctor R S B n ≅ torFunctor R S B' n :=
  NatIso.leftDerived (tensorCoefficientIso R S B B' e hS) n

/-- Its forward map is the existing native coefficient Tor transformation. -/
@[simp]
theorem torCoefficientIso_hom (n : ℕ) :
    (torCoefficientIso R S B B' e hS n).hom =
      torCoefficientTransformation R S B B' e.toLinearMap hS n := rfl

/-- Its inverse is the existing native inverse-coefficient Tor transformation. -/
@[simp]
theorem torCoefficientIso_inv (n : ℕ) :
    (torCoefficientIso R S B B' e hS n).inv =
      torCoefficientTransformation R S B' B e.symm.toLinearMap
        (coefficientEquiv_symm_outer e.toEquiv hS) n := rfl

/-- Identity coefficient equivalences retain the same native Tor functor. -/
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

/-- Actual original coefficient equivalence composition is preserved on native Tor. -/
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
