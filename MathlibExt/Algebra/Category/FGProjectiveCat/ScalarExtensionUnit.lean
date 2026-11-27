/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtension
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors

/-!
# The actual identity scalar extension and the existing balanced unitor

The identity right-action dictionary is identified with the original
regular action by its values. Equality elimination transports only that
quotient presentation, retaining every original pure class. The existing
balanced left unitor then supplies the map and its actual inverse.
Outer linearity and naturality are earned on pure classes of this same
quotient. No unit isomorphism or compatibility equation is a premise.
-/

noncomputable section

open MulOpposite
open scoped TensorProduct

universe uR uP uQ

namespace ModuleCat.RingHomScalarExtension

variable (R : Type uR) [Ring R]

/-- The identity coefficient action is the canonical regular right action. -/
public theorem identityRightModule_eq_regular :
    rightModule (RingHom.id R) = (inferInstance : Module Rᵐᵒᵖ R) := by
  apply Module.ext'
  intro r s
  change s * (RingHom.id R) r.unop = s * r.unop
  rfl

private def identityTensorCoordinates (P : Type uP) [AddCommGroup P] [Module R P] :
    { e : tensor (RingHom.id R) P ≃ₗ[ℤ] TensorProduct.Balanced ℤ R R P //
      ∀ (r : R) (p : P), e (pure (RingHom.id R) P r p) =
        TensorProduct.Balanced.mk ℤ R R P r p } := by
  let d : Module Rᵐᵒᵖ R := rightModule (RingHom.id R)
  let d₀ : Module Rᵐᵒᵖ R := inferInstance
  let T : Module Rᵐᵒᵖ R → Type (max uR uP) := fun a =>
    letI : Module Rᵐᵒᵖ R := a
    TensorProduct.Balanced ℤ R R P
  let z : ∀ a : Module Rᵐᵒᵖ R, R → P → T a := fun a r p =>
    letI : Module Rᵐᵒᵖ R := a
    TensorProduct.Balanced.mk ℤ R R P r p
  have compare (a b : Module Rᵐᵒᵖ R) (h : a = b) :
      { e : T a ≃ₗ[ℤ] T b // ∀ (r : R) (p : P), e (z a r p) = z b r p } := by
    cases h
    exact ⟨LinearEquiv.refl ℤ _, fun _ _ => rfl⟩
  exact compare d d₀ (identityRightModule_eq_regular R)

/-- The original identity-extension carrier, contracted by the existing balanced unitor. -/
public def identityTensorGroundEquiv (P : Type uP) [AddCommGroup P] [Module R P] :
    tensor (RingHom.id R) P ≃ₗ[ℤ] P :=
  (identityTensorCoordinates R P).val.trans (TensorProduct.Balanced.leftUnitor ℤ R P)

/-- The actual unitor sends each original pure class to the original module action. -/
public theorem identityTensorGroundEquiv_pure (P : Type uP)
    [AddCommGroup P] [Module R P] (r : R) (p : P) :
    identityTensorGroundEquiv R P (pure (RingHom.id R) P r p) = r • p := by
  change TensorProduct.Balanced.leftUnitor ℤ R P
    ((identityTensorCoordinates R P).val (pure (RingHom.id R) P r p)) = r • p
  exact (congrArg (TensorProduct.Balanced.leftUnitor ℤ R P)
    ((identityTensorCoordinates R P).property r p)).trans
      (TensorProduct.Balanced.leftUnitor_mk ℤ R P r p)

/-- The inverse inserts the same original unit pure representative. -/
public theorem identityTensorGroundEquiv_symm (P : Type uP)
    [AddCommGroup P] [Module R P] (p : P) :
    (identityTensorGroundEquiv R P).symm p = pure (RingHom.id R) P 1 p := by
  apply (identityTensorGroundEquiv R P).injective
  exact (LinearEquiv.apply_symm_apply (identityTensorGroundEquiv R P) p).trans
    ((identityTensorGroundEquiv_pure R P 1 p).trans (one_smul R p)).symm

/-- Outer linearity upgrades the same ground unitor and its original inverse. -/
public def identityTensorLinearEquiv (P : Type uP) [AddCommGroup P] [Module R P] :
    tensor (RingHom.id R) P ≃ₗ[R] P := by
  letI := rightModule (RingHom.id R)
  letI := leftRightComm (RingHom.id R)
  let e := identityTensorGroundEquiv R P
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' := ?_ }
  intro a x
  have he : e.toAddMonoidHom.comp
      ((TensorProduct.Balanced.leftAction ℤ R R R P a).toAddMonoidHom) =
      (Module.toModuleEnd ℤ P a).toAddMonoidHom.comp e.toAddMonoidHom := by
    apply TensorProduct.Balanced.addHom_ext ℤ R R P
    intro r p
    change identityTensorGroundEquiv R P
      ((TensorProduct.Balanced.leftAction ℤ R R R P a) (pure (RingHom.id R) P r p)) =
        a • identityTensorGroundEquiv R P (pure (RingHom.id R) P r p)
    have hAction : (TensorProduct.Balanced.leftAction ℤ R R R P a)
        (pure (RingHom.id R) P r p) = pure (RingHom.id R) P (a * r) p := by
      rw [pure_eq_mk]
      exact TensorProduct.Balanced.leftAction_mk ℤ R R R P a r p
    rw [hAction, identityTensorGroundEquiv_pure, identityTensorGroundEquiv_pure]
    exact mul_smul a r p
  exact DFunLike.congr_fun he x

/-- The outer-linear unitor retains the same original pure-class formula. -/
public theorem identityTensorLinearEquiv_pure (P : Type uP)
    [AddCommGroup P] [Module R P] (r : R) (p : P) :
    identityTensorLinearEquiv R P (pure (RingHom.id R) P r p) = r • p :=
  identityTensorGroundEquiv_pure R P r p

/-- Its inverse is still the original unit pure class. -/
public theorem identityTensorLinearEquiv_symm (P : Type uP)
    [AddCommGroup P] [Module R P] (p : P) :
    (identityTensorLinearEquiv R P).symm p = pure (RingHom.id R) P 1 p :=
  identityTensorGroundEquiv_symm R P p

/-- Every original linear map commutes with the actual identity-extension unitor. -/
public theorem identityTensorLinearEquiv_naturality
    {P : Type uP} {Q : Type uQ} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (g : P →ₗ[R] Q) :
    (identityTensorLinearEquiv R Q).toLinearMap.comp (linearMap (RingHom.id R) g) =
      g.comp (identityTensorLinearEquiv R P).toLinearMap := by
  let := rightModule (RingHom.id R)
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R R P
  intro r p
  change identityTensorLinearEquiv R Q (linearMap (RingHom.id R) g
      (pure (RingHom.id R) P r p)) =
    g (identityTensorLinearEquiv R P (pure (RingHom.id R) P r p))
  rw [linearMap_pure, identityTensorLinearEquiv_pure, identityTensorLinearEquiv_pure,
    g.map_smul]

end ModuleCat.RingHomScalarExtension

end
