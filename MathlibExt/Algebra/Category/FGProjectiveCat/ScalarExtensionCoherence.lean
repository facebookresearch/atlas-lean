/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionLinearEquiv
public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionUnit
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Associator

/-!
# Canonical balanced scalar-extension comparisons

The coefficient unitor and tensor associator give the actual outer-linear
comparisons for scalar extension. The original shrink coordinates retain the
ring-universe finite-projective objects. All ring and module universes in
these comparisons remain independent.
-/

public section
noncomputable section

open CategoryTheory MulOpposite

universe uR uS uT uP uQ

namespace ModuleCat.RingHomScalarExtension

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

private def coefficientGroundEquiv (g : S →+* T) : tensor g S ≃ₗ[ℤ] T := by
  letI := rightModule g
  exact TensorProduct.Balanced.rightUnitor ℤ S T

private theorem coefficientGroundEquiv_pure (g : S →+* T) (t : T) (s : S) :
    coefficientGroundEquiv g (pure g S t s) = t * g s := by
  let := rightModule g
  change TensorProduct.Balanced.rightUnitor ℤ S T
    (TensorProduct.Balanced.mk ℤ S T S t s) = t * g s
  rw [TensorProduct.Balanced.rightUnitor_mk, rightModule_smul]

/-- Contract the original coefficient tensor by its canonical right unitor, with the earned
outer linearity. -/
def coefficientLinearEquiv (g : S →+* T) : tensor g S ≃ₗ[T] T := by
  letI := rightModule g
  letI := leftRightComm g
  let e := coefficientGroundEquiv g
  refine e.toAddEquiv.toLinearEquiv ?_
  intro a x
  have he : e.toAddMonoidHom.comp
      (TensorProduct.Balanced.leftAction ℤ S T T S a).toAddMonoidHom =
      (Module.toModuleEnd ℤ T a).toAddMonoidHom.comp e.toAddMonoidHom := by
    apply TensorProduct.Balanced.addHom_ext ℤ S T S
    intro t s
    change e (TensorProduct.Balanced.leftAction ℤ S T T S a (pure g S t s)) =
      a • e (pure g S t s)
    have hAction : TensorProduct.Balanced.leftAction ℤ S T T S a (pure g S t s) =
        pure g S (a * t) s :=
      TensorProduct.Balanced.leftAction_mk ℤ S T T S a t s
    rw [hAction, coefficientGroundEquiv_pure, coefficientGroundEquiv_pure]
    exact mul_assoc a t (g s)
  exact DFunLike.congr_fun he x

/-- The coefficient unitor retains the original ordered pure factors. -/
@[simp]
theorem coefficientLinearEquiv_pure (g : S →+* T) (t : T) (s : S) :
    coefficientLinearEquiv g (pure g S t s) = t * g s :=
  coefficientGroundEquiv_pure g t s

/-- The inverse coefficient unitor inserts the original right unit. -/
@[simp]
theorem coefficientLinearEquiv_symm (g : S →+* T) (t : T) :
    (coefficientLinearEquiv g).symm t = pure g S t 1 := by
  apply (coefficientLinearEquiv g).injective
  rw [LinearEquiv.apply_symm_apply, coefficientLinearEquiv_pure, map_one, mul_one]

private theorem coefficientGroundEquiv_right (f : R →+* S) (g : S →+* T) :
    letI := rightModule f
    letI := rightModule g
    letI := leftRightComm f
    letI := TensorProduct.Balanced.rightModule ℤ S R T S
    letI := rightModule (g.comp f)
    ∀ (r : R) (x : tensor g S),
      coefficientGroundEquiv g ((op r) • x) = (op r) • coefficientGroundEquiv g x := by
  let := rightModule f
  let := rightModule g
  let := leftRightComm f
  let := TensorProduct.Balanced.rightModule ℤ S R T S
  let := rightModule (g.comp f)
  intro r x
  let e := coefficientGroundEquiv g
  have he : e.toAddMonoidHom.comp
      (TensorProduct.Balanced.rightAction ℤ S R T S (op r)).toAddMonoidHom =
      (Module.toModuleEnd ℤ T (op r)).toAddMonoidHom.comp e.toAddMonoidHom := by
    apply TensorProduct.Balanced.addHom_ext ℤ S T S
    intro t s
    change e (TensorProduct.Balanced.rightAction ℤ S R T S (op r) (pure g S t s)) =
      (op r) • e (pure g S t s)
    have hAction : TensorProduct.Balanced.rightAction ℤ S R T S (op r) (pure g S t s) =
        pure g S t (s * f r) := by
      have h := TensorProduct.Balanced.rightAction_mk ℤ S R T S (op r) t s
      change TensorProduct.Balanced.rightAction ℤ S R T S (op r) (pure g S t s) =
        pure g S t ((op r) • s) at h
      rw [rightModule_smul f] at h
      exact h
    rw [hAction, coefficientGroundEquiv_pure, coefficientGroundEquiv_pure,
      rightModule_smul (g.comp f)]
    change t * g (s * f r) = (t * g s) * g (f r)
    rw [g.map_mul, mul_assoc]
  exact DFunLike.congr_fun he x

/-- The canonical balanced tensor associator and coefficient unitor compare the actual
composite extension. -/
def compositionLinearEquiv (f : R →+* S) (g : S →+* T)
    (P : Type uP) [AddCommGroup P] [Module R P] :
    tensor g (tensor f P) ≃ₗ[T] tensor (g.comp f) P := by
  letI := rightModule f
  letI := rightModule g
  letI := rightModule (g.comp f)
  letI := leftRightComm f
  letI := leftRightComm g
  letI := leftRightComm (g.comp f)
  let C := TensorProduct.Balanced ℤ S T S
  letI := TensorProduct.Balanced.rightModule ℤ S R T S
  letI := TensorProduct.Balanced.leftModule ℤ S T T S
  letI := TensorProduct.Balanced.leftSMulCommClass ℤ S T T S
  letI := TensorProduct.Balanced.leftRightSMulCommClass ℤ S R T S T
  letI := TensorProduct.Balanced.leftModule ℤ R T C P
  letI := TensorProduct.Balanced.leftModule ℤ R S S P
  letI := TensorProduct.Balanced.leftModule ℤ S T T (TensorProduct.Balanced ℤ R S P)
  letI := TensorProduct.Balanced.leftModule ℤ R T T P
  let e := coefficientGroundEquiv g
  let hRight : ∀ (r : R) (x : C), e ((op r) • x) = (op r) • e x :=
    coefficientGroundEquiv_right f g
  let hP : ∀ (r : R) (p : P), (LinearEquiv.refl ℤ P) (r • p) =
      r • (LinearEquiv.refl ℤ P) p := fun _ _ => rfl
  let hLeft : ∀ (a : T) (x : C), e (a • x) = a • e x :=
    fun a x => (coefficientLinearEquiv g).map_smul a x
  let contraction := TensorProduct.Balanced.congr e (LinearEquiv.refl ℤ P) hRight hP
  let contractionT : TensorProduct.Balanced ℤ R C P ≃ₗ[T]
      TensorProduct.Balanced ℤ R T P :=
    contraction.toAddEquiv.toLinearEquiv (by
      intro a x
      exact DFunLike.congr_fun
        (TensorProduct.Balanced.map_leftAction e.toLinearMap
          (LinearEquiv.refl ℤ P).toLinearMap hRight hP hLeft a) x)
  let associationT : TensorProduct.Balanced.assocSource ℤ S R T S P ≃ₗ[T]
      TensorProduct.Balanced.assocTarget ℤ S R T S P :=
    (TensorProduct.Balanced.assoc ℤ S R T S P).toAddEquiv.toLinearEquiv
      (fun a x => TensorProduct.Balanced.assoc_left_smul ℤ S R T S P T a x)
  exact associationT.symm.trans contractionT

/-- Reassociation followed by the coefficient unitor keeps the original pure factors. -/
@[simp]
theorem compositionLinearEquiv_pure (f : R →+* S) (g : S →+* T)
    (P : Type uP) [AddCommGroup P] [Module R P] (t : T) (s : S) (p : P) :
    compositionLinearEquiv f g P (pure g (tensor f P) t (pure f P s p)) =
      pure (g.comp f) P (t * g s) p := by
  let := rightModule f
  let := rightModule g
  let := rightModule (g.comp f)
  let := leftRightComm f
  let := leftRightComm g
  let := leftRightComm (g.comp f)
  let C := TensorProduct.Balanced ℤ S T S
  let := TensorProduct.Balanced.rightModule ℤ S R T S
  let := TensorProduct.Balanced.leftModule ℤ S T T S
  let := TensorProduct.Balanced.leftSMulCommClass ℤ S T T S
  let := TensorProduct.Balanced.leftRightSMulCommClass ℤ S R T S T
  let := TensorProduct.Balanced.leftModule ℤ R T C P
  let := TensorProduct.Balanced.leftModule ℤ R S S P
  let := TensorProduct.Balanced.leftModule ℤ S T T (TensorProduct.Balanced ℤ R S P)
  let := TensorProduct.Balanced.leftModule ℤ R T T P
  let hP : ∀ (r : R) (p : P), (LinearEquiv.refl ℤ P) (r • p) =
      r • (LinearEquiv.refl ℤ P) p := fun _ _ => rfl
  change TensorProduct.Balanced.congr (coefficientGroundEquiv g) (LinearEquiv.refl ℤ P)
      (coefficientGroundEquiv_right f g) hP
      ((TensorProduct.Balanced.assoc ℤ S R T S P).symm
        (TensorProduct.Balanced.mk ℤ S T (TensorProduct.Balanced ℤ R S P) t
          (TensorProduct.Balanced.mk ℤ R S P s p))) =
    TensorProduct.Balanced.mk ℤ R T P (t * g s) p
  rw [TensorProduct.Balanced.assoc_symm_mk_mk, TensorProduct.Balanced.congr_mk]
  change TensorProduct.Balanced.mk ℤ R T P (coefficientGroundEquiv g (pure g S t s)) p = _
  rw [coefficientGroundEquiv_pure]

/-- The inverse comparison inserts the original intermediate left unit. -/
@[simp]
theorem compositionLinearEquiv_symm_pure (f : R →+* S) (g : S →+* T)
    (P : Type uP) [AddCommGroup P] [Module R P] (t : T) (p : P) :
    (compositionLinearEquiv f g P).symm (pure (g.comp f) P t p) =
      pure g (tensor f P) t (pure f P 1 p) := by
  apply (compositionLinearEquiv f g P).injective
  rw [LinearEquiv.apply_symm_apply, compositionLinearEquiv_pure, map_one, mul_one]

/-- The original linear maps commute with the canonical composite tensor comparison. -/
theorem compositionLinearEquiv_naturality (f : R →+* S) (g : S →+* T)
    {P : Type uP} {Q : Type uQ} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (h : P →ₗ[R] Q) :
    (compositionLinearEquiv f g Q).toLinearMap.comp (linearMap g (linearMap f h)) =
      (linearMap (g.comp f) h).comp (compositionLinearEquiv f g P).toLinearMap := by
  apply linearMap_ext g (tensor f P)
  intro t x
  let := rightModule f
  let a : tensor f P →+ tensor (g.comp f) Q :=
    ((compositionLinearEquiv f g Q).toLinearMap.comp
      (linearMap g (linearMap f h))).toAddMonoidHom.comp
        (pure g (tensor f P) t).toAddMonoidHom
  let b : tensor f P →+ tensor (g.comp f) Q :=
    ((linearMap (g.comp f) h).comp
      (compositionLinearEquiv f g P).toLinearMap).toAddMonoidHom.comp
        (pure g (tensor f P) t).toAddMonoidHom
  have hab : a = b := by
    apply TensorProduct.Balanced.addHom_ext ℤ R S P
    intro s p
    change compositionLinearEquiv f g Q
        (linearMap g (linearMap f h) (pure g (tensor f P) t (pure f P s p))) =
      linearMap (g.comp f) h
        (compositionLinearEquiv f g P (pure g (tensor f P) t (pure f P s p)))
    rw [linearMap_pure, linearMap_pure, compositionLinearEquiv_pure,
      compositionLinearEquiv_pure, linearMap_pure]
  exact DFunLike.congr_fun hab x

end ModuleCat.RingHomScalarExtension

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

/-- Actual ring-universe scalar-extension coordinates from the canonical shrink to the
original tensor. -/
def ringScalarExtensionCoordinates (f : R →+* S) (P : FGProjectiveCat.{uR} R) :
    (ringScalarExtension f).obj P ≃ₗ[S] ModuleCat.RingHomScalarExtension.tensor f P :=
  (UniverseEquivalence.shrinkLinearEquiv.{uS, uR} S ((scalarExtension f).obj P)).trans
    (scalarExtensionCarrierLinearEquiv f P)

/-- The complete forward coordinates are the original shrink followed by tensor coordinates. -/
theorem ringScalarExtensionCoordinates_apply (f : R →+* S) (P : FGProjectiveCat.{uR} R)
    (x : (ringScalarExtension f).obj P) :
    ringScalarExtensionCoordinates f P x =
      scalarExtensionCarrierLinearEquiv f P
        (UniverseEquivalence.shrinkLinearEquiv.{uS, uR} S ((scalarExtension f).obj P) x) := by
  exact LinearEquiv.trans_apply
    (e₁₂ := UniverseEquivalence.shrinkLinearEquiv.{uS, uR} S ((scalarExtension f).obj P))
    (e₂₃ := scalarExtensionCarrierLinearEquiv f P) x

/-- The complete inverse uses inverse tensor coordinates followed by the original shrink inverse. -/
theorem ringScalarExtensionCoordinates_symm_apply (f : R →+* S) (P : FGProjectiveCat.{uR} R)
    (x : ModuleCat.RingHomScalarExtension.tensor f P) :
    (ringScalarExtensionCoordinates f P).symm x =
      (UniverseEquivalence.shrinkLinearEquiv.{uS, uR} S ((scalarExtension f).obj P)).symm
        ((scalarExtensionCarrierLinearEquiv f P).symm x) := by
  exact LinearEquiv.symm_trans_apply
    (e₁₂ := UniverseEquivalence.shrinkLinearEquiv.{uS, uR} S ((scalarExtension f).obj P))
    (e₂₃ := scalarExtensionCarrierLinearEquiv f P) x

/-- The original native scalar morphisms commute with the actual shrink coordinates. -/
theorem ringScalarExtensionCoordinates_naturality (f : R →+* S)
    {P Q : FGProjectiveCat.{uR} R} (h : P ⟶ Q) :
    (ringScalarExtensionCoordinates f Q).toLinearMap.comp
        ((ringScalarExtension f).map h).hom.hom =
      (ModuleCat.RingHomScalarExtension.linearMap f h.hom.hom).comp
        (ringScalarExtensionCoordinates f P).toLinearMap := by
  apply LinearMap.ext
  intro x
  let DP := UniverseEquivalence.shrinkLinearEquiv.{uS, uR} S ((scalarExtension f).obj P)
  let DQ := UniverseEquivalence.shrinkLinearEquiv.{uS, uR} S ((scalarExtension f).obj Q)
  have hshrink : ((ringScalarExtension f).map h).hom.hom x =
      DQ.symm (((scalarExtension f).map h).hom.hom (DP x)) := by
    exact UniverseEquivalence.shrinkFunctor_map_apply S ((scalarExtension f).map h) x
  have hcarrier := LinearMap.congr_fun (scalarExtensionCarrierLinearEquiv_naturality f h) (DP x)
  change scalarExtensionCarrierLinearEquiv f Q
      (((scalarExtension f).map h).hom.hom (DP x)) =
    ModuleCat.RingHomScalarExtension.linearMap f h.hom.hom
      (scalarExtensionCarrierLinearEquiv f P (DP x)) at hcarrier
  change ringScalarExtensionCoordinates f Q (((ringScalarExtension f).map h).hom.hom x) =
    ModuleCat.RingHomScalarExtension.linearMap f h.hom.hom (ringScalarExtensionCoordinates f P x)
  calc
    _ = scalarExtensionCarrierLinearEquiv f Q
        (DQ (((ringScalarExtension f).map h).hom.hom x)) :=
      ringScalarExtensionCoordinates_apply f Q _
    _ = scalarExtensionCarrierLinearEquiv f Q
        (((scalarExtension f).map h).hom.hom (DP x)) := by
      rw [hshrink, DQ.apply_symm_apply]
    _ = ModuleCat.RingHomScalarExtension.linearMap f h.hom.hom
        (scalarExtensionCarrierLinearEquiv f P (DP x)) := hcarrier
    _ = _ := congrArg (ModuleCat.RingHomScalarExtension.linearMap f h.hom.hom)
      (ringScalarExtensionCoordinates_apply f P x).symm

end FGProjectiveCat

end
