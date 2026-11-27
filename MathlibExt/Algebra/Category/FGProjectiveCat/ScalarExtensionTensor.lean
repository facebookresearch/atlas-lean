/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionCoherence
public import MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeComplement
public import MathlibExt.Algebra.Category.FGProjectiveCat.Monoidal
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensor products in the original native scalar extension

For commutative rings in independent universes, the original integral balanced
quotient is linearly equivalent to the ordinary scalar tensor product. Its
forward and inverse maps retain the literal pure representatives. Mathlib's
`distribBaseChange` then supplies the tensor-product comparison, and the
existing shrink coordinates give an isomorphism between the actual native
finite-projective objects.

The module comparisons do not require finite projectivity, flatness, or a
Noetherian hypothesis. This module contains only algebra infrastructure.
-/

public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe uR uS uP uQ uP' uQ' uV

namespace ModuleCat.RingHomScalarExtension

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

private def scalarAddHom (a : S) (V : Type uV) [AddCommGroup V] [Module S V] : V →+ V where
  toFun x := a • x
  map_zero' := smul_zero a
  map_add' := smul_add a

private def standardPairing (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    letI := f.toAlgebra
    S →ₗ[ℤ] P →ₗ[ℤ] S ⊗[R] P := by
  letI := f.toAlgebra
  let a : S →+ (P →ₗ[ℤ] S ⊗[R] P) :=
    { toFun := fun s => (TensorProduct.mk R S P s).toAddMonoidHom.toIntLinearMap
      map_zero' := by
        apply LinearMap.ext
        intro p
        exact TensorProduct.zero_tmul S p
      map_add' := by
        intro s t
        apply LinearMap.ext
        intro p
        exact TensorProduct.add_tmul s t p }
  exact a.toIntLinearMap

private theorem standardPairing_balance (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    letI := f.toAlgebra
    letI := rightModule f
    ∀ (r : R) (s : S) (p : P),
      standardPairing f P (op r • s) p = standardPairing f P s (r • p) := by
  let := f.toAlgebra
  let := rightModule f
  intro r s p
  change (op r • s) ⊗ₜ[R] p = s ⊗ₜ[R] (r • p)
  rw [rightModule_smul f r s, mul_comm s (f r)]
  exact TensorProduct.smul_tmul r s p

private def tensorToStandardGround (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    letI := f.toAlgebra
    tensor f P →ₗ[ℤ] S ⊗[R] P := by
  letI := f.toAlgebra
  letI := rightModule f
  exact TensorProduct.Balanced.lift (standardPairing f P) (standardPairing_balance f P)

private theorem tensorToStandardGround_pure (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] (s : S) (p : P) :
    letI := f.toAlgebra
    tensorToStandardGround f P (pure f P s p) = s ⊗ₜ[R] p := by
  let := f.toAlgebra
  let := rightModule f
  rfl

private def tensorToStandard (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    letI := f.toAlgebra
    tensor f P →ₗ[S] S ⊗[R] P := by
  letI := f.toAlgebra
  let l := tensorToStandardGround f P
  refine { toFun := l, map_add' := l.map_add, map_smul' := ?_ }
  intro a x
  have h : l.toAddMonoidHom.comp (scalarAddHom a (tensor f P)) =
      (scalarAddHom a (S ⊗[R] P)).comp l.toAddMonoidHom := by
    let := rightModule f
    apply TensorProduct.Balanced.addHom_ext ℤ R S P
    intro s p
    change l (a • pure f P s p) = a • l (pure f P s p)
    rw [smul_pure, tensorToStandardGround_pure, tensorToStandardGround_pure]
    exact (TensorProduct.smul_tmul' a s p).symm
  exact DFunLike.congr_fun h x

private theorem tensorToStandard_pure (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] (s : S) (p : P) :
    letI := f.toAlgebra
    tensorToStandard f P (pure f P s p) = s ⊗ₜ[R] p :=
  tensorToStandardGround_pure f P s p

private def standardToTensor (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    letI := f.toAlgebra
    S ⊗[R] P →ₗ[S] tensor f P := by
  letI := f.toAlgebra
  letI : Module R (tensor f P) := Module.compHom (tensor f P) f
  letI : IsScalarTower R S (tensor f P) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : SMulCommClass R S (tensor f P) :=
    ⟨fun r s x => by
      change f r • (s • x) = s • (f r • x)
      rw [← mul_smul, ← mul_smul, mul_comm]⟩
  let a : S →ₗ[S] P →ₗ[R] tensor f P :=
    { toFun := fun s =>
        { toFun := pure f P s
          map_add' := (pure f P s).map_add
          map_smul' := by
            intro r p
            change pure f P s (r • p) = f r • pure f P s p
            rw [← pure_balance f P r s p, smul_pure, mul_comm] }
      map_add' := by
        intro s t
        apply LinearMap.ext
        intro p
        exact LinearMap.congr_fun ((pure f P).map_add s t) p
      map_smul' := by
        intro a s
        apply LinearMap.ext
        intro p
        exact (smul_pure f P a s p).symm }
  exact TensorProduct.AlgebraTensorModule.lift a

private theorem standardToTensor_tmul (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] (s : S) (p : P) :
    letI := f.toAlgebra
    standardToTensor f P (s ⊗ₜ[R] p) = pure f P s p := by
  let := f.toAlgebra
  rfl

/-- The original integral balanced scalar tensor and the ordinary scalar tensor
have their actual S-linear equivalence, with independent carrier universes. -/
def commutativeTensorLinearEquiv (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    letI := f.toAlgebra
    tensor f P ≃ₗ[S] S ⊗[R] P := by
  letI := f.toAlgebra
  refine LinearEquiv.ofLinearMap (tensorToStandard f P) (standardToTensor f P) ?_ ?_
  · apply TensorProduct.AlgebraTensorModule.ext
    intro s p
    rw [LinearMap.comp_apply, standardToTensor_tmul, tensorToStandard_pure]
    rfl
  · apply linearMap_ext f P
    intro s p
    rw [LinearMap.comp_apply, tensorToStandard_pure, standardToTensor_tmul]
    rfl

/-- Every original balanced pure class becomes the corresponding ordinary pure tensor. -/
@[simp]
theorem commutativeTensorLinearEquiv_pure (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] (s : S) (p : P) :
    letI := f.toAlgebra
    commutativeTensorLinearEquiv f P (pure f P s p) = s ⊗ₜ[R] p :=
  tensorToStandard_pure f P s p

/-- The actual inverse sends an ordinary pure tensor to its original balanced class. -/
@[simp]
theorem commutativeTensorLinearEquiv_symm_tmul (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] (s : S) (p : P) :
    letI := f.toAlgebra
    (commutativeTensorLinearEquiv f P).symm (s ⊗ₜ[R] p) = pure f P s p :=
  standardToTensor_tmul f P s p

/-- Scalar extension distributes over the original module tensor product.
The comparison uses the existing independent-universe `distribBaseChange`. -/
def tensorProductLinearEquiv (f : R →+* S) (P : Type uP) (Q : Type uQ)
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] :
    tensor f (P ⊗[R] Q) ≃ₗ[S] (tensor f P) ⊗[S] (tensor f Q) := by
  letI := f.toAlgebra
  exact (commutativeTensorLinearEquiv f (P ⊗[R] Q)).trans
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R S P Q).trans
      (TensorProduct.congr (commutativeTensorLinearEquiv f P).symm
        (commutativeTensorLinearEquiv f Q).symm))

/-- The complete forward tensor comparison on the original nested pure classes. -/
@[simp]
theorem tensorProductLinearEquiv_pure (f : R →+* S) (P : Type uP) (Q : Type uQ)
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (s : S) (p : P) (q : Q) :
    tensorProductLinearEquiv f P Q (pure f (P ⊗[R] Q) s (p ⊗ₜ[R] q)) =
      (pure f P s p) ⊗ₜ[S] (pure f Q 1 q) := by
  let := f.toAlgebra
  simp only [tensorProductLinearEquiv, LinearEquiv.trans_apply,
    commutativeTensorLinearEquiv_pure, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
    TensorProduct.congr_tmul, commutativeTensorLinearEquiv_symm_tmul]

/-- The complete inverse multiplies the original two coefficient scalars. -/
@[simp]
theorem tensorProductLinearEquiv_symm_pure (f : R →+* S) (P : Type uP) (Q : Type uQ)
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (s t : S) (p : P) (q : Q) :
    (tensorProductLinearEquiv f P Q).symm
        ((pure f P s p) ⊗ₜ[S] (pure f Q t q)) =
      pure f (P ⊗[R] Q) (s * t) (p ⊗ₜ[R] q) := by
  let := f.toAlgebra
  simp only [tensorProductLinearEquiv, LinearEquiv.symm_trans_apply,
    TensorProduct.congr_symm_tmul, LinearEquiv.symm_symm,
    commutativeTensorLinearEquiv_pure,
    TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    commutativeTensorLinearEquiv_symm_tmul]

/-- The tensor comparison intertwines the original scalar-extension maps
of two actual linear maps. All four module universes remain independent. -/
theorem tensorProductLinearEquiv_naturality (f : R →+* S)
    {P : Type uP} {Q : Type uQ} {P' : Type uP'} {Q' : Type uQ'}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q']
    (a : P →ₗ[R] P') (b : Q →ₗ[R] Q') :
    (tensorProductLinearEquiv f P' Q').toLinearMap.comp (linearMap f (TensorProduct.map a b)) =
      (TensorProduct.map (linearMap f a) (linearMap f b)).comp
        (tensorProductLinearEquiv f P Q).toLinearMap := by
  apply linearMap_ext f (P ⊗[R] Q)
  intro s x
  induction x using TensorProduct.inductionOn with
  | tmul p q =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, linearMap_pure,
        TensorProduct.map_tmul, tensorProductLinearEquiv_pure]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

end ModuleCat.RingHomScalarExtension

namespace FGProjectiveCat

open ModuleCat.RingHomScalarExtension
open MonoidalCategory

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- The actual native finite-projective tensor coordinates use the original
shrink, the ordinary base-change tensor comparison, and the inverse shrinks. -/
def ringScalarExtensionTensorLinearEquiv (f : R →+* S) (P Q : FGProjectiveCat.{uR} R) :
    (ringScalarExtension f).obj (P ⊗ Q) ≃ₗ[S]
      ((ringScalarExtension f).obj P ⊗ (ringScalarExtension f).obj Q : FGProjectiveCat.{uS} S) :=
  (ringScalarExtensionCoordinates f (P ⊗ Q)).trans
    ((tensorProductLinearEquiv f P Q).trans
      (TensorProduct.congr (ringScalarExtensionCoordinates f P).symm
        (ringScalarExtensionCoordinates f Q).symm))

/-- Tensor comparison on the original native objects, in the target ring's own universe. -/
def ringScalarExtensionTensorIso (f : R →+* S) (P Q : FGProjectiveCat.{uR} R) :
    (ringScalarExtension f).obj (P ⊗ Q) ≅
      (ringScalarExtension f).obj P ⊗ (ringScalarExtension f).obj Q :=
  isoOfLinearEquiv (ringScalarExtensionTensorLinearEquiv f P Q)

/-- The actual native Iso sends a shrink of an original nested pure class
to the tensor of the original two inverse shrink coordinates. -/
theorem ringScalarExtensionTensorIso_hom_pure (f : R →+* S)
    (P Q : FGProjectiveCat.{uR} R) (s : S) (p : P) (q : Q) :
    (ringScalarExtensionTensorIso f P Q).hom.hom.hom
        ((ringScalarExtensionCoordinates f (P ⊗ Q)).symm
          (pure f (P ⊗[R] Q) s (p ⊗ₜ[R] q))) =
      ((ringScalarExtensionCoordinates f P).symm (pure f P s p)) ⊗ₜ[S]
        ((ringScalarExtensionCoordinates f Q).symm (pure f Q 1 q)) := by
  change ringScalarExtensionTensorLinearEquiv f P Q _ = _
  simp only [ringScalarExtensionTensorLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  simpa only [TensorProduct.congr_tmul] using
    congrArg (TensorProduct.congr (ringScalarExtensionCoordinates f P).symm
      (ringScalarExtensionCoordinates f Q).symm)
        (tensorProductLinearEquiv_pure f P Q s p q)

/-- The inverse native Iso reads both original shrink coordinates and
multiplies their coefficient scalars in the genuine balanced tensor. -/
theorem ringScalarExtensionTensorIso_inv_pure (f : R →+* S)
    (P Q : FGProjectiveCat.{uR} R) (s t : S) (p : P) (q : Q) :
    (ringScalarExtensionTensorIso f P Q).inv.hom.hom
        (((ringScalarExtensionCoordinates f P).symm (pure f P s p)) ⊗ₜ[S]
          ((ringScalarExtensionCoordinates f Q).symm (pure f Q t q))) =
      (ringScalarExtensionCoordinates f (P ⊗ Q)).symm
        (pure f (P ⊗[R] Q) (s * t) (p ⊗ₜ[R] q)) := by
  change (ringScalarExtensionTensorLinearEquiv f P Q).symm _ = _
  simp only [ringScalarExtensionTensorLinearEquiv, LinearEquiv.symm_trans_apply]
  have h : (TensorProduct.congr (ringScalarExtensionCoordinates f P).symm
      (ringScalarExtensionCoordinates f Q).symm).symm
        (((ringScalarExtensionCoordinates f P).symm (pure f P s p)) ⊗ₜ[S]
          ((ringScalarExtensionCoordinates f Q).symm (pure f Q t q))) =
      (pure f P s p) ⊗ₜ[S] (pure f Q t q) := by
    simpa only [TensorProduct.congr_tmul] using
      (TensorProduct.congr (ringScalarExtensionCoordinates f P).symm
        (ringScalarExtensionCoordinates f Q).symm).symm_apply_apply
          ((pure f P s p) ⊗ₜ[S] (pure f Q t q))
  rw [h]
  exact congrArg (ringScalarExtensionCoordinates f (P ⊗ Q)).symm
    (tensorProductLinearEquiv_symm_pure f P Q s t p q)

end FGProjectiveCat
