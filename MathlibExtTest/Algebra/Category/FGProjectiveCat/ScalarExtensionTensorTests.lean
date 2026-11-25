/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionTensor

/-! Direct algebra clients for the actual scalar tensors and their native coordinates. -/

noncomputable section

open CategoryTheory ModuleCat.RingHomScalarExtension FGProjectiveCat
open scoped TensorProduct

universe uR uS uP uQ uP' uQ'

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
variable {P : Type uP} {Q : Type uQ} {P' : Type uP'} {Q' : Type uQ'}
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q']

example (f : R →+* S) (s : S) (p : P) :
    letI := f.toAlgebra
    commutativeTensorLinearEquiv f P (pure f P s p) = s ⊗ₜ[R] p :=
  commutativeTensorLinearEquiv_pure f P s p

example (f : R →+* S) (s : S) (p : P) :
    letI := f.toAlgebra
    (commutativeTensorLinearEquiv f P).symm (s ⊗ₜ[R] p) = pure f P s p :=
  commutativeTensorLinearEquiv_symm_tmul f P s p

example (f : R →+* S) (s : S) (p : P) (q : Q) :
    tensorProductLinearEquiv f P Q (pure f (P ⊗[R] Q) s (p ⊗ₜ[R] q)) =
      (pure f P s p) ⊗ₜ[S] (pure f Q 1 q) :=
  tensorProductLinearEquiv_pure f P Q s p q

-- This reads the original two scalar-extension maps before the tensor inverse.
example (f : R →+* S) (a : P →ₗ[R] P') (b : Q →ₗ[R] Q')
    (s t : S) (p : P) (q : Q) :
    (tensorProductLinearEquiv f P' Q').symm
        (TensorProduct.map (linearMap f a) (linearMap f b)
          ((pure f P s p) ⊗ₜ[S] (pure f Q t q))) =
      pure f (P' ⊗[R] Q') (s * t) ((a p) ⊗ₜ[R] (b q)) := by
  simp only [TensorProduct.map_tmul, linearMap_pure, tensorProductLinearEquiv_symm_pure]

example (f : R →+* S) (a : P →ₗ[R] P') (b : Q →ₗ[R] Q') :
    (tensorProductLinearEquiv f P' Q').toLinearMap.comp (linearMap f (TensorProduct.map a b)) =
      (TensorProduct.map (linearMap f a) (linearMap f b)).comp
        (tensorProductLinearEquiv f P Q).toLinearMap :=
  tensorProductLinearEquiv_naturality f a b

open MonoidalCategory

-- These are the actual native target objects and original inverse shrink coordinates.
example (f : R →+* S) (P Q : FGProjectiveCat.{uR} R) (s : S) (p : P) (q : Q) :
    (ringScalarExtensionTensorIso f P Q).hom.hom.hom
        ((ringScalarExtensionCoordinates f (P ⊗ Q)).symm
          (pure f (P ⊗[R] Q) s (p ⊗ₜ[R] q))) =
      ((ringScalarExtensionCoordinates f P).symm (pure f P s p)) ⊗ₜ[S]
        ((ringScalarExtensionCoordinates f Q).symm (pure f Q 1 q)) :=
  ringScalarExtensionTensorIso_hom_pure f P Q s p q

example (f : R →+* S) (P Q : FGProjectiveCat.{uR} R) (s t : S) (p : P) (q : Q) :
    (ringScalarExtensionTensorIso f P Q).inv.hom.hom
        (((ringScalarExtensionCoordinates f P).symm (pure f P s p)) ⊗ₜ[S]
          ((ringScalarExtensionCoordinates f Q).symm (pure f Q t q))) =
      (ringScalarExtensionCoordinates f (P ⊗ Q)).symm
        (pure f (P ⊗[R] Q) (s * t) (p ⊗ₜ[R] q)) :=
  ringScalarExtensionTensorIso_inv_pure f P Q s t p q

#print axioms commutativeTensorLinearEquiv
#print axioms tensorProductLinearEquiv
#print axioms tensorProductLinearEquiv_naturality
#print axioms ringScalarExtensionTensorIso
#print axioms ringScalarExtensionTensorIso_hom_pure
#print axioms ringScalarExtensionTensorIso_inv_pure
