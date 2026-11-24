/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtension

/-!
# Actual associative scalar extension of linear equivalences

The same original balanced-quotient maps send an actual R-linear equivalence
to an S-linear equivalence, with both inverse laws derived from the original
map composition and identity laws. Source and target module universes remain
independent. This is algebra infrastructure and imports no K-theory module.
-/

public section

noncomputable section

open CategoryTheory

universe uR uS uP uQ

namespace ModuleCat.RingHomScalarExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The actual balanced scalar-extension map of an original linear equivalence. -/
def tensorLinearEquiv (f : R →+* S)
    {P : Type uP} {Q : Type uQ} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) :
    tensor f P ≃ₗ[S] tensor f Q :=
  LinearEquiv.ofLinearMap (linearMap f e.toLinearMap) (linearMap f e.symm.toLinearMap)
    (by
      rw [← linearMap_comp]
      have h : e.toLinearMap.comp e.symm.toLinearMap = (LinearMap.id : Q →ₗ[R] Q) := by
        ext q
        exact e.apply_symm_apply q
      rw [h, linearMap_id])
    (by
      rw [← linearMap_comp]
      have h : e.symm.toLinearMap.comp e.toLinearMap = (LinearMap.id : P →ₗ[R] P) := by
        ext p
        exact e.symm_apply_apply p
      rw [h, linearMap_id])

private theorem tensorLinearEquivValueComputed (f : R →+* S)
    {P : Type uP} {Q : Type uQ} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) (x : tensor f P) :
    tensorLinearEquiv f e x = linearMap f e.toLinearMap x := rfl

/-- The whole forward map retains the original scalar-extension linear map. -/
theorem tensorLinearEquiv_value (f : R →+* S)
    {P : Type uP} {Q : Type uQ} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) (x : tensor f P) :
    tensorLinearEquiv f e x = linearMap f e.toLinearMap x :=
  tensorLinearEquivValueComputed f e x

private theorem tensorLinearEquivInverseValueComputed (f : R →+* S)
    {P : Type uP} {Q : Type uQ} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) (x : tensor f Q) :
    (tensorLinearEquiv f e).symm x = linearMap f e.symm.toLinearMap x := rfl

/-- The whole inverse is the original scalar map of the actual inverse linear equivalence. -/
theorem tensorLinearEquiv_symm_value (f : R →+* S)
    {P : Type uP} {Q : Type uQ} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) (x : tensor f Q) :
    (tensorLinearEquiv f e).symm x = linearMap f e.symm.toLinearMap x :=
  tensorLinearEquivInverseValueComputed f e x

/-- Every original pure representative retains the actual linear-equivalence value. -/
theorem tensorLinearEquiv_pure (f : R →+* S)
    {P : Type uP} {Q : Type uQ} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) (s : S) (p : P) :
    tensorLinearEquiv f e (pure f P s p) = pure f Q s (e p) :=
  (tensorLinearEquiv_value f e _).trans (linearMap_pure f e.toLinearMap s p)

end ModuleCat.RingHomScalarExtension

end
