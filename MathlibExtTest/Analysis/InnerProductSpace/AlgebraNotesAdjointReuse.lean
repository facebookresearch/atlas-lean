/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

/-!
# AlgebraNotes canonical API reuse tests

Canonical adjoint pairing, uniqueness, normal-operator norms and orthonormal bases.
The continuous normality check is not a claimed LinearMap conversion theorem.
-/

namespace AlgebraNotesApiProbe

private theorem adjoint_pairing {K E : Type*} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [FiniteDimensional K E] (A : E →ₗ[K] E) (x y : E) :
    @inner K E _ x (A.adjoint y) = @inner K E _ (A x) y :=
  LinearMap.adjoint_inner_right A x y

private theorem adjoint_unique {K E : Type*} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [FiniteDimensional K E] (A B : E →ₗ[K] E) :
    A = B.adjoint ↔ ∀ x y, @inner K E _ (A x) y = @inner K E _ x (B y) :=
  LinearMap.eq_adjoint_iff A B

private theorem normal_norm {K E : Type*} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [CompleteSpace E] (A : E →L[K] E) (h : IsStarNormal A)
    (x : E) : ‖A x‖ = ‖A.adjoint x‖ :=
  (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp h) x

private theorem basis_existence {K E : Type*} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [FiniteDimensional K E] :
    Nonempty (OrthonormalBasis (Fin (Module.finrank K E)) K E) :=
  ⟨stdOrthonormalBasis K E⟩

-- Reversal and conjugation are exercised through the canonical involution law.
example : (LinearMap.id : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ]
    EuclideanSpace ℂ (Fin 2)).adjoint = LinearMap.id := by simp

#print axioms adjoint_pairing
#print axioms adjoint_unique
#print axioms normal_norm
#print axioms basis_existence

end AlgebraNotesApiProbe
