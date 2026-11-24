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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.VectorFunctionalCriterion
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual spatial normal operator maps between the original Hilbert spaces

Conjugation by an actual linear isometry equivalence sends a concrete
von Neumann algebra into the full original target operator algebra.
Its vector-functional pullback is the original source functional on the
inverse-transformed vectors, so the actual source predual proves normality.

This constructor supplies the normal coefficient map on the verified
H-first Borel product model. No normality, source model, Fourier unitary
or normalized dual Haar certificate is supplied. Both Hilbert universes
are independent and either Hilbert space may be zero.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra

noncomputable section

universe uH uK

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)

/-- Restrict the original spatial operator conjugation to the source algebra and full target. -/
def isometryConjugationStarAlgHom : M →⋆ₐ[ℂ] (⊤ : VonNeumannAlgebra K) where
  toFun x := ⟨e.conjStarAlgEquiv (x : H →L[ℂ] H), by trivial⟩
  map_one' := by
    apply Subtype.ext
    exact map_one e.conjStarAlgEquiv
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul e.conjStarAlgEquiv (x : H →L[ℂ] H) (y : H →L[ℂ] H)
  map_zero' := by
    apply Subtype.ext
    exact map_zero e.conjStarAlgEquiv
  map_add' x y := by
    apply Subtype.ext
    exact map_add e.conjStarAlgEquiv (x : H →L[ℂ] H) (y : H →L[ℂ] H)
  commutes' c := by
    apply Subtype.ext
    change e.conjStarAlgEquiv (algebraMap ℂ (H →L[ℂ] H) c) = algebraMap ℂ (K →L[ℂ] K) c
    exact AlgEquivClass.commutes e.conjStarAlgEquiv c
  map_star' x := by
    apply Subtype.ext
    exact map_star e.conjStarAlgEquiv (x : H →L[ℂ] H)

/-- The restricted spatial map has the exact original bounded-operator value. -/
theorem isometryConjugationStarAlgHom_coe (x : M) :
    (isometryConjugationStarAlgHom e M x : K →L[ℂ] K) =
      e.conjStarAlgEquiv (x : H →L[ℂ] H) := rfl

/-- Its computed vector pullback is the original functional on inverse-transformed vectors. -/
theorem isometryConjugation_vectorFunctional (ξ η : K) (x : M) :
    vectorFunctional (⊤ : VonNeumannAlgebra K) ξ η (isometryConjugationStarAlgHom e M x) =
      vectorFunctional M (e.symm ξ) (e.symm η) x := by
  simp only [vectorFunctional_apply, isometryConjugationStarAlgHom_coe,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  exact (e.symm.inner_map_eq_flip ξ ((x : H →L[ℂ] H) (e.symm η))).symm

/-- The exact spatial map is normal by its actual source vector-functional pullbacks. -/
def isometryConjugationNormalHom : NormalStarAlgHom M (⊤ : VonNeumannAlgebra K) := by
  let f := isometryConjugationStarAlgHom e M
  refine NormalStarAlgHom.ofVectorFunctionalPullbacks f ?_
  intro ξ η
  have hEq : (vectorFunctional (⊤ : VonNeumannAlgebra K) ξ η).comp
      (⟨LinearMap.ofClass f, map_continuous f⟩ : M →L[ℂ] (⊤ : VonNeumannAlgebra K)) =
      vectorFunctional M (e.symm ξ) (e.symm η) := by
    apply ContinuousLinearMap.ext
    intro x
    exact isometryConjugation_vectorFunctional e M ξ η x
  rw [hEq]
  exact vectorFunctional_mem_normalFunctionalSpace M (e.symm ξ) (e.symm η)

/-- The normal bundle retains the same original spatial operator value. -/
theorem isometryConjugationNormalHom_coe (x : M) :
    (isometryConjugationNormalHom e M x : K →L[ℂ] K) =
      e.conjStarAlgEquiv (x : H →L[ℂ] H) := rfl

/-- Acting on a target vector uses the actual inverse and forward Hilbert maps. -/
theorem isometryConjugationNormalHom_apply_apply (x : M) (ξ : K) :
    (isometryConjugationNormalHom e M x : K →L[ℂ] K) ξ =
      e ((x : H →L[ℂ] H) (e.symm ξ)) := rfl

end

end VonNeumannAlgebra
