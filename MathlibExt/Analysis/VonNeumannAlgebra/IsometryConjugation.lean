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
# Normal spatial maps between unitarily equivalent Hilbert spaces

For a unitary equivalence `e : H ≃ K` of complete complex Hilbert spaces and a concrete von
Neumann algebra `M ⊆ B(H)`, conjugation `x ↦ e x e⁻¹` is a unital complex star homomorphism `M →
B(K)`.

The target vector coefficient `⟨ξ,(e x e⁻¹)η⟩` pulls back to `⟨e⁻¹ξ,x(e⁻¹η)⟩`. Hence this
spatial homomorphism is ultraweakly continuous and defines a normal map to the full operator von
Neumann algebra on `K`. The Hilbert-space universes are independent and zero spaces are allowed.
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

/-- **Spatial star homomorphism into the full target operator algebra.** Let `H,K` be complete
complex Hilbert spaces, `e : H ≃ₗᵢ[ℂ] K` a unitary equivalence and `M ⊆ B(H)` a concrete
von Neumann algebra. `isometryConjugationStarAlgHom e M : M →⋆ₐ[ℂ] B(K)` sends `x` to `e x
e⁻¹`, viewing `B(K)` as its full von Neumann algebra. -/
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

/-- **Bounded-operator value of spatial conjugation.** Let `H,K` be complete complex Hilbert
spaces, `e : H ≃ₗᵢ[ℂ] K` a unitary equivalence and `M ⊆ B(H)` a concrete von Neumann
algebra. for `x ∈ M`, the operator underlying `isometryConjugationStarAlgHom e M x` is
`e.conjStarAlgEquiv x=e x e⁻¹`. -/
theorem isometryConjugationStarAlgHom_coe (x : M) :
    (isometryConjugationStarAlgHom e M x : K →L[ℂ] K) =
      e.conjStarAlgEquiv (x : H →L[ℂ] H) := rfl

/-- **Vector functional pullback through a spatial map.** Let `H,K` be complete complex
Hilbert spaces, `e : H ≃ₗᵢ[ℂ] K` a unitary equivalence and `M ⊆ B(H)` a concrete von
Neumann algebra. for `ξ,η ∈ K` and `x ∈ M`, `⟨ξ,(e x e⁻¹)η⟩=⟨e⁻¹ξ,x(e⁻¹η)⟩`, equivalently
the target vector functional pulls back to `vectorFunctional M (e.symm ξ) (e.symm η)`. -/
theorem isometryConjugation_vectorFunctional (ξ η : K) (x : M) :
    vectorFunctional (⊤ : VonNeumannAlgebra K) ξ η (isometryConjugationStarAlgHom e M x) =
      vectorFunctional M (e.symm ξ) (e.symm η) x := by
  simp only [vectorFunctional_apply, isometryConjugationStarAlgHom_coe,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  exact (e.symm.inner_map_eq_flip ξ ((x : H →L[ℂ] H) (e.symm η))).symm

/-- **Normal spatial conjugation into the full operator algebra.** Let `H,K` be complete
complex Hilbert spaces, `e : H ≃ₗᵢ[ℂ] K` a unitary equivalence and `M ⊆ B(H)` a concrete
von Neumann algebra. `isometryConjugationNormalHom e M : NormalStarAlgHom M B(K)` is the
unital complex star map `x ↦ e x e⁻¹`, continuous for the ultraweak topologies. -/
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

/-- **Operator value of the normal spatial homomorphism.** Let `H,K` be complete complex
Hilbert spaces, `e : H ≃ₗᵢ[ℂ] K` a unitary equivalence and `M ⊆ B(H)` a concrete von
Neumann algebra. for `x ∈ M`, `(isometryConjugationNormalHom e M x : B(K))=e x e⁻¹`. -/
theorem isometryConjugationNormalHom_coe (x : M) :
    (isometryConjugationNormalHom e M x : K →L[ℂ] K) =
      e.conjStarAlgEquiv (x : H →L[ℂ] H) := rfl

/-- **Target-vector action of a normal spatial map.** Let `H,K` be complete complex Hilbert
spaces, `e : H ≃ₗᵢ[ℂ] K` a unitary equivalence and `M ⊆ B(H)` a concrete von Neumann
algebra. for `x ∈ M` and `ξ ∈ K`, `(isometryConjugationNormalHom e M x)ξ=e(x(e.symm ξ))`. -/
theorem isometryConjugationNormalHom_apply_apply (x : M) (ξ : K) :
    (isometryConjugationNormalHom e M x : K →L[ℂ] K) ξ =
      e ((x : H →L[ℂ] H) (e.symm ξ)) := rfl

end

end VonNeumannAlgebra
