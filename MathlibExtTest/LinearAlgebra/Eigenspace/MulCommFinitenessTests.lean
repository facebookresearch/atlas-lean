/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm

@[expose] public section

/-!
# Generalized-eigenspace finiteness for reversed products

The finite/infinite ambient-space projection and the zero-scalar counterexample
exercise the Module.Finite interface independently of totalized Module.finrank.
-/

namespace MathlibExtTest.LinearAlgebra.Eigenspace.MulCommFiniteness

open MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm.ContinuousLinearMap

/-- The ambient Finsupp space in the projection model is infinite-dimensional. -/
private theorem infinite_ambient : ¬ Module.Finite ℚ (ℕ →₀ ℚ) :=
  Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne (R := ℚ) (ι := ℕ))

/-- Finiteness of the coordinate projection is transferred from its reversed
product on the one-dimensional scalar space. -/
private theorem finite_projection_genEigenspace :
    Module.Finite ℚ (Module.End.genEigenspace
      ((Finsupp.lsingle 0 : ℚ →ₗ[ℚ] (ℕ →₀ ℚ)) ∘ₗ Finsupp.lapply 0) 1 ⊤) :=
  (MathlibExt.LinearAlgebra.Eigenspace.MulComm.End.finite_genEigenspace_comp_iff
    (Finsupp.lsingle 0 : ℚ →ₗ[ℚ] (ℕ →₀ ℚ)) (Finsupp.lapply 0)
    (by norm_num) ⊤).mpr inferInstance

/-- The finite generalized eigenspace in the infinite ambient model contains
a nonzero vector. -/
private theorem projection_genEigenspace_nonzero :
    ∃ x : ℕ →₀ ℚ, x ∈ Module.End.genEigenspace
      ((Finsupp.lsingle 0 : ℚ →ₗ[ℚ] (ℕ →₀ ℚ)) ∘ₗ Finsupp.lapply 0) 1 ⊤ ∧ x ≠ 0 := by
  refine ⟨Finsupp.single 0 1, ?_, by simp⟩
  apply Module.End.mem_genEigenspace.mpr
  refine ⟨1, by simp, ?_⟩
  rw [LinearMap.mem_ker]
  simp [Finsupp.lsingle_apply, Finsupp.lapply_apply]

/-- With scalar zero, zero maps between a finite and an infinite space have
generalized eigenspaces of different finite-dimensionality. -/
private theorem zero_scalar_finiteness_iff_fails :
    ¬ (Module.Finite ℚ (Module.End.genEigenspace
        ((0 : ℚ →ₗ[ℚ] (ℕ →₀ ℚ)) ∘ₗ (0 : (ℕ →₀ ℚ) →ₗ[ℚ] ℚ)) 0 1) ↔
      Module.Finite ℚ (Module.End.genEigenspace
        ((0 : (ℕ →₀ ℚ) →ₗ[ℚ] ℚ) ∘ₗ (0 : ℚ →ₗ[ℚ] (ℕ →₀ ℚ))) 0 1)) := by
  intro h
  have hfinite : Module.Finite ℚ (Module.End.genEigenspace
      ((0 : (ℕ →₀ ℚ) →ₗ[ℚ] ℚ) ∘ₗ (0 : ℚ →ₗ[ℚ] (ℕ →₀ ℚ))) 0 1) := by
    infer_instance
  have hinfinite := h.mpr hfinite
  rw [Module.End.genEigenspace_one, zero_smul, sub_zero,
    LinearMap.zero_comp, LinearMap.ker_zero] at hinfinite
  let := hinfinite
  apply infinite_ambient
  exact Module.Finite.of_surjective (⊤ : Submodule ℚ (ℕ →₀ ℚ)).subtype
    (fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩)

/-- The endomorphism product interface transfers a supplied finite-dimensional
generalized eigenspace without assuming the ambient space is finite. -/
theorem end_mul_finiteness_transfer {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A B : Module.End K V) {μ : K} (hμ : μ ≠ 0) (k : ℕ∞)
    (hfinite : Module.Finite K ((A * B).genEigenspace μ k)) :
    Module.Finite K ((B * A).genEigenspace μ k) :=
  (MathlibExt.LinearAlgebra.Eigenspace.MulComm.End.finite_genEigenspace_mul_iff
    A B hμ k).mp hfinite

/-- The rectangular wrapper transfers finiteness between a coordinate
projection on `ℚ³` and the identity product on `ℚ²`. -/
private theorem rectangular_matrix_finiteness :
    Module.Finite ℚ (Module.End.genEigenspace (Matrix.toLin'
      ((!![1, 0, 0; 0, 1, 0] : Matrix (Fin 2) (Fin 3) ℚ) *
        (!![1, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℚ))) 1 ⊤) :=
  (MathlibExt.LinearAlgebra.Eigenspace.MulComm.Matrix.finite_genEigenspace_mul_iff
    (!![1, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℚ)
    (!![1, 0, 0; 0, 1, 0] : Matrix (Fin 2) (Fin 3) ℚ) (by norm_num) ⊤).mp inferInstance

/-- The continuous wrapper needs finiteness of the generalized eigenspace,
with no finite-dimensionality premise on the normed ambient space. -/
theorem continuous_finiteness_transfer {K E : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E] (S T : E →L[K] E)
    {μ : K} (hμ : μ ≠ 0) (k : ℕ∞)
    (hfinite : Module.Finite K
      (Module.End.genEigenspace ((S * T : E →L[K] E) : Module.End K E) μ k)) :
    Module.Finite K
      (Module.End.genEigenspace ((T * S : E →L[K] E) : Module.End K E) μ k) :=
  (finite_genEigenspace_mul_iff S T hμ k).mp hfinite

/-- The continuous wrapper applies at exponent zero on an arbitrary normed
space, including infinite-dimensional ambient spaces. -/
theorem zero_exponent_continuous_finite {K E : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E] (S T : E →L[K] E) :
    Module.Finite K
      (Module.End.genEigenspace ((T * S : E →L[K] E) : Module.End K E) 1 0) := by
  apply (finite_genEigenspace_mul_iff S T one_ne_zero 0).mp
  rw [Module.End.genEigenspace_zero]
  infer_instance

end MathlibExtTest.LinearAlgebra.Eigenspace.MulCommFiniteness
