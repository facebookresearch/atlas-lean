/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.QuantumInformation.Finite.NoCloning

/-!
# No-cloning public-API and boundary checks

Exact-statement exercise for `NoCloning.no_cloning_two_state`, plus the identical-state
boundary case: a unit vector paired with itself has `‖⟪ψ, ψ⟫‖ = 1`, so the strict
`0 < ‖·‖ < 1` obstruction hypothesis can never fire.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

namespace NoCloningTest

/-- Exact public-API statement check. -/
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ φ b : H) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hb : ‖b‖ = 1)
    (hpos : 0 < ‖⟪ψ, φ⟫_ℂ‖) (hlt : ‖⟪ψ, φ⟫_ℂ‖ < 1) :
    ¬ ∃ (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H)),
      U (ψ ⊗ₜ[ℂ] b) = ψ ⊗ₜ[ℂ] ψ ∧ U (φ ⊗ₜ[ℂ] b) = φ ⊗ₜ[ℂ] φ :=
  MathlibExt.QuantumInformation.Finite.NoCloning.no_cloning_two_state
    ψ φ b hψ hφ hb hpos hlt

/-- Boundary: identical unit states escape the obstruction since `‖⟪ψ, ψ⟫‖ = 1`. -/
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) (hψ : ‖ψ‖ = 1) : ¬ (0 < ‖⟪ψ, ψ⟫_ℂ‖ ∧ ‖⟪ψ, ψ⟫_ℂ‖ < 1) := by
  have hself : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  rw [hself, norm_one]
  norm_num

/-- The orthonormal-pair hypothesis of `no_cloning_linear` holds on a qubit `ℂ²`, so the
linear no-cloning theorem is not vacuous there. -/
example : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 2))‖ = 1 ∧
    ‖(EuclideanSpace.single 1 1 : EuclideanSpace ℂ (Fin 2))‖ = 1 ∧
    ⟪(EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 2)),
      (EuclideanSpace.single 1 1 : EuclideanSpace ℂ (Fin 2))⟫_ℂ = 0 := by
  refine ⟨by simp, by simp, ?_⟩
  rw [EuclideanSpace.inner_single_left]
  simp

/-- On a qubit, no linear map clones every unit vector. -/
example (b : EuclideanSpace ℂ (Fin 2)) :
    ¬ ∃ U : (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) →ₗ[ℂ]
        (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)),
      ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → U (ψ ⊗ₜ[ℂ] b) = ψ ⊗ₜ[ℂ] ψ :=
  MathlibExt.QuantumInformation.Finite.NoCloning.no_cloning_linear
    (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) b (by simp) (by simp)
    (by rw [EuclideanSpace.inner_single_left]; simp)

end NoCloningTest
