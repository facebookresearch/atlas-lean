/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Analysis.InnerProductSpace.KitaevGeometricLemma

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for Kitaev's geometric lemma

The tests evaluate the subspace angle for the zero and whole
subspaces, apply the geometric lemma to the identity operator on
`ℂ`, and check that a common kernel vector defeats every positive
scalar lower bound for the zero operators.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.KitaevGeometricLemmaTests

open MathlibExt.Analysis.InnerProductSpace.KitaevGeometricLemma

/-- The cosine against the zero subspace is zero. -/
theorem subspaceCos_bot_left
    (M : Submodule ℂ (EuclideanSpace ℂ (Fin 2))) :
    subspaceCos (⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))) M = 0 := by
  unfold subspaceCos
  rw [Submodule.starProjection_bot]
  simp

/-- The angle against the zero subspace is `π / 2`. -/
theorem subspaceAngle_bot_left
    (M : Submodule ℂ (EuclideanSpace ℂ (Fin 2))) :
    subspaceAngle (⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))) M =
      Real.pi / 2 := by
  unfold subspaceAngle
  rw [subspaceCos_bot_left, Real.arccos_zero]

/-- The cosine of the whole space with itself is one. -/
theorem subspaceCos_top_top :
    subspaceCos (⊤ : Submodule ℂ ℂ) (⊤ : Submodule ℂ ℂ) = 1 := by
  unfold subspaceCos
  rw [Submodule.starProjection_top]
  simp

/-- For two copies of the identity operator on `ℂ`, Kitaev's bound is
the identity operator. -/
theorem identity_geometric_bound :
    (1 : ℂ) • (1 : ℂ →ₗ[ℂ] ℂ) ≤
      (1 : ℂ →ₗ[ℂ] ℂ) + (1 : ℂ →ₗ[ℂ] ℂ) := by
  have hA : (1 : ℂ →ₗ[ℂ] ℂ).IsPositive := LinearMap.isPositive_one
  have hB : (1 : ℂ →ₗ[ℂ] ℂ).IsPositive := LinearMap.isPositive_one
  have hv : 0 ≤ (1 : ℝ) := zero_le_one
  have hgap1 : ∀ μ : ℂ,
      Module.End.HasEigenvalue (1 : ℂ →ₗ[ℂ] ℂ) μ →
        μ = 0 ∨ (1 : ℝ) ≤ RCLike.re μ := by
    intro μ hμ
    obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
    have hx_ne : x ≠ 0 := (Module.End.hasEigenvector_iff.mp hx).2
    have hx_eq : (1 : ℂ →ₗ[ℂ] ℂ) x = μ • x :=
      Module.End.HasEigenvector.apply_eq_smul hx
    rw [Module.End.one_apply] at hx_eq
    have hsub : (μ - 1) • x = 0 := by
      rw [sub_smul, one_smul, ← hx_eq, sub_self]
    have h_or : μ - 1 = 0 ∨ x = 0 := smul_eq_zero.mp hsub
    have hmu1 : μ = 1 := by
      rcases h_or with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hx_ne
    right
    rw [hmu1]
    simp
  have hker : LinearMap.ker (1 : ℂ →ₗ[ℂ] ℂ) = ⊥ := by
    rw [Module.End.one_eq_id]
    exact LinearMap.ker_id
  have hdisj : Disjoint (LinearMap.ker (1 : ℂ →ₗ[ℂ] ℂ))
      (LinearMap.ker (1 : ℂ →ₗ[ℂ] ℂ)) := by
    rw [hker]
    exact disjoint_bot_left
  have hmain := kitaev_geometric_lemma hA hB hv hgap1 hgap1 hdisj
  have hcos0 : subspaceCos (LinearMap.ker (1 : ℂ →ₗ[ℂ] ℂ))
      (LinearMap.ker (1 : ℂ →ₗ[ℂ] ℂ)) = 0 := by
    rw [hker]
    unfold subspaceCos
    rw [Submodule.starProjection_bot]
    simp
  have hang : subspaceAngle (LinearMap.ker (1 : ℂ →ₗ[ℂ] ℂ))
      (LinearMap.ker (1 : ℂ →ₗ[ℂ] ℂ)) = Real.pi / 2 := by
    unfold subspaceAngle
    rw [hcos0, Real.arccos_zero]
  have hsin : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 :=
    Real.sin_pi_div_four
  have hsq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hbound_eq : 2 * (1 : ℝ) * Real.sin (Real.pi / 2 / 2) ^ 2 =
      1 := by
    have hpi : Real.pi / 2 / 2 = Real.pi / 4 := by ring
    rw [hpi, hsin, hsq]
    ring
  rw [hang] at hmain
  have hcast : ((((2 * (1 : ℝ) *
      Real.sin (Real.pi / 2 / 2) ^ 2 : ℝ)) : ℂ)) = (1 : ℂ) := by
    rw [hbound_eq]
    simp
  simp only [hbound_eq, hcast] at hmain
  exact hmain

/-- Equal zero operators have a common kernel vector, so no positive
scalar lower bound is possible. -/
theorem no_positive_bound_zero_operators :
    ¬ ((1 : ℂ) • (1 : ℂ →ₗ[ℂ] ℂ) ≤
      (0 : ℂ →ₗ[ℂ] ℂ) + (0 : ℂ →ₗ[ℂ] ℂ)) := by
  have hc : 0 < (1 : ℝ) := by norm_num
  have hx : (1 : ℂ) ≠ 0 := one_ne_zero
  have hxker : (1 : ℂ) ∈
      LinearMap.ker (0 : ℂ →ₗ[ℂ] ℂ) ⊓
        LinearMap.ker (0 : ℂ →ₗ[ℂ] ℂ) := by
    simp
  have hmain := not_pos_smul_one_le_of_exists_mem_ker_inf
    hc hx hxker
  simpa using hmain

#print axioms subspaceCos_nonneg
#print axioms subspaceCos_le_one
#print axioms norm_inner_le_subspaceCos_mul_norm
#print axioms norm_sq_starProjection_add_norm_sq_starProjection_le
#print axioms rayleighForm_ge_of_mem_ker_orthogonal
#print axioms kitaev_geometric_quadratic
#print axioms kitaev_geometric_lemma
#print axioms kitaev_geometric_eigenvalue_ge
#print axioms not_pos_smul_one_le_of_exists_mem_ker_inf

end MathlibExtTest.Analysis.InnerProductSpace.KitaevGeometricLemmaTests
