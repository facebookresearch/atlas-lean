/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2TriangleProjection

/-! Genuine image and scaled-projection identities for the seventh physical triangle. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual physical root outer operator is twice the genuine seventh matrix projection. -/
theorem leechSeventhTriangle_outer_linear :
    leechSeventhRootOuterSum (leechSeventhE8A2PlaneRoots 537) =
      (2 : ℝ) • Matrix.toLin' generatedSeventhPlaneSupport := by
  rw [← map_smul, ← leechSeventhTriangle_outer_matrix]
  apply LinearMap.ext
  intro x
  ext i
  suffices h :
      (∑ j : Fin 3, ∑ k : Fin 24, leechSeventhE8A2PlaneRoots 537 j k *
        (x k * leechSeventhE8A2PlaneRoots 537 j i)) =
      ∑ j : Fin 3, ∑ k : Fin 24, leechSeventhE8A2PlaneRoots 537 j i *
        (leechSeventhE8A2PlaneRoots 537 j k * x k) by
    simpa [leechSeventhRootOuterSum, Matrix.mulVec, Matrix.vecMulVec,
      dotProduct, Finset.sum_mul, mul_assoc] using h
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The genuine root outer operator has exactly the actual triangle span as its image. -/
theorem leechSeventhTriangle_outer_range :
    LinearMap.range (leechSeventhRootOuterSum (leechSeventhE8A2PlaneRoots 537)) =
      leechSeventhE8A2Plane 537 := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact leechSeventhRootOuterSum_mem _ y
  · intro x hx
    refine ⟨(6 : ℝ)⁻¹ • x, ?_⟩
    rw [map_smul, (leechSeventhE8A2Plane_mem_iff 537 x).mp hx, smul_smul]
    norm_num

/-- The original seventh scaled projection has exactly the genuine intrinsic triangle as image. -/
theorem leechSeventhTriangle_projection_range :
    LinearMap.range (Matrix.toLin' generatedSeventhPlaneSupport) =
      leechSeventhE8A2Plane 537 := by
  rw [← LinearMap.range_smul (Matrix.toLin' generatedSeventhPlaneSupport) 2 (by norm_num),
    ← leechSeventhTriangle_outer_linear, leechSeventhTriangle_outer_range]

/-- The genuine seventh triangle matrix is symmetric. -/
theorem leechSeventhTriangle_projection_symm :
    generatedSeventhPlaneSupport.transpose = generatedSeventhPlaneSupport := by
  ext i j
  change (generatedSeventhPlaneNumerator j i : ℝ) =
    (generatedSeventhPlaneNumerator i j : ℝ)
  by_cases h : i = j
  · subst j
    rfl
  · by_cases hi : generatedSeventhTriangle i <;>
      by_cases hj : generatedSeventhTriangle j <;>
      simp [generatedSeventhPlaneNumerator, hi, hj, h, Ne.symm h]

/-- The original seventh triangle matrix squares to three times itself. -/
theorem leechSeventhTriangle_projection_square :
    generatedSeventhPlaneSupport * generatedSeventhPlaneSupport =
      (3 : ℝ) • generatedSeventhPlaneSupport := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (generatedSeventhPlaneSupport * generatedSeventhPlaneSupport) *ᵥ x =
    ((3 : ℝ) • generatedSeventhPlaneSupport) *ᵥ x
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  have hx : generatedSeventhPlaneSupport *ᵥ x ∈ leechSeventhE8A2Plane 537 := by
    rw [← leechSeventhTriangle_projection_range]
    exact LinearMap.mem_range_self _ x
  have h := (leechSeventhE8A2Plane_mem_iff 537 _).mp hx
  rw [leechSeventhTriangle_outer_linear, LinearMap.smul_apply] at h
  ext i
  have hi := congrFun h i
  change 2 * (generatedSeventhPlaneSupport *ᵥ (generatedSeventhPlaneSupport *ᵥ x)) i =
    6 * (generatedSeventhPlaneSupport *ᵥ x) i at hi
  change (generatedSeventhPlaneSupport *ᵥ (generatedSeventhPlaneSupport *ᵥ x)) i =
    3 * (generatedSeventhPlaneSupport *ᵥ x) i
  linarith

/-- Fixing the actual seventh triangle projection is equivalent to fixing its genuine real plane. -/
theorem leechSeventhTriangle_projection_fixed_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g generatedSeventhPlaneSupport = generatedSeventhPlaneSupport ↔
      (leechSeventhE8A2Plane 537).map g.val.toLinearMap = leechSeventhE8A2Plane 537 := by
  simpa only [leechSeventhTriangle_projection_range] using
    leechSeventh_scaledProjection_fixed_iff g generatedSeventhPlaneSupport 3
      (by norm_num) leechSeventhTriangle_projection_symm leechSeventhTriangle_projection_square

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
