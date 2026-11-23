/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.Stampacchia

@[expose] public section

open scoped InnerProductSpace

namespace MathlibExtTest.Analysis.InnerProductSpace.StampacchiaTests

open Filter Topology
open MathlibExt.Analysis.InnerProductSpace.Stampacchia

noncomputable section

/-- The bilinear form `B u v = 2 * u * v` on `ℝ`, as a continuous bilinear map. -/
private noncomputable def testB : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => (2 * u) • ContinuousLinearMap.id ℝ ℝ
      map_add' := by
        intro a b
        apply ContinuousLinearMap.ext
        intro x
        show 2 * (a + b) * x = 2 * a * x + 2 * b * x
        ring
      map_smul' := by
        intro c a
        apply ContinuousLinearMap.ext
        intro x
        simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    2 (by
      intro u
      show ‖(2 * u) • ContinuousLinearMap.id ℝ ℝ‖ ≤ 2 * ‖u‖
      have h1 : ‖(2 * u) • ContinuousLinearMap.id ℝ ℝ‖ = ‖2 * u‖ := by
        rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
      rw [h1, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.norm_eq_abs])

/-- `testB` applies as `2 * u * v`. -/
private lemma testB_apply (u v : ℝ) : testB u v = 2 * u * v := by
  show ((2 * u) • ContinuousLinearMap.id ℝ ℝ) v = 2 * u * v
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- Coercivity of `A = 2 • id` on `ℝ`. -/
private lemma coercive_two_smul_id : ∀ u : ℝ, 2 * ‖u‖ ^ 2 ≤
    ⟪((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) u, u⟫_ℝ := by
  intro u
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [RCLike.inner_apply]
  simp only [starRingEnd_apply, star_trivial, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg u]

/-- Stampacchia on `[0, 1]` in `ℝ` with `A = 2 • id` and `f = 3`: the solution is `1`. -/
example : ∃ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 ∧
    (∀ v ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ ⟪((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) u - 3, v - u⟫_ℝ) ∧ u = 1 := by
  obtain ⟨u, hu, huniq⟩ := exists_unique_stampacchia (K := Set.Icc (0 : ℝ) 1)
    (Set.nonempty_Icc.mpr (by norm_num))
    isClosed_Icc (convex_Icc 0 1) ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (by norm_num)
    coercive_two_smul_id 3
  refine ⟨u, hu.1, hu.2, ?_⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ v ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ ⟪((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) - 3, v - 1⟫_ℝ) := by
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    intro v hv
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [RCLike.inner_apply]
    simp only [starRingEnd_apply, star_trivial]
    nlinarith [hv.2]
  exact (huniq 1 h1).symm

/-- Surjectivity: `A = 2 • id` on `ℝ` hits `3`, at `u = 3 / 2`. -/
example : ∃ u : ℝ, ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) u = 3 ∧ u = 3 / 2 := by
  obtain ⟨u, hu⟩ := exists_eq_of_coercive ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    (α := 2) (by norm_num) coercive_two_smul_id 3
  refine ⟨u, hu, ?_⟩
  have h : (2 : ℝ) * u = 3 := by
    have h' := hu
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at h'
    exact h'
  linarith

/-- Whole-space case: the variational inequality forces `A u = f`. -/
example : ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (3 / 2 : ℝ) = 3 := by
  apply stampacchia_eq_of_univ _ _ _
  intro v _
  have h0 : ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (3 / 2 : ℝ) - 3 = 0 := by
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    norm_num
  rw [h0]
  simp

/-- Bilinear form on `[0, 1]` in `ℝ`: `B u v = 2 * u * v`, `φ v = 3 * v`; solution `1`. -/
example : ∃ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 ∧
    (∀ v ∈ Set.Icc (0 : ℝ) 1,
      ((3 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (v - u) ≤ testB u (v - u)) ∧ u = 1 := by
  have hcoer : ∀ u : ℝ, 2 * ‖u‖ ^ 2 ≤ testB u u := by
    intro u
    rw [testB_apply]
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg u]
  obtain ⟨u, hu, huniq⟩ := exists_unique_stampacchia_bilinear (K := Set.Icc (0 : ℝ) 1)
    (Set.nonempty_Icc.mpr (by norm_num)) isClosed_Icc (convex_Icc 0 1) testB (α := 2)
    (by norm_num) hcoer ((3 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
  refine ⟨u, hu.1, hu.2, ?_⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ v ∈ Set.Icc (0 : ℝ) 1,
        ((3 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (v - 1) ≤ testB 1 (v - 1)) := by
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    intro v hv
    rw [testB_apply]
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    nlinarith [hv.2]
  exact (huniq 1 h1).symm

/-- Obstacle problem on `[0, ∞)` in `ℝ` with `A = id` and `f = -1`: the solution is `0`. -/
example : ∃ u : ℝ, u ∈ Set.Ici (0 : ℝ) ∧
    (∀ v ∈ Set.Ici (0 : ℝ),
      0 ≤ ⟪ContinuousLinearMap.id ℝ ℝ u - (-1 : ℝ), v - u⟫_ℝ) ∧ u = 0 := by
  have hcoer : ∀ u : ℝ, 1 * ‖u‖ ^ 2 ≤
      ⟪ContinuousLinearMap.id ℝ ℝ u, u⟫_ℝ := by
    intro u
    simp [ContinuousLinearMap.id_apply]
  obtain ⟨u, hu, huniq⟩ := exists_unique_stampacchia (K := Set.Ici (0 : ℝ))
    ⟨0, le_refl 0⟩
    isClosed_Ici (convex_Ici 0) (ContinuousLinearMap.id ℝ ℝ) (α := 1) (by norm_num) hcoer (-1)
  refine ⟨u, hu.1, hu.2, ?_⟩
  have h1 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) ∧
      (∀ v ∈ Set.Ici (0 : ℝ),
        0 ≤ ⟪ContinuousLinearMap.id ℝ ℝ (0 : ℝ) - (-1 : ℝ), v - 0⟫_ℝ) := by
    refine ⟨le_refl 0, ?_⟩
    intro v hv
    simp [ContinuousLinearMap.id_apply, RCLike.inner_apply]
    exact hv
  exact (huniq 0 h1).symm

end

end MathlibExtTest.Analysis.InnerProductSpace.StampacchiaTests
