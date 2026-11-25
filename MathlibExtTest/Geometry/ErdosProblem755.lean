/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Geometry.ErdosProblem755
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Regression tests for the triangle-counting API in dimension six. -/

open MathlibExt.Geometry.ErdosProblem755Wanted
open scoped Finset RealInnerProductSpace

example : conjecture := conjecture_holds

private abbrev Point := EuclideanSpace ℝ (Fin 6)

private noncomputable def v (i : Fin 3) : Point := EuclideanSpace.basisFun (Fin 6) ℝ
  (Fin.castLE (by decide : 3 ≤ 6) i)

private theorem v_dist {i j : Fin 3} (hij : i ≠ j) : dist (v i) (v j) = √2 := by
  have h := (EuclideanSpace.basisFun (Fin 6) ℝ).orthonormal
  have hne : Fin.castLE (by decide : 3 ≤ 6) i ≠ Fin.castLE (by decide : 3 ≤ 6) j :=
    fun e ↦ hij (Fin.ext (congrArg (fun k : Fin 6 ↦ k.val) e))
  rw [dist_eq_norm, ← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), norm_sub_sq_real,
    Real.sq_sqrt (by norm_num)]
  change ‖v i‖ ^ 2 - 2 * ⟪v i, v j⟫ + ‖v j‖ ^ 2 = 2
  unfold v
  rw [h.norm_eq_one, h.norm_eq_one, h.inner_eq_zero hne]
  norm_num

open Classical in
private noncomputable def configuration (r : ℝ) : Finset Point :=
  Finset.univ.image (fun i ↦ r • v i)

private theorem configuration_triangle {r : ℝ} (hr : 0 < r) :
    IsEquilateralTriangle (r * √2) (configuration r) := by
  classical
  have hd (i j : Fin 3) (hij : i ≠ j) : dist (r • v i) (r • v j) = r * √2 := by
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hr.le, ← dist_eq_norm, v_dist hij]
  have hinj : Function.Injective (fun i ↦ r • v i) := by
    intro i j h
    by_contra hn
    have he := hd i j hn
    change r • v i = r • v j at h
    rw [h, dist_self] at he
    exact (mul_pos hr (Real.sqrt_pos_of_pos (by norm_num))).ne he
  refine ⟨by simp [configuration, Finset.card_image_of_injective _ hinj], ?_⟩
  intro p hp q hq hpq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
  exact hd i j (ne_of_apply_ne (fun k : Fin 3 ↦ r • v k) hpq)

example (P : Finset Point) (hP : P.card < 3) :
    unitEquilateralTriangleCount 6 P = 0 ∧ anySizeEquilateralTriangleCount 6 P = 0 := by
  classical
  simp [unitEquilateralTriangleCount, anySizeEquilateralTriangleCount,
    Finset.powersetCard_eq_empty.mpr hP]

example : IsEquilateralTriangle (√2) (configuration 1) := by
  simpa using configuration_triangle (r := 1) (by norm_num)

-- The three orthogonal coordinate vectors give one nonunit equilateral triangle.
example : anySizeEquilateralTriangleCount 6 (configuration 1) = 1 ∧
    unitEquilateralTriangleCount 6 (configuration 1) = 0 := by
  classical
  have hT : IsEquilateralTriangle (√2) (configuration 1) := by
    simpa using configuration_triangle (r := 1) (by norm_num)
  have hcard : (configuration 1).card = 3 := hT.1
  have hp : (configuration 1).powersetCard 3 = {configuration 1} :=
    hcard ▸ Finset.powersetCard_self (configuration 1)
  have ha : IsAnySizeEquilateralTriangle (configuration 1) :=
    ⟨√2, Real.sqrt_pos_of_pos (by norm_num), hT⟩
  have hnu : ¬ IsUnitEquilateralTriangle (configuration 1) := by
    intro hu
    have hv (i : Fin 3) : v i ∈ configuration 1 := by
      unfold configuration
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, one_smul ℝ (v i)⟩
    have hn : v 0 ≠ v 1 := by
      intro he
      have hd := v_dist (i := 0) (j := 1) (by decide)
      rw [he, dist_self] at hd
      exact (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)).ne hd
    have he := hu.2 (v 0) (hv 0) (v 1) (hv 1) hn
    rw [v_dist (by decide)] at he
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp [anySizeEquilateralTriangleCount, unitEquilateralTriangleCount, Finset.filter_singleton,
    hp, ha, hnu]

-- Rescaling the same geometric configuration yields a unit triangle with count one.
example : unitEquilateralTriangleCount 6 (configuration (√2)⁻¹) = 1 := by
  classical
  have hpos : 0 < √(2 : ℝ) := Real.sqrt_pos_of_pos (by norm_num)
  have hu : IsUnitEquilateralTriangle (configuration (√2)⁻¹) := by
    simpa [IsUnitEquilateralTriangle, inv_mul_cancel₀ hpos.ne'] using
      configuration_triangle (inv_pos.mpr hpos)
  have hcard : (configuration (√2)⁻¹).card = 3 := hu.1
  have hp : (configuration (√2)⁻¹).powersetCard 3 = {configuration (√2)⁻¹} :=
    hcard ▸ Finset.powersetCard_self (configuration (√2)⁻¹)
  simp [unitEquilateralTriangleCount, Finset.filter_singleton, hp, hu]
