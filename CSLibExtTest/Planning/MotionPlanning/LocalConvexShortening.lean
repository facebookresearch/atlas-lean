/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.LocalConvexShortening
public meta import CSLibExt.Planning.MotionPlanning.LocalConvexShortening

/-!
# Local-convexity shortening tests

Boundary-bend examples in the closed upper half-plane and axiom probes for
`CSLibExt.Planning.MotionPlanning.LocalConvexShortening`.
-/

open Metric Topology

namespace Cslib.Planning.MotionPlanning.PathShortening

/-! ## Tests: boundary bend in the closed upper half-plane -/

def testHalfPlane : Set plane := {p | 0 ≤ p.ofLp 1}

noncomputable def testA : plane := EuclideanSpace.single 0 (-3)
noncomputable def testB : plane := 0
noncomputable def testC : plane := EuclideanSpace.single 1 4

theorem testA_ofLp_0 : testA.ofLp 0 = -3 := by simp [testA, EuclideanSpace.single]
theorem testA_ofLp_1 : testA.ofLp 1 = 0 := by simp [testA, EuclideanSpace.single]
theorem testB_ofLp_0 : testB.ofLp 0 = 0 := by simp [testB]
theorem testB_ofLp_1 : testB.ofLp 1 = 0 := by simp [testB]
theorem testC_ofLp_0 : testC.ofLp 0 = 0 := by simp [testC, EuclideanSpace.single]
theorem testC_ofLp_1 : testC.ofLp 1 = 4 := by simp [testC, EuclideanSpace.single]

theorem test_dist_AC : dist testA testC = 5 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, testA_ofLp_0, testA_ofLp_1,
    testC_ofLp_0, testC_ofLp_1]
  norm_num [Real.dist_eq, Real.sqrt_eq_iff_eq_sq]

theorem test_dist_AB : dist testA testB = 3 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, testA_ofLp_0, testA_ofLp_1,
    testB_ofLp_0, testB_ofLp_1]
  norm_num [Real.dist_eq, Real.sqrt_eq_iff_eq_sq]

theorem test_dist_BC : dist testB testC = 4 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, testB_ofLp_0, testB_ofLp_1,
    testC_ofLp_0, testC_ofLp_1]
  norm_num [Real.dist_eq, Real.sqrt_eq_iff_eq_sq]

theorem test_not_wbtw : ¬ Wbtw ℝ testA testB testC :=
  dist_lt_dist_add_dist_iff.mp (by
    rw [test_dist_AC, test_dist_AB, test_dist_BC]
    norm_num)

theorem testB_not_interior : testB ∉ interior testHalfPlane := by
  intro hmem
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
  obtain ⟨δ, hδpos, hδsub⟩ := hmem
  set e : plane := EuclideanSpace.single 1 (1 : ℝ) with he_def
  have he0 : e.ofLp 0 = 0 := by simp [he_def, EuclideanSpace.single]
  have he1 : e.ofLp 1 = 1 := by simp [he_def, EuclideanSpace.single]
  have enorm : ‖e‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, he0, he1, norm_zero, norm_one]
    norm_num
  set q : plane := testB - (δ / 2) • e with hq_def
  have hq1 : q.ofLp 1 = -(δ / 2) := by
    rw [hq_def, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, testB_ofLp_1, he1]
    ring
  have hq_out : q ∉ testHalfPlane := by
    intro hqin
    have hle : 0 ≤ q.ofLp 1 := hqin
    rw [hq1] at hle
    linarith
  have hdist : dist testB q = δ / 2 := by
    have hsub : testB - q = (δ / 2) • e := by
      rw [hq_def]
      module
    rw [dist_eq_norm, hsub, norm_smul,
      Real.norm_of_nonneg (by linarith : 0 ≤ δ / 2), enorm, mul_one]
  have hq_ball : q ∈ ball testB δ := by
    rw [mem_ball, dist_comm q testB, hdist]
    linarith
  exact hq_out (hδsub hq_ball)

theorem testC_mem : testC ∈ testHalfPlane := by
  show 0 ≤ testC.ofLp 1
  rw [testC_ofLp_1]
  norm_num

theorem test_seg_AB : segment ℝ testA testB ⊆ testHalfPlane := by
  intro x hx
  obtain ⟨u, v, _, _, _, rfl⟩ := hx
  show 0 ≤ (u • testA + v • testB).ofLp 1
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    testA_ofLp_1, testB_ofLp_1]
  simp

theorem test_seg_BC : segment ℝ testB testC ⊆ testHalfPlane := by
  intro x hx
  obtain ⟨u, v, _, hv, _, rfl⟩ := hx
  show 0 ≤ (u • testB + v • testC).ofLp 1
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    testB_ofLp_1, testC_ofLp_1]
  simp only [mul_zero, zero_add]
  exact mul_nonneg hv (by norm_num)

theorem test_feasible : Feasible testHalfPlane [testA, testB, testC] := by
  rw [feasible_cons_cons]
  refine ⟨test_seg_AB, ?_⟩
  rw [feasible_cons_cons]
  exact ⟨test_seg_BC, testC_mem⟩

theorem testHalfPlane_convex : Convex ℝ testHalfPlane := by
  intro x hx y hy t s ht hs _
  have hx' : 0 ≤ x.ofLp 1 := hx
  have hy' : 0 ≤ y.ofLp 1 := hy
  show 0 ≤ (t • x + s • y).ofLp 1
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
  exact add_nonneg (mul_nonneg ht hx') (mul_nonneg hs hy')

theorem test_locally_convex : ∃ U ∈ 𝓝 testB, Convex ℝ (U ∩ testHalfPlane) := by
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  rw [Set.univ_inter]
  exact testHalfPlane_convex

theorem test_instantiation :
    ∀ ε > 0, ∃ a' c', a' ∈ segment ℝ testA testB ∧ c' ∈ segment ℝ testB testC ∧
      dist a' testB < ε ∧ dist c' testB < ε ∧
      Feasible testHalfPlane ([] ++ [testA, a', c', testC] ++ []) ∧
      polyLen ([] ++ [testA, a', c', testC] ++ []) <
        polyLen ([] ++ [testA, testB, testC] ++ []) :=
  local_shortening_of_locally_convex testHalfPlane [] [] testA testB testC test_feasible
    test_locally_convex test_not_wbtw

example (F : Set plane) (l₁ : List plane) (a b c : plane) (l₂ : List plane)
    (h : Feasible F (l₁ ++ [a, b, c] ++ l₂))
    (hconv : ∃ U ∈ 𝓝 b, Convex ℝ (U ∩ F))
    (hb : ¬ Wbtw ℝ a b c) (ε : ℝ) (hε : 0 < ε) :
    ∃ a' c', a' ∈ segment ℝ a b ∧ c' ∈ segment ℝ b c ∧
      dist a' b < ε ∧ dist c' b < ε ∧
      Feasible F (l₁ ++ [a, a', c', c] ++ l₂) ∧
      polyLen (l₁ ++ [a, a', c', c] ++ l₂) < polyLen (l₁ ++ [a, b, c] ++ l₂) :=
  local_shortening_of_locally_convex F l₁ l₂ a b c h hconv hb ε hε

example (F : Set plane) (l₁ l₂ : List plane) (a b c : plane)
    (hfeas : Feasible F (l₁ ++ [a, b, c] ++ l₂))
    (hconv : ∃ U ∈ 𝓝 b, Convex ℝ (U ∩ F))
    (hmin : ∀ l' : List plane, Feasible F l' →
      l'.head? = (l₁ ++ [a, b, c] ++ l₂).head? →
      l'.getLast? = (l₁ ++ [a, b, c] ++ l₂).getLast? →
      polyLen (l₁ ++ [a, b, c] ++ l₂) ≤ polyLen l') :
    Wbtw ℝ a b c :=
  wbtw_of_minimal_of_locally_convex F l₁ l₂ a b c hfeas hconv hmin

#print axioms local_shortening_of_locally_convex
#print axioms wbtw_of_minimal_of_locally_convex

end Cslib.Planning.MotionPlanning.PathShortening
