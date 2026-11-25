/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Geometry.GoodmanGoodman
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for the Goodman–Goodman circle covering theorem -/

open MathlibExt.Geometry.ErdosProblem1121Wanted Metric Set
open scoped RealInnerProductSpace

namespace MathlibExtTest.Geometry.GoodmanGoodman

-- An empty family has total radius zero in every dimension.
example {d : ℕ} (c : Fin 0 → EuclideanSpace ℝ (Fin d)) (r : Fin 0 → ℝ) :
    ∃ z, (⋃ i, closedBall (c i) (r i)) ⊆ closedBall z 0 := by
  simpa only [Finset.univ_eq_empty, Finset.sum_empty] using
    conjecture_holds.2 c r (fun i ↦ i.elim0) (fun _ _ _ _ ↦ Or.inl fun i ↦ i.elim0)

-- Two disks of radii one and two touch at the origin. Their outer tips are six units apart.
example (u : EuclideanSpace ℝ (Fin 2)) (hu : ‖u‖ = 1) :
    ∃ z, closedBall u 1 ∪ closedBall ((-2 : ℝ) • u) 2 ⊆ closedBall z 3 := by
  let c : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![u, (-2 : ℝ) • u]
  let r : Fin 2 → ℝ := ![1, 2]
  have hr (i) : 0 < r i := by fin_cases i <;> norm_num [r]
  have hzero (i) : 0 ∈ closedBall (c i) (r i) := by
    fin_cases i <;> norm_num [c, r, mem_closedBall, norm_smul, hu]
  have hconn := isPreconnected_iUnion ⟨0, mem_iInter.mpr hzero⟩
    (fun i ↦ isPreconnected_closedBall (x := c i) (r := r i))
  have hcenter (i) : c i ∈ ⋃ j, closedBall (c j) (r j) :=
    mem_iUnion.mpr ⟨i, mem_closedBall_self (hr i).le⟩
  obtain ⟨z, hz⟩ := conjecture_holds.1 c r hr fun v t _ hmiss ↦ by
    by_contra! h
    obtain ⟨⟨i, hi⟩, j, hj⟩ := h
    have hcont : Continuous (fun p ↦ ⟪v, p⟫) := continuous_const.inner continuous_id
    obtain ⟨p, hp, heq⟩ := hconn.intermediate_value (hcenter j) (hcenter i)
      hcont.continuousOn (show t ∈ Icc ⟪v, c j⟫ ⟪v, c i⟫ from ⟨hj, hi⟩)
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    exact hmiss k p hk heq
  refine ⟨z, ?_⟩
  norm_num [c, r, Fin.sum_univ_two] at hz ⊢
  exact hz

end MathlibExtTest.Geometry.GoodmanGoodman
