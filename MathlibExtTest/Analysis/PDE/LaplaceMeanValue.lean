/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.LaplaceMeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Tests for the harmonic mean-value property

The identity on the line has the mean-value property on translated intervals.
The square function fails the converse's hypothesis, and positive-radius balls also work in
dimension zero.
-/

open InnerProductSpace Metric MeasureTheory Set Laplacian
open MathlibExt.Analysis.PDE.LaplaceMeanValueWanted
open scoped Topology

example (a : ℝ) {r : ℝ} (hr : 0 < r) : ⨍ y in closedBall a r, y = a := by
  apply (harmonicOnNhd_iff_forall_average_closedBall isOpen_univ
    (u := fun y : ℝ ↦ y) contDiffOn_id).mp _ a r hr (subset_univ _)
  intro x _
  refine ⟨contDiffAt_id, Filter.Eventually.of_forall fun y ↦ ?_⟩
  change Δ (fun z : ℝ ↦ z) y = 0
  simp [laplacian_eq_iteratedDeriv_real, iteratedDeriv_fun_id]

example : ¬ ∀ a : ℝ, ∀ r : ℝ, 0 < r → ⨍ y in closedBall a r, y ^ 2 = a ^ 2 := by
  intro hm
  have hh := (harmonicOnNhd_iff_forall_average_closedBall isOpen_univ
    (u := fun y : ℝ ↦ y ^ 2) (by fun_prop)).mpr (fun a r hr _ ↦ hm a r hr)
  have hz := (hh 0 (mem_univ _)).2.self_of_nhds
  change Δ (fun y : ℝ ↦ y ^ 2) 0 = 0 at hz
  norm_num [laplacian_eq_iteratedDeriv_real, iteratedDeriv_fun_pow_zero] at hz

example (u : EuclideanSpace ℝ (Fin 0) → ℝ) :
    ⨍ y in closedBall 0 1, u y = u 0 := by
  have he : u = fun _ ↦ u 0 := funext fun x ↦ congrArg u (Subsingleton.elim x 0)
  rw [he]
  exact (harmonicOnNhd_iff_forall_average_closedBall isOpen_univ contDiffOn_const).mp
    (harmonicOnNhd_const (u 0)) 0 1 zero_lt_one (subset_univ _)
