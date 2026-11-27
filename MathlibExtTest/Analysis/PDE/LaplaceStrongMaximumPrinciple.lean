/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.LaplaceStrongMaximumPrinciple
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for the strong maximum principle

The maximum propagates to an interval endpoint. The principle also applies to the whole
zero-dimensional Euclidean space, whose boundary is empty.
-/

open InnerProductSpace Set
open MathlibExt.Analysis.PDE.LaplaceMeanValueWanted

example {u : ℝ → ℝ} (hu : HarmonicOnNhd u (Ioo (-1) 1)) (hc : ContinuousOn u (Icc (-1) 1))
    (hm : IsMaxOn u (Icc (-1) 1) 0) : u 1 = u 0 := by
  have hcl : closure (Ioo (-1 : ℝ) 1) = Icc (-1) 1 := closure_Ioo (by norm_num)
  apply eqOn_closure_of_isMaxOn_harmonicOnNhd isOpen_Ioo (Metric.isBounded_Ioo _ _)
    (isConnected_Ioo (by norm_num)) hu (hcl ▸ hc) (by norm_num) (hcl ▸ hm)
  rw [hcl]
  norm_num

example (c : ℝ) : ∀ x ∈ closure (univ : Set (EuclideanSpace ℝ (Fin 0))), (fun _ => c) x = c := by
  exact eqOn_closure_of_isMaxOn_harmonicOnNhd isOpen_univ finite_univ.isBounded isConnected_univ
    (harmonicOnNhd_const c) continuousOn_const (mem_univ 0) (fun _ _ => le_rfl)
