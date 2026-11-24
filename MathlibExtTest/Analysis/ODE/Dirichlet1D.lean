/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.Dirichlet1D

open MathlibExt.Analysis.Distribution.Dirichlet1DWanted

-- The forcing jumps at 1 but is continuous on the closed interval.
example : ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ u 0 = 0 ∧ u 1 = 0 ∧
    deriv (deriv u) (1 / 2) = 1 / 2 := by
  let f : ℝ → ℝ := (Set.Icc 0 1).indicator id
  have hf : ContinuousOn f (Set.Icc 0 1) :=
    continuous_id.continuousOn.congr fun _ hx => Set.indicator_of_mem hx id
  obtain ⟨u, hu, hu0, hu1, hderiv⟩ := dirichlet_1d_exists hf
  have hx : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  refine ⟨u, hu, hu0, hu1, (hderiv _ hx).trans ?_⟩
  exact Set.indicator_of_mem (Set.Ioo_subset_Icc_self hx) id
