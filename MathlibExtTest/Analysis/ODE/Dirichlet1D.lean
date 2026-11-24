/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
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

-- Uniqueness identifies a solution of `u'' = 1` with `x (x - 1) / 2` on `[0, 1]`; in particular
-- it takes the value `-1 / 8` at the midpoint.
example {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u ∧ u 0 = 0 ∧ u 1 = 0 ∧
    ∀ x ∈ Set.Ioo 0 1, deriv (deriv u) x = 1) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, u x = x * (x - 1) / 2) ∧ u (1 / 2) = -1 / 8 := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y * (y - 1) / 2) (x - 1 / 2) x := by
    convert ((hasDerivAt_id' x).fun_mul ((hasDerivAt_id' x).sub_const 1)).div_const 2 using 1
    ring
  have hdd : deriv (deriv fun y : ℝ => y * (y - 1) / 2) = fun _ => 1 := by
    rw [funext fun x => (hd x).deriv]
    exact funext fun x => ((hasDerivAt_id' x).sub_const _).deriv
  have key : ∀ x ∈ Set.Icc (0 : ℝ) 1, u x = x * (x - 1) / 2 :=
    dirichlet_1d_unique hu ⟨by fun_prop, by norm_num, by norm_num, fun x _ => by rw [hdd]⟩
  refine ⟨key, ?_⟩
  rw [key (1 / 2) (by norm_num)]
  norm_num

-- A solution of `u'' = 0` with zero boundary values vanishes on the closed interval.
example {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u ∧ u 0 = 0 ∧ u 1 = 0 ∧
    ∀ x ∈ Set.Ioo 0 1, deriv (deriv u) x = 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x = 0 :=
  dirichlet_1d_unique hu ⟨contDiff_const, rfl, rfl, fun x _ => by simp⟩

-- With existence: for a forcing continuous on `[0, 1]`, every solution agrees on `[0, 1]` with
-- the one that `dirichlet_1d_exists` provides.
example {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ u : ℝ → ℝ, (ContDiff ℝ 2 u ∧ u 0 = 0 ∧ u 1 = 0 ∧
      ∀ x ∈ Set.Ioo 0 1, deriv (deriv u) x = f x) ∧
      ∀ v : ℝ → ℝ, (ContDiff ℝ 2 v ∧ v 0 = 0 ∧ v 1 = 0 ∧
        ∀ x ∈ Set.Ioo 0 1, deriv (deriv v) x = f x) → ∀ x ∈ Set.Icc 0 1, v x = u x := by
  obtain ⟨u, hu⟩ := dirichlet_1d_exists hf
  exact ⟨u, hu, fun v hv => dirichlet_1d_unique hv hu⟩
