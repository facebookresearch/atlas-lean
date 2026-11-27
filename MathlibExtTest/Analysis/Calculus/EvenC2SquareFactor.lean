/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.EvenC2SquareFactor
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set MathlibExt.Analysis.Calculus.EvenC2SquareFactorWanted

-- This example samples the factor at zero, at the square of a negative input, and at one.
example : ∃ g : ℝ → ℝ, ContDiffOn ℝ 1 g (Icc 0 1) ∧
    g 0 = 0 ∧ g (1 / 4) = 5 / 16 ∧ g 1 = 2 := by
  let f (x : ℝ) := x ^ 2 + x ^ 4
  have hf : ContDiff ℝ 2 f := by
    dsimp [f]
    fun_prop
  have he : ∀ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → f x = f (-x) := by
    intro x _
    dsimp [f]
    ring
  obtain ⟨g, hg, hre⟩ := exists_contDiffOn_comp_sq_of_even 1 (by norm_num) f hf.contDiffOn he
  have h0 := hre 0 (by norm_num : (0 : ℝ) ∈ Icc (-1) 1)
  have hn := hre (-1 / 2) (by norm_num : (-1 / 2 : ℝ) ∈ Icc (-1) 1)
  have h1 := hre 1 (by norm_num : (1 : ℝ) ∈ Icc (-1) 1)
  norm_num [f] at h0 hn h1
  exact ⟨g, by simpa only [one_pow] using hg, h0.symm, hn.symm, h1.symm⟩
