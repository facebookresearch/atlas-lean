/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.ImplicitFunctionExpExample
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Test of the implicit solution along the line `y₁ = 1` -/

open Filter
open scoped Topology
open MathlibExt.Analysis.Calculus.ImplicitFunctionExpExampleWanted

-- On the slice, differentiating the equation at the base point gives u'(-1) + 1 = 0.
example : ∃ u : ℝ → ℝ, u (-1) = 0 ∧ HasDerivAt u (-1) (-1) ∧
    ∀ᶠ t in 𝓝 (-1 : ℝ), u t ^ 2 + Real.exp (u t) + t = 0 := by
  obtain ⟨U, hU, ha, g, hg, hg0, heq⟩ :=
    exists_implicit_function_sq_mul_add_exp_add _ rfl
  let u (t : ℝ) := g (1, t)
  have hslice : DifferentiableAt ℝ (fun t : ℝ => ((1 : ℝ), t)) (-1) := by fun_prop
  have hu : DifferentiableAt ℝ u (-1) := (hg.differentiableAt (hU.mem_nhds ha)).comp _ hslice
  have hzero : (fun t => u t ^ 2 + Real.exp (u t) + t) =ᶠ[𝓝 (-1 : ℝ)] fun _ => 0 := by
    filter_upwards [hslice.continuousAt.preimage_mem_nhds (hU.mem_nhds ha)] with t ht
    simpa [u] using heq (1, t) ht
  have hslope := ((hu.hasDerivAt.pow 2).add hu.hasDerivAt.exp).add (hasDerivAt_id (-1 : ℝ))
  have hd := (hslope.congr_of_eventuallyEq hzero.symm).unique (hasDerivAt_const (-1 : ℝ) 0)
  have hu0 : u (-1) = 0 := hg0
  simp [hu0] at hd
  refine ⟨u, hu0, ?_, hzero⟩
  simpa only [eq_neg_of_add_eq_zero_left hd] using hu.hasDerivAt
