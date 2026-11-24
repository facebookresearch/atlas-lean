/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.ErdosProblem907
import Mathlib.Tactic.Linarith

/-! # Decomposing a quadratic translated by an arbitrary additive function -/

open MathlibExt.Analysis.ErdosProblem907Wanted

-- The additive summand can be discontinuous. Every decomposition must put the offset
-- at zero into the continuous summand.
example (b : ℝ →+ ℝ) :
    ∃ g a : ℝ → ℝ, Continuous g ∧ (∀ x y, a (x + y) = a x + a y) ∧
      (fun x => x ^ 2 + 1 + b x) = g + a ∧ g 0 = 1 := by
  have hdiff (h : ℝ) : Continuous fun x => ((x + h) ^ 2 + 1 + b (x + h)) -
      (x ^ 2 + 1 + b x) := by
    have eqn (x : ℝ) : ((x + h) ^ 2 + 1 + b (x + h)) - (x ^ 2 + 1 + b x) =
        (x + h) ^ 2 - x ^ 2 + b h := by
      rw [map_add]
      abel
    simp_rw [eqn]
    fun_prop
  obtain ⟨g, a, hg, ha, he⟩ := conjecture_holds (fun x => x ^ 2 + 1 + b x) (fun h _ => hdiff h)
  refine ⟨g, a, hg, ha, he, ?_⟩
  have hadd := ha 0 0
  have hzero := congrFun he 0
  simp only [zero_add] at hadd
  simp at hzero
  linarith
