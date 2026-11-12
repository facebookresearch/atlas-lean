/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.EmpiricalDistribution
public import Mathlib.Data.Fintype.Card

import Mathlib.Tactic.NormNum

/-- Computation: in the constant sample, the empirical frequency
of the repeated value is `1` (for `n = 2`). -/
example {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    empFreq (fun _ : Fin 2 => a) a = 1 := by
  simp [empFreq]

/-- Boundary check: the expectation bound instantiates for one
sample on a two-element alphabet. -/
example (p : PMF (Fin 2)) :
    (∑ x : Fin 1 → Fin 2, (∏ i, (p (x i)).toReal) *
      ∑ a, |empFreq x a - (p a).toReal|) ≤
    Real.sqrt (Fintype.card (Fin 2) / ((1 : ℕ) : ℝ)) :=
  empFreq_l1_expectation (n := 1) p (by norm_num)
