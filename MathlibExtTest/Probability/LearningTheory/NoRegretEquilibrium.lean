/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.NoRegretEquilibrium
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: the averaging lemma instantiates on one
round, where the average strategy is the single strategy. -/
example (A : Fin 1 → Fin 1 → ℝ) (p : Fin 1 → Fin 1 → ℝ)
    (y : Fin 1 → ℝ) :
    mixedPayoff A (avgStrat p) y =
      (∑ t, mixedPayoff A (p t) y) / (1 : ℕ) :=
  mixedPayoff_avg_left A p y (by norm_num)
