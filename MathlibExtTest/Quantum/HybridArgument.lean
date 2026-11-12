/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.HybridArgument
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: constant distribution sequences have zero
distinguishing advantage on any event. -/
example (p : PMF Bool) (E : Finset Bool) (k : ℕ) :
    |(∑ a ∈ E, (p a).toReal) - (∑ a ∈ E, (p a).toReal)| ≤ k * (0 : ℝ) := by
  have h := hybrid_argument (fun _ => p) E (ε := 0)
    (fun i => by simp) k
  simpa using h
