/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook51

open Set
open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook51Wanted

/-- Unpack the sequence counterexample into an actual uncountable system. -/
example : ∃ S : Set (ℕ → ℝ),
    (∀ f ∈ S, f ≠ 0) ∧
    (∀ f ∈ S, ∀ g ∈ S, f ≠ g →
      Summable (fun n => f n * g n) ∧ ∑' n, f n * g n = 0) ∧
    ¬ S.Countable := by
  classical
  by_contra h
  apply orthogonal_systems_not_necessarily_countable.1
  intro S hne hpair
  by_contra hn
  exact h ⟨S, hne, hpair, hn⟩

/-- The second counterexample uses the original almost-everywhere conditions. -/
example : ¬ FunctionSystemsAreCountable := orthogonal_systems_not_necessarily_countable.2
