/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 845
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Basic
public import MathlibExt.Data.Set.Density

@[expose] public section

open Filter
open scoped Topology

namespace MathlibExt.NumberTheory.ErdosProblem845Wanted

/-! Source record `FC-ErdosProblem845`, ported from FormalConjectures
`ErdosProblems/845.lean` and checked against erdosproblems.com/845.
`Set.partialDensity` and `Set.HasDensity` are reused from `MathlibExt.Data.Set.Density`.
The source proposition is preserved; its external disproof by van Doorn and
Everts (`C = 6`) and a pinned external Lean proof are recorded in the
registry. This module states the proposition but does not refute it. -/

/-- Smooth `2^k 3^l` subset sums have density zero. -/
def conjecture : Prop :=
  ∀ (C : ℝ), 0 < C →
    let f : ℕ × ℕ → ℕ := fun (k, l) ↦ 2 ^ k * 3 ^ l
    { ∑ x ∈ B, f x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty)
      (_hB : B.sup f ≤ C * B.inf' h f) }.HasDensity 0

/--
Resolved false: Resolved false externally by Wouter van Doorn and Anneroos R. F. Everts, who
obtain a counterexample at C = 6. This repository records the statement, not a proof. Source:
Wouter van Doorn and Anneroos R. F. Everts, Smooth sums with small spacings, arXiv:2511.04585v1
(2025), https://arxiv.org/abs/2511.04585v1. Moved from
`OpenConjectures/NumberTheory/ErdosProblem845`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem845Wanted
