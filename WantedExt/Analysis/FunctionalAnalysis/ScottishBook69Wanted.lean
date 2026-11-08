/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook69Wanted

/-- The iterated sets defining the metric center of a pair `(p, q)`:
`R 0` is the set of points `x` with `px + xq = pq`, and `R (n + 1)` is
the set of points `r` in `R n` whose distance to every point of `R n`
is at most half the diameter of `R n`. -/
noncomputable def metricCenterSets (E : Type*) [PseudoMetricSpace E]
    (p q : E) : ℕ → Set E
  | 0 => {x | dist p x + dist x q = dist p q}
  | (n + 1) =>
    {r ∈ metricCenterSets E p q n |
      ∀ x ∈ metricCenterSets E p q n,
        dist r x ≤ Metric.diam (metricCenterSets E p q n) / 2}

/-- `c` is the metric center of the pair `(p, q)`: it lies in every
iterated set, and it is the only point that does. -/
def IsMetricCenter (E : Type*) [PseudoMetricSpace E] (p q c : E) : Prop :=
  (∀ n, c ∈ metricCenterSets E p q n) ∧
  ∀ y, (∀ n, y ∈ metricCenterSets E p q n) → y = c

/-- Mazur and Ulam's Problem 69 from the Scottish Book: is a complete
metric space `E` in which (1) every pair has exactly one metric center
and (2) for every `p, q` there is exactly one `x` such that `q` is the
metric center of `(p, x)` necessarily isometric to a Banach space? -/
def ScottishBookProblem69Claim : Prop :=
  ∀ (E : Type) [PseudoMetricSpace E] [CompleteSpace E],
    (∀ p q : E, ∃! c, IsMetricCenter E p q c) →
    (∀ p q : E, ∃! x, IsMetricCenter E p x q) →
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F)
      (_ : CompleteSpace F), Nonempty (E ≃ᵢ F)

/--
Mazur–Ulam Problem 69 is false: properties (1) and (2) do not
characterize Banach spaces among metric spaces. Source: S. Mazur and
S. Ulam, Problem 69 of the Scottish Book; typescript Ad 69 records the
negative answer (S. Mazur, December 21, 1936).
-/
theorem_wanted mazurUlam69_refuted : ¬ ScottishBookProblem69Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook69Wanted
