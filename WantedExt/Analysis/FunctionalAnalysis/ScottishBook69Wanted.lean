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

/-- **Iterated metric center sets.** Let $p, q$ be points of a pseudometric space $E$ with
distance $d$. The iterated metric center sets $R_n \subseteq E$ of $(p, q)$, for
$n \in \mathbb{N}$, are defined by $R_0 = \{x \in E : d(p, x) + d(x, q) = d(p, q)\}$ and
$R_{n+1} = \{r \in R_n : d(r, x) \le \operatorname{diam}(R_n) / 2 \text{ for all } x \in R_n\}$. -/
noncomputable def metricCenterSets (E : Type*) [PseudoMetricSpace E]
    (p q : E) : ℕ → Set E
  | 0 => {x | dist p x + dist x q = dist p q}
  | (n + 1) =>
    {r ∈ metricCenterSets E p q n |
      ∀ x ∈ metricCenterSets E p q n,
        dist r x ≤ Metric.diam (metricCenterSets E p q n) / 2}

/-- **Metric center of a pair of points.** Let $p, q, c$ be points of a pseudometric space $E$
and let $R_n$, for $n \in \mathbb{N}$, be the iterated metric center sets of $(p, q)$. We say
that $c$ is the metric center of $(p, q)$ when $c \in R_n$ for every $n$, and every point
$y \in E$ with $y \in R_n$ for every $n$ equals $c$. -/
def IsMetricCenter (E : Type*) [PseudoMetricSpace E] (p q c : E) : Prop :=
  (∀ n, c ∈ metricCenterSets E p q n) ∧
  ∀ y, (∀ n, y ∈ metricCenterSets E p q n) → y = c

/-- Mazur and Ulam's Problem 69 from the Scottish Book: is a nonempty complete
metric space `E` in which (1) every pair has exactly one metric center
and (2) for every `p, q` there is exactly one `x` such that `q` is the
metric center of `(p, x)` necessarily isometric to a Banach space? -/
def ScottishBookProblem69Claim : Prop :=
  ∀ (E : Type) [PseudoMetricSpace E] [CompleteSpace E] [Nonempty E],
    (∀ p q : E, ∃! c, IsMetricCenter E p q c) →
    (∀ p q : E, ∃! x, IsMetricCenter E p x q) →
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F)
      (_ : CompleteSpace F), Nonempty (E ≃ᵢ F)

/--
Mazur–Ulam Problem 69 is false: properties (1) and (2) do not
characterize Banach spaces among nonempty metric spaces. Source: S. Mazur and
S. Ulam, Problem 69 of the Scottish Book; typescript Ad 69 records the
negative answer (S. Mazur, December 21, 1936).
-/
theorem_wanted mazurUlam69_refuted : ¬ ScottishBookProblem69Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook69Wanted
