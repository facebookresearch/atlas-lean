/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook144Wanted

/-- **Scottish Book Problem 144 (Mazur–Ulam), as a claim.** For every separable real Banach
space $E$, with unit sphere $K = \{x \in E : \|x\| = 1\}$, there is an injective map
$f \colon K \to [0, 1]$ such that for every nonempty open subset $U$ of $K$ the image $f(U)$ has
positive Lebesgue outer measure.

Mazur and Ulam ask, in a separable Banach space, whether such a map exists. -/
def ScottishBookProblem144Claim : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E],
    ∃ f : ↥(Metric.sphere (0 : E) 1) → ℝ,
      Function.Injective f ∧ (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (U : Set ↥(Metric.sphere (0 : E) 1)), IsOpen U → U.Nonempty →
        0 < MeasureTheory.volume (f '' U)

/--
**Scottish Book Problem 144 is false as stated.** The Scottish Book Problem 144 claim fails: some
separable real Banach space $E$ admits no injective map $f$ from its unit sphere $K$ to $[0, 1]$
such that the image under $f$ of every nonempty open subset of $K$ has positive Lebesgue outer
measure.

For example, take $E = \mathbb{R}$: its unit sphere is $\{-1, 1\}$, so $U = \{1\}$ is a nonempty
open subset of $K$, and its image under any $f$ is a single point, of measure zero. The source
contains no dimension restriction (it says "infinite-dimensional" explicitly when it means it,
e.g. Problem 7), so none is added here.

Source: S. Mazur and S. Ulam, Problem 144 of the Scottish Book,
typescript p. 63 (printed), PDF p. 66; see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted mazurUlam144_refuted : ¬ ScottishBookProblem144Claim

end MathlibExt.Analysis.ScottishBook144Wanted
