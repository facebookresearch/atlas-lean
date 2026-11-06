/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook167Wanted

/-- **Scottish Book Problem 167.** Ulam's claim that for every infinite-dimensional real Hilbert
space $H$ with unit sphere $S = \{p \in H : \|p\| = 1\}$, every $n \in \mathbb{N}$, all
continuous functions $f_1, \dots, f_n : S \to \mathbb{R}$ and every continuous map
$T : S \to S$, there is a point $p_0 \in S$ with $f_i(T(p_0)) = f_i(p_0)$ for every $i$. -/
def ScottishBookProblem167Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
    ¬ Module.Finite ℝ E →
    ∀ (n : ℕ) (f : Fin n → ↥(Metric.sphere (0 : E) 1) → ℝ)
      (T : ↥(Metric.sphere (0 : E) 1) → ↥(Metric.sphere (0 : E) 1)),
      Continuous T → (∀ i, Continuous (f i)) →
      ∃ p0 : ↥(Metric.sphere (0 : E) 1), ∀ i, f i (T p0) = f i p0

/--
**Negative answer to Scottish Book Problem 167.** Ulam's claim in Problem 167 is false: there
are an infinite-dimensional real Hilbert space $H$ with unit sphere $S$, a number
$n \in \mathbb{N}$, continuous functions $f_1, \dots, f_n : S \to \mathbb{R}$ and a continuous map
$T : S \to S$ such that no point $p_0 \in S$ satisfies $f_i(T(p_0)) = f_i(p_0)$ for every $i$.

The claim fails already for one function.

Source: S. Ulam, Problem 167 of the Scottish Book; refuted via V. Klee's
homeomorphism of the Hilbert sphere onto the whole Hilbert space: composing
that homeomorphism with a translation gives a continuous `T` and a continuous
`f` with no point `p0` satisfying `f (T p0) = f p0`. See the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted ulam167_refuted : ¬ ScottishBookProblem167Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook167Wanted
