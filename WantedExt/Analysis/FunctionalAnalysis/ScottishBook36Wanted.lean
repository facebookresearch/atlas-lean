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

universe u

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook36Wanted

/--
**Retraction onto the unit sphere of Hilbert space.** Let $E$ be an infinite-dimensional real
Hilbert space and let $S = \{x \in E : \|x\| = 1\}$ be its unit sphere. Then there is a
continuous map $f : E \to E$ such that $f(x) \in S$ for every $x \in E$ and $f(x) = x$ for every
$x \in S$.

Restricting $f$ to the closed unit ball gives a retraction of the ball onto $S$; conversely, a
retraction $r$ of the closed unit ball onto $S$ extends to all of $E$ by
$f(x) = r(x / \max(1, \|x\|))$. In finite dimensions no such map exists, by the Brouwer
no-retraction theorem, so the infinite-dimensional hypothesis is essential.

Source: S. Ulam, Problem 36 of the Scottish
Book, asking whether there is a retraction of the closed unit ball of Hilbert
space onto its boundary; the answer is affirmative, see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015), and the
2026 survey "90+ years of the Scottish Book" (arXiv:2603.27867), which notes
that the unit sphere of a Hilbert space is homeomorphic to the whole space.
-/
theorem_wanted hilbertBallRetractsOntoSphere :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ¬ Module.Finite ℝ E →
      ∃ f : E → E, Continuous f ∧ (∀ x, f x ∈ Metric.sphere (0 : E) 1) ∧
        ∀ x ∈ Metric.sphere (0 : E) 1, f x = x

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook36Wanted
