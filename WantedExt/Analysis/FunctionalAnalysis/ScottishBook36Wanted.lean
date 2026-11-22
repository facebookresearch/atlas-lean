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
In every infinite-dimensional real Hilbert space, the closed unit ball retracts
onto the unit sphere: there is a continuous map from the ball onto the sphere
fixing every point of the sphere. Source: S. Ulam, Problem 36 of the Scottish
Book, asking whether there is a retraction of the closed unit ball of Hilbert
space onto its boundary; the answer is affirmative, see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015), and the
2026 survey "90+ years of the Scottish Book" (arXiv:2603.27867), which notes
that the unit sphere of a Hilbert space is homeomorphic to the whole space.
In finite dimensions this is false by the Brouwer no-retraction theorem, so
the infinite-dimensional hypothesis is essential.
Stated in ambient form: `f` restricted to the closed ball is the retraction,
and conversely a ball retraction extends by radial projection outside the ball,
`f x = r (x / max 1 ‖x‖)`.
-/
theorem_wanted hilbertBallRetractsOntoSphere :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ¬ Module.Finite ℝ E →
      ∃ f : E → E, Continuous f ∧ (∀ x, f x ∈ Metric.sphere (0 : E) 1) ∧
        ∀ x ∈ Metric.sphere (0 : E) 1, f x = x

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook36Wanted
