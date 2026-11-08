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

/-- Ulam's Problem 167 from the Scottish Book, in its original form: for the
surface `S` of the unit sphere in a Hilbert space, finitely many continuous
real functions `f i` on `S`, and a continuous map `T` of `S` into itself,
there is a point `p0` with `f i (T p0) = f i p0` for every `i`. -/
def ScottishBookProblem167Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
    ¬ Module.Finite ℝ E →
    ∀ (n : ℕ) (f : Fin n → ↥(Metric.sphere (0 : E) 1) → ℝ)
      (T : ↥(Metric.sphere (0 : E) 1) → ↥(Metric.sphere (0 : E) 1)),
      Continuous T → (∀ i, Continuous (f i)) →
      ∃ p0 : ↥(Metric.sphere (0 : E) 1), ∀ i, f i (T p0) = f i p0

/--
Ulam's Problem 167 is false: the claim above fails already for one function.
Source: S. Ulam, Problem 167 of the Scottish Book; refuted via V. Klee's
homeomorphism of the Hilbert sphere onto the whole Hilbert space: composing
that homeomorphism with a translation gives a continuous `T` and a continuous
`f` with no point `p0` satisfying `f (T p0) = f p0`. See the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted ulam167_refuted : ¬ ScottishBookProblem167Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook167Wanted
