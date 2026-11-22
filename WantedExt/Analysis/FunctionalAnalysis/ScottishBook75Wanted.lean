/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook75Wanted

/-- Mazur's Problem 75 from the Scottish Book, in the general
Banach-space form for scalar-valued continuous polynomials of degree
at most two: if such a polynomial `W` (given by
`W x = B x x + L x + c` for a continuous bilinear map `B`, a continuous
linear functional `L` and a constant `c`) is bounded in some
`ε`-neighbourhood of a set `R`, is `W` then bounded in some
`δ`-neighbourhood of the scaled set `α • R`, for every nonzero scalar
`α`? The linear and constant terms are essential: for a homogeneous
quadratic `W x = B x x` the scaling identity `W (α • x) = α ^ 2 * W x`
transports any such bound to the scaled set, so that case is trivial,
whereas Pestov's counterexample is inhomogeneous. -/
def ScottishBookProblem75Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : Set E) (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] ℝ) (c α : ℝ), α ≠ 0 →
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ x : E, (∃ r ∈ R, dist x r < ε) → |B x x + L x + c| ≤ C) →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ x : E, (∃ r ∈ R, dist x (α • r) < δ) → |B x x + L x + c| ≤ C

/--
Mazur's Problem 75 is false in the general Banach-space form above.
Source: S. Mazur, Problem 75 of the Scottish Book; refuted by
V. Pestov, whose counterexample to Problem 55 is a continuous
scalar-valued inhomogeneous 2-polynomial `W` on `ℓ²`, bounded on an
`ε`-neighbourhood of an unbounded set `R`, but unbounded on
`(1 / 2) R`, hence unbounded on every neighbourhood of `(1 / 2) R`
("Two 1935 questions of Mazur about polynomials in Banach spaces:
a counter-example", 1997, arXiv:funct-an/9705002). Plichko and
Zagorodnyuk gave an independent negative solution ("On automatic
continuity and three problems of 'The Scottish Book' concerning the
boundedness of polynomial functionals", J. Math. Anal. Appl. 220
(1998), 477–494). In the Euclidean case the statement is true, per
typescript Ad 75.
-/
theorem_wanted mazur75_refuted : ¬ ScottishBookProblem75Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook75Wanted
