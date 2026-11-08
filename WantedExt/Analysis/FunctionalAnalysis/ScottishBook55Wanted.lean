/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook55Wanted

/-- Mazur's Problem 55 from the Scottish Book, in the general Banach-space
form for scalar-valued 2-polynomials: every continuous 2-polynomial `W`
bounded on an `ε`-neighbourhood of an unbounded set `R` factors as
`W = V ∘ φ` for a univariate polynomial `V` and a first-degree (affine)
polynomial `φ` with `φ(R)` bounded. Here `W x = B x x` for a continuous
bilinear map `B`, and `φ x = L x + c` for a continuous linear functional
`L`. -/
def ScottishBookProblem55Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : Set E) (B : E →L[ℝ] E →L[ℝ] ℝ),
    (∀ M : ℝ, ∃ r ∈ R, M < ‖r‖) →
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ x : E, (∃ r ∈ R, dist x r < ε) → |B x x| ≤ C) →
    ∃ (L : E →L[ℝ] ℝ) (c : ℝ) (V : Polynomial ℝ),
      (∀ x : E, B x x = V.eval (L x + c)) ∧
      ∃ M : ℝ, ∀ r ∈ R, |L r + c| ≤ M

/--
Mazur's Problem 55 is false in the general Banach-space form above: the
factorisation through an affine map with bounded image on `R` fails.
Source: S. Mazur, Problem 55 of the Scottish Book; refuted by V. Pestov,
who constructs a continuous scalar-valued 2-polynomial `W` on the
separable Hilbert space `ℓ²` and an unbounded set `R` such that `W` is
bounded on an `ε`-neighbourhood of `R` but does not factor through any
bounded first-degree polynomial sending `R` to a bounded set
("Two 1935 questions of Mazur about polynomials in Banach spaces:
a counter-example", 1997, arXiv:funct-an/9705002). The same
counterexample refutes Problem 75. In finite dimensions the answer is
positive (Auerbach), so the infinite-dimensional Banach setting is
essential.
-/
theorem_wanted mazur55_refuted : ¬ ScottishBookProblem55Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook55Wanted
