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

/-- **Mazur's factorisation claim (Scottish Book Problem 55).** The claim that for every real
Banach space $E$, every unbounded set $R \subseteq E$ and every continuous bilinear form
$B : E \times E \to \mathbb{R}$, if the quadratic form $W(x) = B(x, x)$ is bounded on the set
of points at distance less than $\varepsilon$ from $R$ for some $\varepsilon > 0$, then there
are a continuous linear functional $L : E \to \mathbb{R}$, a constant $c \in \mathbb{R}$ and a
real polynomial $V$ such that $W(x) = V(L(x) + c)$ for all $x \in E$ and $|L(r) + c|$ is
bounded for $r \in R$.

This is Mazur's question in the general Banach-space form for scalar-valued 2-polynomials: $W$
factors as $V \circ \varphi$ through the first-degree polynomial $\varphi(x) = L(x) + c$, which
maps $R$ to a bounded set. -/
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
**Mazur's Problem 55 has a negative answer.** The factorisation claim of Scottish Book
Problem 55 is false: there are a real Banach space $E$, an unbounded set $R \subseteq E$ and a
continuous bilinear form $B : E \times E \to \mathbb{R}$ such that for some $\varepsilon > 0$
the quadratic form $W(x) = B(x, x)$ is bounded on the set of points at distance less than
$\varepsilon$ from $R$, yet there are no continuous linear functional $L : E \to \mathbb{R}$,
constant $c \in \mathbb{R}$ and real polynomial $V$ with $W(x) = V(L(x) + c)$ for all $x \in E$
and $|L(r) + c|$ bounded for $r \in R$.

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
