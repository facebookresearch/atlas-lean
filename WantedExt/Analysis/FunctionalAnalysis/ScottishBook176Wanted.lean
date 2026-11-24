/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook176Wanted

/-- **Scottish Book Problem 176 (Eidelheit's claim).** The claim that in every complete normed
ring $A$ (so $\|xy\| \le \|x\| \, \|y\|$, and $A$ has a unit) that is a normed algebra over
$\mathbb{R}$, the inverse of every invertible element is a limit of real polynomials in that
element: whenever $a, b \in A$ satisfy $ab = 1$ and $ba = 1$, there is a sequence
$(p_n)_{n \ge 0}$ of real polynomials with $p_n(a) \to b$ as $n \to \infty$. -/
def ScottishBookProblem176Claim : Prop :=
  ∀ (A : Type) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a b : A), a * b = 1 → b * a = 1 →
    ∃ p : ℕ → Polynomial ℝ,
      Filter.Tendsto (fun n => Polynomial.aeval a (p n)) Filter.atTop (nhds b)

/--
**Eidelheit's Problem 176 has a negative answer.** The claim of Scottish Book Problem 176 is
false: there are a complete normed ring $A$ that is a normed algebra over $\mathbb{R}$ and
elements $a, b \in A$ with $ab = 1$ and $ba = 1$ such that $b$ is not the limit of any sequence
$(p_n(a))_{n \ge 0}$ with $p_n$ real polynomials.

The counterexample recorded in the typescript is the ring of linear operations on the space
$C[0, 1]$, with $a$ the operation $U$ given by $U(x)(t) = x(t^2)$ for $0 \le t \le 1$.

Source: M. Eidelheit,
Problem 176 of the Scottish Book, with the negative answer recorded in
Ad 176 of the typescript (November 11, 1938). See the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted eidelheit176_refuted : ¬ ScottishBookProblem176Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook176Wanted
