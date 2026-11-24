/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153Wanted

/-- **Mazur's Problem 153.** The claim of Mazur's Problem 153 from the Scottish Book, in its
original form: for every continuous function $f \colon [0,1]^2 \to \mathbb{R}$ and every real
$\varepsilon > 0$ there are a natural number $n$, points
$a_1, \dots, a_n, b_1, \dots, b_n \in [0,1]$ and real numbers $c_1, \dots, c_n$ such that

$$\Bigl| f(x, y) - \sum_{k=1}^n c_k \, f(a_k, y) \, f(x, b_k) \Bigr| \le \varepsilon$$

for all $x, y \in [0,1]$. -/
def ScottishBookProblem153Claim : Prop :=
  ∀ (f : C(↥(Set.Icc (0 : ℝ) 1) × ↥(Set.Icc (0 : ℝ) 1), ℝ)) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (a b : Fin n → ↥(Set.Icc (0 : ℝ) 1)) (c : Fin n → ℝ),
      ∀ (x y : ↥(Set.Icc (0 : ℝ) 1)),
        -- `dist` here is `|f (x, y) - ∑ k, c k * f (a k, y) * f (x, b k)|` by `Real.dist_eq`.
        dist (f (x, y)) (∑ k, c k * f (a k, y) * f (x, b k)) ≤ ε

/--
**Negative answer to Mazur's Problem 153.** There are a continuous function
$f \colon [0,1]^2 \to \mathbb{R}$ and a real number $\varepsilon > 0$ such that for every natural
number $n$, all points $a_1, \dots, a_n, b_1, \dots, b_n \in [0,1]$ and all real numbers
$c_1, \dots, c_n$ there are $x, y \in [0,1]$ with

$$\Bigl| f(x, y) - \sum_{k=1}^n c_k \, f(a_k, y) \, f(x, b_k) \Bigr| > \varepsilon.$$

That is, the approximation scheme of Mazur's Problem 153 fails.

Source: S. Mazur, Problem 153 of the Scottish
Book; refuted via P. Enflo's counterexample to the approximation problem in
Banach spaces, Acta Math. 130 (1973), 309–317, DOI 10.1007/BF02392270; see the
commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser,
2015). This is the original bivariate-function form of the problem, distinct
from the approximation-property consequence already in
`EnfloWanted.lean`.
-/
theorem_wanted mazur153_refuted : ¬ ScottishBookProblem153Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153Wanted
