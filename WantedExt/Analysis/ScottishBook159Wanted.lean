/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook159Wanted

/-- **The claim of Scottish Book Problem 159.** There is a sequence of real numbers
$a_0, a_1, a_2, \dots$ such that for every $\varepsilon > 0$ there is a natural number $N$ with the
following property: for every function $f : \mathbb{R} \to \mathbb{R}$ that is continuous on
$[0, 1]$ and satisfies $f(0) = 0$ and $0 \le f(x) \le 1$ for all $x \in [0, 1]$, there is a natural
number $n \le N$ with $|f(x) - P_n(x)| < \varepsilon$ for all $x \in [0, 1]$, where
$P_n(x) = \sum_{k=0}^{n} a_k x^k$ is the $n$-th partial sum of the power series $\sum a_k x^k$. -/
def ScottishBookProblem159Claim : Prop :=
  ∃ a : ℕ → ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ f : ℝ → ℝ,
    ContinuousOn f (Set.Icc 0 1) → f 0 = 0 →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, f x ∈ Set.Icc 0 1) →
      ∃ n : ℕ, n ≤ N ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1,
        dist (f x) (∑ k ∈ Finset.range (n + 1), a k * x ^ k) < ε

/--
**Scottish Book Problem 159 has a negative answer.** There is no sequence of real numbers
$a_0, a_1, a_2, \dots$ with the following property: for every $\varepsilon > 0$ there is a natural
number $N$ such that for every function $f : \mathbb{R} \to \mathbb{R}$ that is continuous on
$[0, 1]$ and satisfies $f(0) = 0$ and $0 \le f(x) \le 1$ for all $x \in [0, 1]$, there is a natural
number $n \le N$ with $\left|f(x) - \sum_{k=0}^{n} a_k x^k\right| < \varepsilon$ for all
$x \in [0, 1]$.

Sternbach's argument in the addendum Ad 159 uses the functions $\sin^2(2^n \pi x)$. Mazur showed
that for an arbitrary family $\Phi$ of functions of this kind, a power series with this property
exists exactly when the functions of $\Phi$ are equicontinuous.

Source: S. Ruziewicz, Problem 159 of the Scottish Book; Ad 159 in the
typescript (Sternbach's negative argument; Mazur's equicontinuity criterion).
-/
theorem_wanted problem159Refuted : ¬ ScottishBookProblem159Claim

end MathlibExt.Analysis.ScottishBook159Wanted
