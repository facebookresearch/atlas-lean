/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1196
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

open scoped Asymptotics

namespace MathlibExt.NumberTheory.ErdosProblem1196Wanted

/-! Source record `FC-ErdosProblem1196`, ported from FormalConjectures
`ErdosProblems/1196.lean` (`theorem erdos_1196`) and checked against
erdosproblems.com/1196. The `answer(True)` wrapper is elaborated to the
direct claim. Status: resolved true (site: PROVED (LEAN)). -/

/-- **Primitive set in a commutative monoid.** A subset $A$ of a commutative monoid $M$ is
primitive if for all $x, y \in A$ with $x \mid y$, the elements $x$ and $y$ are associated,
that is, $x u = y$ for some unit $u$ of $M$. In $\mathbb{N}$, where $1$ is the only unit, this
says that no element of $A$ divides a different element of $A$. -/
def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → Associated x y

/-- **Asymptotic primitive set bound.** The statement that there is a function
$o : \mathbb{N} \to \mathbb{R}$ with $o(x) \to 0$ as $x \to \infty$ such that for every natural
number $x > 0$ and every primitive set $A$ of natural numbers contained in $[x, \infty)$, the
series $\sum_{a \in A} \frac{1}{a \log a}$ is summable and
$\sum_{a \in A} \frac{1}{a \log a} < 1 + o(x)$. Here a set of natural numbers is primitive if
no element divides a different element, and the term for $a = 1$, where $\log a = 0$, is taken
to be $0$. -/
def conjecture : Prop :=
  ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧ ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x,
    IsPrimitive A →
    Summable (fun a : A => 1 / ((a.val : ℝ).log * a)) ∧
      ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x

/-- **Erdős Problem 1196 on primitive sets.** There is a function $o : \mathbb{N} \to \mathbb{R}$
with $o(x) \to 0$ as $x \to \infty$ such that for every natural number $x > 0$ and every
primitive set $A$ of natural numbers contained in $[x, \infty)$, the series
$\sum_{a \in A} \frac{1}{a \log a}$ is summable and $\sum_{a \in A} \frac{1}{a \log a} < 1 + o(x)$.
Here a set of natural numbers is primitive if no element divides a different element, and the
term for $a = 1$, where $\log a = 0$, is taken to be $0$.

Resolved true: Resolved affirmatively (GPT-5.4 Pro prompted by Price; account [ABLLPSTT26]), per
erdosproblems.com/1196. Source: B. Alexeev, K. Barreto, Y. Li, J. D. Lichtman, L. Price, J. I.
Shah, Q. Tang, T. Tao, Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond,
arXiv:2605.00301 (2026), https://arxiv.org/abs/2605.00301. Moved from
`OpenConjectures/NumberTheory/ErdosProblem1196`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem1196Wanted
