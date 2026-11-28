/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1148
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem1148Wanted

/-! Source record `FC-ErdosProblem1148`, ported from FormalConjectures
`ErdosProblems/1148.lean` (`theorem erdos_1148` and its variants) and
checked against erdosproblems.com/1148. The historical question is
preserved as `eventualRepresentation` (established); the weaker
`n + 2√n` bound is the unregistered companion `weakerBound`. Status:
resolved true (Chojecki with GPT-5.4 Pro, conditional on a Duke-type
equidistribution theorem [ELMV12]). -/

/-- **Bounded representation by $x^2 + y^2 - z^2$.** A natural number $n$ has a bounded
representation by $x^2 + y^2 - z^2$ if there are natural numbers $x, y, z$ with
$n = x^2 + y^2 - z^2$ and $x^2 \le n$, $y^2 \le n$, $z^2 \le n$, where the subtraction is
truncated subtraction of natural numbers.

The truncation changes nothing: a nonzero truncated difference is the true difference, and
$0 = 0^2 + 0^2 - 0^2$. -/
def Erdos1148Prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n

/-- **Representation by $x^2 + y^2 - z^2$ with the bound $n + 2\sqrt{n}$.**
A natural number $n$ has this representation if there are natural numbers $x, y, z$ with
$n = x^2 + y^2 - z^2$, where the subtraction is truncated subtraction of natural numbers, and
each of $x^2$, $y^2$, $z^2$ is at most $n + 2\sqrt{n}$ as a real number.

This weaker bound is reported obvious in [Va99]. -/
def weaker_prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n

/-- **Eventual bounded representation by $x^2 + y^2 - z^2$.** The statement that every
sufficiently large natural number $n$ can be written as $n = x^2 + y^2 - z^2$ with natural
numbers $x, y, z$ satisfying $\max(x^2, y^2, z^2) \le n$. -/
def eventualRepresentation : Prop :=
  ∀ᶠ n in Filter.atTop, Erdos1148Prop n

/-- **Representability of every $n$ with the bound $n + 2\sqrt{n}$.** The statement that every
natural number $n$ can be written as $n = x^2 + y^2 - z^2$ with natural numbers $x, y, z$,
the subtraction being truncated subtraction of natural numbers, such that each of $x^2$, $y^2$,
$z^2$ is at most $n + 2\sqrt{n}$. -/
def weakerBound : Prop :=
  ∀ n, weaker_prop n

/-- **Every large integer is a bounded value of $x^2 + y^2 - z^2$ (Erdős Problem 1148).**
For every sufficiently large natural number $n$ there are natural numbers $x, y, z$ with
$n = x^2 + y^2 - z^2$ and $\max(x^2, y^2, z^2) \le n$.

Resolved true: Resolved affirmatively (Chojecki with GPT-5.4 Pro via Duke-type theorem
[ELMV12]), per erdosproblems.com/1148. Source: P. Chojecki, Bounded Representations by
x^2+y^2-z^2, arXiv:2603.18087 (2026), https://arxiv.org/abs/2603.18087. Moved from
`OpenConjectures/NumberTheory/ErdosProblem1148`.
-/
public theorem_wanted eventualRepresentation_holds : eventualRepresentation

end MathlibExt.NumberTheory.ErdosProblem1148Wanted
