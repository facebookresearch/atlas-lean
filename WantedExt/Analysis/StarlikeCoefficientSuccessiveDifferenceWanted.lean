/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import MathlibExt.Analysis.Complex.Wiman

@[expose] public section

namespace MathlibExt.Analysis.StarlikeCoefficientSuccessiveDifferenceWanted

open Complex (wimanTaylorCoefficient)

/-!
# Research Problems in Function Theory — Problem 6.46

Source clause list (every item appears in the formal text below):
1. `f` is in the class `S`: analytic in the unit disc, normalized by
  `f 0 = 0` and `f'(0) = 1`, and univalent (injective) on the unit disc.
2. `f` is star-like: `Re (z * f'(z) / f z) > 0` for `z ≠ 0` in the unit disc.
3. `a n` denotes the Taylor coefficient of `f` at `0`
  (`iteratedDeriv n f 0 / n!`).
4. Quantifier domain: all such `f`, all `n : ℕ` with `1 ≤ n`.
5. Questioned bound: `‖ |a (n+1)| - |a n| ‖ ≤ 1`, stated as the
  source's question (a `Prop` with no proof in this repository).
-/

/-- **Normalized univalent functions (the class $S$).** A function $f : \mathbb{C} \to \mathbb{C}$
is in the class $S$ when it is analytic on the open unit disc $\mathbb{D} = \{z : |z| < 1\}$,
satisfies $f(0) = 0$ and $f'(0) = 1$, and is injective on $\mathbb{D}$.

Source: Hayman and Lingham, Research Problems in Function Theory (2018), Problem 6.46,
https://arxiv.org/abs/1809.07200. -/
def IsInClassS (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
    f 0 = 0 ∧ HasDerivAt f 1 0 ∧ Set.InjOn f (Metric.ball (0 : ℂ) 1)

/-- **Starlike functions on the unit disc.** A function $f : \mathbb{C} \to \mathbb{C}$ is
starlike when it is analytic on the open unit disc $\mathbb{D} = \{z : |z| < 1\}$ and, for every
$z \ne 0$ in $\mathbb{D}$, $f(z) \ne 0$ and $\operatorname{Re}\bigl(z f'(z) / f(z)\bigr) > 0$.

Source: Hayman, Research Problems in Function Theory (2018), Problem 6.46,
https://arxiv.org/abs/1809.07200. -/
def IsStarlike (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
    ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → 0 < (z * deriv f z / f z).re

/-- **Hayman's successive coefficient problem for starlike functions.** The statement that for
every function $f : \mathbb{C} \to \mathbb{C}$ in the class $S$ (analytic on the open unit disc
$\mathbb{D} = \{z : |z| < 1\}$, with $f(0) = 0$ and $f'(0) = 1$, and injective on $\mathbb{D}$)
that is moreover starlike ($\operatorname{Re}\bigl(z f'(z) / f(z)\bigr) > 0$ for every $z \ne 0$
in $\mathbb{D}$), the Taylor coefficients $a_n = f^{(n)}(0) / n!$ of $f$ at $0$ satisfy
$\bigl| |a_{n+1}| - |a_n| \bigr| \le 1$ for every natural number $n \ge 1$.

Source: Hayman and Lingham, Research Problems in Function Theory (2018), Problem 6.46,
https://arxiv.org/abs/1809.07200. -/
def conjecture : Prop :=
  ∀ f : ℂ → ℂ, IsInClassS f → IsStarlike f →
    ∀ n : ℕ, 1 ≤ n → |‖wimanTaylorCoefficient f (n + 1)‖ - ‖wimanTaylorCoefficient f n‖| ≤ 1
/--
**Leung's theorem on successive coefficients of starlike functions.** Let
$f : \mathbb{C} \to \mathbb{C}$ be analytic on the open unit disc $\mathbb{D} = \{z : |z| < 1\}$,
with $f(0) = 0$ and $f'(0) = 1$, injective on $\mathbb{D}$, and starlike, meaning that
$\operatorname{Re}\bigl(z f'(z) / f(z)\bigr) > 0$ for every $z \ne 0$ in $\mathbb{D}$. Let
$a_n = f^{(n)}(0) / n!$ be the Taylor coefficients of $f$ at $0$. Then
$\bigl| |a_{n+1}| - |a_n| \bigr| \le 1$ for every natural number $n \ge 1$.

This answers Problem 6.46 of Hayman and Lingham, Research Problems in Function Theory (2018),
affirmatively. It was proved by Y. Leung (Bull. London Math. Soc. 10 (1978), 193-196) and
independently by D. H. Hamilton.

Source: Moduli difference of initial inverse logarithmic
coefficients for starlike and convex functions (2026), arXiv:2603.17600,
https://arxiv.org/abs/2603.17600. Moved from
`OpenConjectures/Analysis/StarlikeCoefficientSuccessiveDifference`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.StarlikeCoefficientSuccessiveDifferenceWanted
