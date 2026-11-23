/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace MathlibExt.Probability.ScottishBook161Wanted

/-- **Central limit theorem for lacunary sine sums.** A sequence of integers $(r_k)_{k \ge 0}$
satisfies the central limit theorem for lacunary sine sums if for all real numbers $a < b$, the
Lebesgue measure of the set of $x \in [0, 1]$ with
$a < \frac{1}{\sqrt{n}} \sum_{k=0}^{n-1} \sin(2 \pi r_k x) < b$ tends to
$\frac{1}{\sqrt{\pi}} \int_a^b e^{-y^2} \, dy$ as $n \to \infty$. -/
def LacunaryCLT (r : ℕ → ℤ) : Prop :=
  ∀ a b : ℝ, a < b →
    Filter.Tendsto
      (fun n : ℕ =>
        (MeasureTheory.volume {x : ℝ | x ∈ Set.Icc 0 1 ∧
          a < (∑ k ∈ Finset.range n, Real.sin (2 * Real.pi * (r k : ℝ) * x)) /
              Real.sqrt (n : ℝ) ∧
          (∑ k ∈ Finset.range n, Real.sin (2 * Real.pi * (r k : ℝ) * x)) /
              Real.sqrt (n : ℝ) < b}).toReal)
      Filter.atTop
      (nhds ((1 / Real.sqrt Real.pi) * MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Ioc a b)) (fun y => Real.exp (- y ^ 2))))

/--
**Kac's lacunary central limit theorem.** Let $(r_n)_{n \ge 0}$ be a sequence of positive integers
such that $r_n - (r_0 + r_1 + \dots + r_{n-1})$ tends to $+\infty$ as $n \to \infty$. Then $(r_n)$
satisfies the central limit theorem for lacunary sine sums. The sequence $r_n = 2^n$ satisfies
it as well.

Without a sign restriction the statement is false for integer sequences, so the terms are taken
positive here: the constant sequence $r_n = -1$ satisfies the gap hypothesis, since
$r_n - (r_0 + \dots + r_{n-1}) = n - 1$, but its normalized sum $-\sqrt{n} \sin(2 \pi x)$ is not
asymptotically normal.

The sequence $r_n = 2^n$ does not satisfy the gap hypothesis, since
$2^n - (1 + 2 + \dots + 2^{n-1}) = 1$ for every $n$. The sequence $r_n = 2^{n^2}$ is the example
given in the problem that does satisfy it.

Source: M. Kac, Problem 161 of the Scottish Book; the `2ⁿ` case is affirmative
by R. Salem and A. Zygmund, "On lacunary trigonometric series", Proc. Natl.
Acad. Sci. USA 33 (1947), 333-338, who proved the central limit theorem for
lacunary trigonometric series with ratio bounded away from `1`.
-/
theorem_wanted kacLacunaryCentralLimitTheorem :
    (∀ r : ℕ → ℤ, (∀ k, 0 < r k) →
      Filter.Tendsto (fun n : ℕ => (r n - ∑ k ∈ Finset.range n, r k))
        Filter.atTop Filter.atTop → LacunaryCLT r) ∧
      LacunaryCLT (fun n : ℕ => (2 : ℤ) ^ n)

/--
**Salem–Zygmund central limit theorem for lacunary sine sums.** Let $(r_k)_{k \ge 0}$ be a
sequence of positive integers with Hadamard gaps: there is $q > 1$ such that
$r_{k+1} / r_k \ge q$ for every $k$. Then $(r_k)$ satisfies the central limit theorem for
lacunary sine sums. In particular this holds for $r_k = 2^k$ and for $r_k = 2^{k^2}$.

This is the case of unit coefficients of the Salem–Zygmund theorem, which normalises a lacunary
sum $\sum_{k < n} a_k \sin(2 \pi r_k x)$ by $\bigl(\frac12 \sum_{k < n} a_k^2\bigr)^{1/2}$ and
obtains the standard normal law in the limit; with $a_k = 1$ the normaliser is $\sqrt{n/2}$, so
dividing by $\sqrt{n}$ instead gives the normal law with variance $1/2$.

The Hadamard-gap condition differs from Kac's condition in `kacLacunaryCentralLimitTheorem`:
$r_n = 2^n$ has Hadamard gaps with $q = 2$ but does not satisfy Kac's condition, and the
Fibonacci numbers $1, 2, 3, 5, 8, \dots$ have Hadamard gaps with $q = 3/2$ while
$r_n - (r_0 + \dots + r_{n-1})$ tends to $-\infty$ for them.

Source: R. Salem and A. Zygmund, "On lacunary trigonometric series", Proc. Natl.
Acad. Sci. USA 33 (1947), 333-338.
-/
theorem_wanted salemZygmundLacunaryCentralLimitTheorem :
    ∀ r : ℕ → ℤ, (∀ k, 0 < r k) →
      (∃ q : ℝ, 1 < q ∧ ∀ k, q ≤ (r (k + 1) : ℝ) / (r k : ℝ)) → LacunaryCLT r

end MathlibExt.Probability.ScottishBook161Wanted
