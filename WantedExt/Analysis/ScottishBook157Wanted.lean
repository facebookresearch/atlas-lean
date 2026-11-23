/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook157Wanted

/-- **Right density zero at the origin.** A set $S \subseteq \mathbb{R}$ has right-hand density
$0$ at $0$ if the Lebesgue outer measure of $S \cap (0, \delta]$, divided by $\delta$, tends to
$0$ as $\delta \to 0^+$. -/
def HasZeroDensityAtRight (S : Set ℝ) : Prop :=
  Filter.Tendsto (fun δ => (MeasureTheory.volume (S ∩ Set.Ioc 0 δ)).toReal / δ)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- **Approximate continuity.** A function $f \colon \mathbb{R} \to \mathbb{R}$ is approximately
continuous at $x$ if, for every $\varepsilon > 0$, the set
$S_\varepsilon = \{y : |f(y) - f(x)| < \varepsilon\}$ has density $1$ at $x$: the Lebesgue outer
measure of $S_\varepsilon \cap (x - \delta, x + \delta)$, divided by $2\delta$, tends to $1$ as
$\delta \to 0^+$. -/
def ApproxContinuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto
      (fun δ => (MeasureTheory.volume ({y | |f y - f x| < ε} ∩ Set.Ioo (x - δ) (x + δ))).toReal /
        (2 * δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)

/-- **Positive upper right approximate derivative.** The upper right-hand approximate derivative
of $f \colon \mathbb{R} \to \mathbb{R}$ at $x$ is positive: there are $a > 0$ and $\varepsilon > 0$
such that for every $\delta > 0$ there is $\delta' \in (0, \delta]$ for which the Lebesgue outer
measure of $\{h \in (0, \delta'] : (f(x + h) - f(x))/h > a\}$ is at least $\varepsilon \delta'$.

Equivalently, the approximate upper limit of the difference quotient $(f(x + h) - f(x))/h$ as
$h \to 0^+$, which neglects sets of $h$ of right density $0$ at $0$, is positive. -/
def HasPositiveUpperRightApproxDeriv (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
      ε ≤ (MeasureTheory.volume {h | h ∈ Set.Ioc 0 δ' ∧
        a < (f (x + h) - f x) / h}).toReal / δ'

/--
**Approximate derivative test for monotonicity (Scottish Book Problem 157).** Let
$f \colon \mathbb{R} \to \mathbb{R}$ be approximately continuous at every point, and suppose that
at every point $x$ the upper right-hand approximate derivative of $f$ is positive. Then $f$ is
monotone nondecreasing.

Source: A. J. (Gus) Ward, Problem 157 of the Scottish Book; solved
affirmatively by D. Ornstein, "A characterization of monotone functions",
Illinois J. Math. 15 (1971), 73-76, and by R. O'Malley (1975), whose theorem
on approximate maxima yields an immediate positive solution; see
K. Beanland, P. Humke, T. Richards, "On Scottish Book Problem 157",
Real Anal. Exchange 41(2) (2016), 331-346.
-/
theorem_wanted wardApproximatelyContinuousPositiveDerivMonotone :
    ∀ f : ℝ → ℝ, (∀ x, ApproxContinuousAt f x) →
      (∀ x, HasPositiveUpperRightApproxDeriv f x) → Monotone f

end MathlibExt.Analysis.ScottishBook157Wanted
