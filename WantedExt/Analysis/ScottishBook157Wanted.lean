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

/-- A set `S` has right-hand density `0` at `0` if the proportion of `S` in
`(0, δ)` tends to `0` as `δ → 0⁺`. Densities are with respect to Lebesgue
measure. -/
def HasZeroDensityAtRight (S : Set ℝ) : Prop :=
  Filter.Tendsto (fun δ => (MeasureTheory.volume (S ∩ Set.Ioc 0 δ)).toReal / δ)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- `f` is approximately continuous at `x` if, for every `ε > 0`, the set of
`y` with `|f y - f x| < ε` has density `1` at `x`. -/
def ApproxContinuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto
      (fun δ => (MeasureTheory.volume ({y | |f y - f x| < ε} ∩ Set.Ioo (x - δ) (x + δ))).toReal /
        (2 * δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)

/-- The upper right-hand approximate derivative of `f` at `x` is positive:
for some threshold `a > 0`, the set of `h > 0` with
`(f (x + h) - f x) / h > a` has positive upper density at `0`, i.e. its
density does not tend to `0`. This is the approximate limsup of the
difference quotient over `h → 0⁺`, neglecting sets of `h` of density `0`
at `0`, being positive. -/
def HasPositiveUpperRightApproxDeriv (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
      ε ≤ (MeasureTheory.volume {h | h ∈ Set.Ioc 0 δ' ∧
        a < (f (x + h) - f x) / h}).toReal / δ'

/--
Let `f` be a real function of a real variable which is approximately
continuous everywhere, and suppose that at each point `x` the upper
right-hand approximate derivative of `f` at `x` is positive. Then `f` is
monotone increasing (nondecreasing).
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
