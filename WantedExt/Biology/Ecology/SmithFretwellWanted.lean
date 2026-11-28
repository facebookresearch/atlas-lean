/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Smith–Fretwell optimal offspring size

A parent with reproductive budget `R > 0` makes `N = R / s` offspring of size (investment) `s`,
treating `N` as continuous; an offspring of size `s` has fitness `f(s)`. Parental fitness is
`W(s) = (R / s) f(s)`. Smith and Fretwell (1974) observed that the optimal size is where a
straight line through the origin is tangent to the offspring fitness curve: at an interior
optimum `s*`, `f'(s*) = f(s*) / s*`, and `s*` maximizes `f(s) / s`, so it does not depend on the
budget `R`.

Recorded here: the first-order tangency condition at any interior maximizer of `W` at which `f`
is differentiable, and the independence of the optimal sizes from `R`. Only the abstract of the
primary was read; both statements are elementary calculus derived from the model as stated.

Sources: C. C. Smith and S. D. Fretwell, "The optimal balance between size and number of
offspring", Am. Nat. 108 (1974) 499–506, doi:10.1086/282929.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.SmithFretwellWanted

/-- **Parental fitness.** The parental fitness `W(s) = (R / s) f(s)` with budget `R` and offspring
fitness `f`. -/
noncomputable def parentalFitness (R : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := R / s * f s

/-- **The Smith–Fretwell tangency condition.** Let `R > 0` and let `f : ℝ → ℝ` be any function. If
`s* > 0` maximizes parental fitness `W(s) = (R / s) f(s)` over all `s > 0`, and `f` is
differentiable at `s*`, then `f'(s*) = f(s*) / s*`.

Source: Smith and Fretwell (1974). -/
public theorem_wanted deriv_eq_div_of_isMaxOn (R : ℝ) (hR : 0 < R) (f : ℝ → ℝ) (ss : ℝ)
    (hss : 0 < ss) (hmax : ∀ s : ℝ, 0 < s → parentalFitness R f s ≤ parentalFitness R f ss)
    (hf : DifferentiableAt ℝ f ss) :
    deriv f ss = f ss / ss

/-- **The optimal size does not depend on the budget.** Let `R > 0` and let `f : ℝ → ℝ` be any
function. A size `s* > 0` maximizes parental fitness
`W(s) = (R / s) f(s)` over all `s > 0` if and only if it maximizes `f(s) / s` over all `s > 0`.

Source: Smith and Fretwell (1974). -/
public theorem_wanted isMaxOn_iff_div (R : ℝ) (hR : 0 < R) (f : ℝ → ℝ) (ss : ℝ) (hss : 0 < ss) :
    (∀ s : ℝ, 0 < s → parentalFitness R f s ≤ parentalFitness R f ss) ↔
      ∀ s : ℝ, 0 < s → f s / s ≤ f ss / ss

end WantedExt.Biology.Ecology.SmithFretwellWanted
