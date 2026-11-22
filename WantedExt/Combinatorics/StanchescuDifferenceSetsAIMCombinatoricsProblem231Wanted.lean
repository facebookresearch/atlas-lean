/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimum difference sets of full-dimensional sets in `ℤ^d` (AIM additive combinatorics, 2.6)

Problems presented at the AIM workshop on recent trends in additive combinatorics (collected by E.
Croot and V. F. Lev), Problem 2.6 (Y. Stanchescu): suppose that `A` is a finite subset of `ℤ^d`, not
contained in a hyperplane of dimension smaller than `d`. Determine the smallest possible value of
`|A - A|` as a function of `|A|`. Remarks: Freiman, Heppes and Uhrin proved `|A - A| ≥ (d + 1)|A| -
d(d + 1)/2`, best possible for `d = 1, 2`; for `d = 3` the presenter showed that the best possible
bound is `|A - A| ≥ 4.5|A| - 9`; for `d ≥ 4` the presenter conjectures `|A - A| ≥ (2d - 2 + 1/(d -
1))|A| - C_d` for some constant `C_d`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.StanchescuDifferenceSetsAIMCombinatoricsProblem231Wanted

open scoped Pointwise

/-!
Source: Problems presented at the workshop on recent trends in additive combinatorics, collected by
E. Croot and V. F. Lev, AIM workshop problem list, Problem 2.6 (Y. Stanchescu),
https://aimath.org/WWN/additivecomb/additivecomb.pdf. UnsolvedMath record UM-20001106
(`AIM-COMBINATORICS-0231`), dataset ulamai/UnsolvedMath v1.8.0.

"Not contained in a hyperplane" is read as affinely spanning: no nonzero real linear functional is
constant on `A`. The target is Stanchescu's conjectured bound for sufficiently large `A`, in the
exact form of Conlon and Lim's theorem (constant `C_d = 2d² - 4d + 3`, every `d ≥ 2`; they prove it
for finite `A ⊆ ℝ^d` not in a translate of a hyperplane, and `ℤ^d` is the source's setting). It does
not determine the minimum of `|A - A|` for every size, so the open-ended "determine" is covered only
asymptotically.
-/

/-- `A ⊆ ℤ^d` is not contained in an affine hyperplane: no nonzero real linear functional is
constant on `A`. -/
def IsFullDimensional {d : ℕ} (A : Finset (Fin d → ℤ)) : Prop :=
  ∀ (a : Fin d → ℝ) (c : ℝ), (∀ x ∈ A, ∑ i, a i * x i = c) → a = 0

/-- Stanchescu's bound: for every `d ≥ 2`, every sufficiently large full-dimensional finite
`A ⊆ ℤ^d` has `|A - A| ≥ (2d - 2 + 1/(d - 1))|A| - (2d² - 4d + 3)`. -/
def stanchescuDifferenceBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ N : ℕ, ∀ A : Finset (Fin d → ℤ), IsFullDimensional A → N ≤ A.card →
    (2 * d - 2 + 1 / (d - 1 : ℝ)) * A.card - (2 * d ^ 2 - 4 * d + 3) ≤ ((A - A).card : ℝ)

/--
Resolved true: Conlon and Lim prove `|A - A| ≥ (2d - 2 + 1/(d - 1))|A| - (2d² - 4d + 3)` for every
`d ≥ 2` and every sufficiently large finite `A ⊆ ℝ^d` not contained in a translate of a hyperplane,
best possible by a construction of Stanchescu, resolving the question first raised by Uhrin. Source:
Problems presented at the workshop on recent trends in additive combinatorics, collected by E. Croot
and V. F. Lev, AIM workshop problem list, Problem 2.6 (Y. Stanchescu),
https://aimath.org/WWN/additivecomb/additivecomb.pdf; resolution: D. Conlon and J. Lim, Difference
sets in ℝ^d, Israel J. Math. 267 (2025) 729-748, arXiv:2110.09053, abstract and main theorem,
https://arxiv.org/abs/2110.09053.
-/
public theorem_wanted stanchescuDifferenceBound_holds : stanchescuDifferenceBound

end MathlibExt.Combinatorics.StanchescuDifferenceSetsAIMCombinatoricsProblem231Wanted
