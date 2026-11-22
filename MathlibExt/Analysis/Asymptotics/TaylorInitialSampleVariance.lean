/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Initial segment sample variance for Taylor's variance-to-mean power law

Formalizes the unbiased sample variance of the first `n` terms of an integer sequence.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- Unbiased initial-segment sample variance `v(a, n) = (1 / (n - 1)) * ∑_{j=1}^n (a(j) - m(a,
n))^2`
in `ℝ` for Taylor's variance-to-mean power law: the first equality of `eq:varexpanded`,
with mean `m(a, n) = (1 / n) * ∑_{j=1}^n a(j)` from `eq:mean` inlined.

Source: Joel E. Cohen, *Variance Functions of Asymptotically Exponentially
Increasing Integer Sequences Go Beyond Taylor's Law*, Journal of Integer
Sequences 25 (2022), Article 22.9.3, mean/variance definitions, lines 119–124,
equation `eq:mean` at line 122, first equality of `eq:varexpanded` at line 123
(label at line 124),
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Cohen/cohen13.tex>.

Indices run from `1` through `n`; total in Lean (`n = 0` gives `0` via
inverse-zero); the source invokes it for `n ≥ 2` with `ℕ = {1, 2, ...}`. -/
noncomputable def initialSegmentSampleVariance (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ j ∈ Finset.Icc 1 n,
    (((a j : ℝ) - (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, (a k : ℝ)) ^ 2)

end

end MetaMathlibExt
