/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Initial segment sample variance for Taylor's variance-to-mean power law

Formalizes the unbiased sample variance of the first `n` terms of an integer sequence.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Initial-segment sample variance.** For a sequence $a : \mathbb{N} \to \mathbb{N}$ and
$n \in \mathbb{N}$, the unbiased initial-segment sample variance is the real number
$v(a, n) = \frac{1}{n - 1} \sum_{j=1}^{n} \left(a(j) - \frac{1}{n} \sum_{k=1}^{n} a(k)\right)^2$,
with the convention $1 / 0 = 0$; in particular $v(a, 0) = v(a, 1) = 0$.

The inner average is the initial-segment mean $m(a, n)$. The source uses $v(a, n)$ only for
$n \ge 2$, with indices starting at $1$.

Source: Joel E. Cohen, *Variance Functions of Asymptotically Exponentially
Increasing Integer Sequences Go Beyond Taylor's Law*, Journal of Integer
Sequences 25 (2022), Article 22.9.3, mean/variance definitions, lines 119–124,
equation `eq:mean` at line 122, first equality of `eq:varexpanded` at line 123
(label at line 124),
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Cohen/cohen13.tex>. -/
noncomputable def initialSegmentSampleVariance (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ j ∈ Finset.Icc 1 n,
    (((a j : ℝ) - (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, (a k : ℝ)) ^ 2)

end

end MetaMathlibExt
