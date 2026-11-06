/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic

/-!
# Initial segment mean for Taylor's variance-to-mean power law

Formalizes the mean of the first `n` terms of an integer sequence.
-/

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/-- **Initial-segment mean.** For a sequence $a : \mathbb{N} \to \mathbb{N}$ and $n \in \mathbb{N}$,
the initial-segment mean is the real number $m(a, n) = \frac{1}{n} \sum_{j=1}^{n} a(j)$, with
the convention $1 / 0 = 0$, so that $m(a, 0) = 0$.

The source uses $m(a, n)$ only for $n \ge 2$, with indices starting at $1$.

Source: Joel E. Cohen, *Variance Functions of Asymptotically Exponentially
Increasing Integer Sequences Go Beyond Taylor's Law*, Journal of Integer
Sequences 25 (2022), Article 22.9.3, mean/variance definitions, lines 119–124,
equation `eq:mean` at line 122,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Cohen/cohen13.tex>. -/
noncomputable def initialSegmentMean (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (a (j + 1) : ℝ)

end MetaMathlibExt

end
