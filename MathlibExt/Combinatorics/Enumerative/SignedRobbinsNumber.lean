/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Signed Robbins numbers

The definitions in this file come from Paul Barry, *From Fibonacci to Robbins:
Series Reversion and Hankel Transforms*, Journal of Integer Sequences 24 (2021).
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose]
public section

/-- **Robbins numbers.** For $n \in \mathbb{N}$, the Robbins number $A_n$ is the natural number
obtained by dividing $\prod_{k=0}^{n-1} (3k+1)!$ by $\prod_{k=0}^{n-1} (n+k)!$, where the division
is division of natural numbers rounded down.

Source: Paul Barry, "From Fibonacci to Robbins: Series Reversion and Hankel Transforms,"
Journal of Integer Sequences 24 (2021). Stable source identifiers: concept
`jis_sem_6ccc916178dd254f612035dd`; source statements `jis_43e90ede434b32aa20186bc5`,
`jis_6d15f998fcbd06c902185831`, `jis_8997a72d034e17ed46810fce`,
`jis_9e6db18aea1f87c47362e55f`, and `jis_f49a3ed20d503c088eb53ef1`.
-/
def robbinsNumber (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.range n, (3 * k + 1).factorial) /
    (∏ k ∈ Finset.range n, (n + k).factorial)

/-- **Signed Robbins numbers.** For $n \in \mathbb{N}$, the signed Robbins number is the integer
$(-1)^{\binom{n+1}{2}} A_{n+1}$, where $A_{n+1}$ is the Robbins number. -/
def signedRobbinsNumber (n : ℕ) : ℤ :=
  (-1) ^ Nat.choose (n + 1) 2 * (robbinsNumber (n + 1) : ℤ)

end

end MetaMathlibExt
