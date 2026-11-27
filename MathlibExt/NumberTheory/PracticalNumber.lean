/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **Practical number.** A natural number $n$ is practical if $n > 0$ and every integer $m$ with
$1 \le m \le n$ is the sum of a set of distinct positive divisors of $n$.

Source: concept `jis_term_8ed6008fc4e01e1cc05ff7f6`, source lines 94–98. -/
public def IsPracticalNumber (n : ℕ) : Prop :=
  0 < n ∧ ∀ m, 1 ≤ m → m ≤ n →
    ∃ s : Finset ℕ, s ⊆ n.divisors ∧ ∑ x ∈ s, x = m

end

end MetaMathlibExt
