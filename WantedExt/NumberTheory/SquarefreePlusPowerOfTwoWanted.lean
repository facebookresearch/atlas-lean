/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Every odd integer `1 < n < 2^50` is a squarefree positive integer plus `2^k` with
`1 ≤ k ≤ 13` (a finite verification of Erdős's conjecture; see
`OpenConjectures/NumberTheory/ErdosProblem11` for the open statement over all odd `n`).

Source: Christian Hercher, *On the Sum of a Squarefree Integer and a Power of Two*, Journal of Integer Sequences 28 (2025), Article 25.3.1, Theorem 5 (`jis-2025-25.3.1-thm-5`). -/
public theorem_wanted exists_squarefree_add_two_pow_of_odd_lt_two_pow_fifty (n : ℕ) (h1 : 1 < n)
    (h2 : n < 2 ^ 50) (hodd : Odd n) :
    ∃ s k : ℕ, 0 < s ∧ Squarefree s ∧ 1 ≤ k ∧ k ≤ 13 ∧ n = s + 2 ^ k

end

end MetaMathlibExt
