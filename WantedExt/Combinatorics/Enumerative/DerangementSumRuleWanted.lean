/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.Derangements.Finite

/-!
# A sum rule for derangements (statement)

Statement-only target from Jean-Christophe Pain, *A Sum Rule for Derangements*.
`D(n)` is Mathlib's `numDerangements n`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- For every integer `p ≥ 0`, `∑_{n=0}^{p} n D(n) = ⌊(p + 1)!/e⌋`, where `D(n)` is the number
of derangements of `n` objects.

Source: Jean-Christophe Pain, *A Sum Rule for Derangements*, INTEGERS 25 (2025),
Article A84, Theorem 1 (`integers-2025-A84-thm-1`). -/
public theorem_wanted sum_mul_numDerangements_eq_floor (p : ℕ) :
    ((∑ n ∈ Finset.range (p + 1), n * numDerangements n : ℕ) : ℤ) =
      ⌊((p + 1).factorial : ℝ) / Real.exp 1⌋

end

end MetaMathlibExt
