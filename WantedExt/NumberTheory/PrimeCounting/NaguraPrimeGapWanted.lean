/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nagura's theorem — wishlist
This file records Nagura's theorem as a `theorem_wanted` declaration.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.NaguraPrimeGapWanted

/--
Nagura's theorem: for `x ≥ 25` there is a prime `p` with `x < p < 6x / 5`.

Source: J. Nagura, On the interval containing at least one prime number,
Proc. Japan Acad. 28 (1952), 177–181.
-/
public theorem_wanted nagura_prime_gap :
    ∀ x : ℝ, 25 ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) < 6 * x / 5

end MathlibExt.NumberTheory.NaguraPrimeGapWanted
