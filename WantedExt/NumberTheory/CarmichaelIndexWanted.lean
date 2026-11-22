/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Carmichael indices

Wanted statements from Yamagami and Inaba on the Carmichael index `N(n)`, the number of
solutions of `xⁿ = x` in `ℤ/nℤ`. Korselt's criterion (the paper's Corollary 1) is already
`Nat.isCarmichael_iff_korselt` in Mathlib.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The Carmichael index `N(n) = #{a ∈ ℤ | 0 ≤ a ≤ n - 1, aⁿ ≡ a (mod n)}`.

Source: Atsushi Yamagami and Youichi Inaba, *On a Formula and Some Properties of Carmichael
Indices*, INTEGERS 24 (2024), Article A40, Definition 1. -/
public def carmichaelIndex (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun a => a ^ n ≡ a [MOD n]).card

/-- `N(1) = 1`.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Section 1. -/
public theorem carmichaelIndex_one : carmichaelIndex 1 = 1 := by decide

/-- `N(4) = 2` and `N(66) = 24`, as in the paper's Table 1 and Example 3.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Example 1 (Table 1) and Example 3. -/
public theorem carmichaelIndex_four_and_sixtySix :
    carmichaelIndex 4 = 2 ∧ carmichaelIndex 66 = 24 := by
  constructor <;> decide +kernel

/-- Theorem 1: for `n ≥ 2` with prime factorization `n = ∏ pᵢ^{eᵢ}`,
`N(n) = ∏ᵢ (N(n; pᵢ^{eᵢ}) + 1)`, where `N(n; pᵢ^{eᵢ})` is the number of units of
`ℤ/pᵢ^{eᵢ}ℤ` whose order divides `gcd(pᵢ - 1, n / pᵢ^{eᵢ} - 1)`. The exponent `eᵢ` is
`n.factorization p`; the subtraction `n / p^e - 1` is in `ℕ`, where `n / p^e ≥ 1`.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Theorem 1 (`integers-2024-A40-thm-1`). -/
public theorem_wanted carmichaelIndex_eq_prod (n : ℕ) (hn : 2 ≤ n) :
    carmichaelIndex n = ∏ p ∈ n.primeFactors,
      (Nat.card {u : (ZMod (p ^ n.factorization p))ˣ //
        orderOf u ∣ Nat.gcd (p - 1) (n / p ^ n.factorization p - 1)} + 1)

/-- Theorem 2: there is no positive integer `n` with `N(n) = n - 1`.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Theorem 2 (`integers-2024-A40-thm-2`). -/
public theorem_wanted carmichaelIndex_ne_sub_one (n : ℕ) (hn : 0 < n) :
    carmichaelIndex n ≠ n - 1

end

end MetaMathlibExt
