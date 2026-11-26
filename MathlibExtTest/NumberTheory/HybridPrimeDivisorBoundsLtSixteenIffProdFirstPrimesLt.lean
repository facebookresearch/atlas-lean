/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HybridPrimeDivisorBoundsLtSixteenIffProdFirstPrimesLt

/-!
# Tests for primorials below powers of sixteen

The theorem gives the strict bound at fifteen and its failure at sixteen.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 10 (`integers-2026-A95-prop-10`).
-/

namespace MathlibExtTest.NumberTheory.HybridPrimeDivisorBoundsLtSixteenIffProdFirstPrimesLt

example : ∏ i ∈ Finset.range 15, Nat.nth Nat.Prime i < 16 ^ 15 :=
  (MetaMathlibExt.lt_sixteen_iff_prod_first_primes_lt (by decide)).mp (by decide)

example : 16 ^ 16 ≤ ∏ i ∈ Finset.range 16, Nat.nth Nat.Prime i := by
  apply Nat.le_of_not_gt
  intro h
  have := (MetaMathlibExt.lt_sixteen_iff_prod_first_primes_lt (by decide)).mpr h
  omega

end MathlibExtTest.NumberTheory.HybridPrimeDivisorBoundsLtSixteenIffProdFirstPrimesLt
