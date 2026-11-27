/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.GCD

/-!
# Coprimality of a power plus a signed multiple

Reducing the sum modulo each of the two coprime inputs gives the two gcd identities.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **$u^N + (-1)^{N+1} v$ is coprime to $u$ and to $v$.** Let $u, v$ be coprime positive integers
and let $N \ge 1$. Then $\gcd(u^N + (-1)^{N+1} v, u) = 1$ and $\gcd(u^N + (-1)^{N+1} v, v) = 1$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 5
(`jis-2025-25.2.2-lem-5`). -/
public theorem gcd_pow_add_neg_one_pow_mul_eq_one {N u v : ℕ} (hN : 1 ≤ N)
    (hu : 0 < u) (hv : 0 < v) (huv : u.Coprime v) :
    Int.gcd ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) u = 1 ∧
      Int.gcd ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) v = 1 := by
  constructor
  · rw [Int.gcd_add_left_left_of_dvd _ (dvd_pow_self (u : ℤ) (Nat.ne_of_gt hN))]
    simpa [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_mul] using huv.symm.gcd_eq_one
  · rw [Int.gcd_add_mul_right_left]
    exact Int.gcd_pow_left_of_gcd_eq_one huv

end MetaMathlibExt
