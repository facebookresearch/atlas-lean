/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.Set.Finite.Basic

/-!
# Prime divisibility of rows of Pascal's triangle

For a prime `p`, each row indexed by a power of `p` has all its inner entries divisible by `p`.
-/

namespace MetaMathlibExt

/-- **Primes divide all inner binomial coefficients of infinitely many rows.** For every prime
$p$ there are infinitely many natural numbers $n$ such that $p$ divides the binomial coefficient
$\binom{n}{k}$ for every $k$ with $1 \le k < n$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 3
(`integers-2024-A53-cor-3`). -/
public theorem infinite_setOf_prime_dvd_choose {p : ℕ} (hp : p.Prime) :
    {n : ℕ | ∀ k, 1 ≤ k → k < n → p ∣ n.choose k}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (Nat.pow_right_injective hp.two_le)
  intro m k hk hkm
  exact hp.dvd_choose_pow (Nat.ne_of_gt hk) hkm.ne

end MetaMathlibExt
