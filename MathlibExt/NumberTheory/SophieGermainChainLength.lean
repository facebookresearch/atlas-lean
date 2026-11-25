/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic

/-!
# Length of a Sophie Germain prime chain

A chain starting at an odd prime `p` has at most `orderOf (2 : ZMod p)` initial prime terms.
-/

namespace MetaMathlibExt

/-- **Length of a Sophie Germain prime chain.** Let $p$ be an odd prime and let
$\mathrm{ord}_p(2)$ be the multiplicative order of $2$ modulo $p$. Then there is some
$j \le \mathrm{ord}_p(2)$ such that $2^j (p + 1) - 1$ is not prime. Thus the Sophie Germain prime
chain $q_1 = p$, $q_{i+1} = 2q_i + 1 = 2^i (p + 1) - 1$ begins with at most $\mathrm{ord}_p(2)$
consecutive primes.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.5, quoting T. Agoh, Tatra Mt. Math. Publ. 20 (2000), Proposition 3.1
(`integers-2025-A31-thm-3-5`). -/
public theorem sophieGermainChain_length_le_orderOf_two {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∃ j ≤ orderOf (2 : ZMod p), ¬(2 ^ j * (p + 1) - 1).Prime := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let j := orderOf (2 : ZMod p)
  have hu : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 (hp.odd_of_ne_two hp2).coprime_two_left
  have hpow : 1 < 2 ^ j := one_lt_pow₀ one_lt_two hu.isOfFinOrder.orderOf_pos.ne'
  have hlt : p + 1 < 2 ^ j * (p + 1) := lt_mul_of_one_lt_left (Nat.succ_pos _) hpow
  refine ⟨j, le_rfl, Nat.not_prime_of_dvd_of_lt ?_ hp.two_le (by omega)⟩
  rw [← ZMod.natCast_eq_zero_iff]
  simp [Nat.cast_sub (by omega : 1 ≤ 2 ^ j * (p + 1)), j, pow_orderOf_eq_one]

end MetaMathlibExt
