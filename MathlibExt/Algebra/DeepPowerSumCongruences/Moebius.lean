/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Basic

/-! # The Möbius sum over divisors prime to a given prime -/

namespace MetaMathlibExt

open ArithmeticFunction

/-- **Möbius sum over the divisors prime to a given prime.** Let $p$ be a prime, $\mu$ the Möbius
function and $n \ge 1$. The sum of $\mu(d)$ over the divisors $d$ of $n$ with $p \nmid d$ is $1$ if
$n$ is a power of $p$ (including $n = 1 = p^0$) and $0$ otherwise.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 28 (`integers-2024-A46-lem-28`). -/
public theorem sum_moebius_divisors_not_dvd_prime {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : n ≠ 0) :
    ∑ d ∈ n.divisors with ¬ p ∣ d, ArithmeticFunction.moebius d =
      if p ^ Nat.log p n = n then 1 else 0 := by
  have hdiv : n.divisors.filter (fun d => ¬ p ∣ d) = (ordCompl[p] n).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, _⟩, hpd⟩
      exact ⟨Nat.dvd_ordCompl_of_dvd_not_dvd hd hpd, (Nat.ordCompl_pos p hn).ne'⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.ordCompl_dvd n p), hn⟩,
        fun hpd => Nat.not_dvd_ordCompl hp hn (hpd.trans hd)⟩
  have hpower : ordCompl[p] n = 1 ↔ p ^ Nat.log p n = n := by
    constructor
    · intro h
      have heq := Nat.ordProj_mul_ordCompl_eq_self n p
      rw [h, mul_one] at heq
      rw [← heq, Nat.log_pow hp.one_lt]
    · intro h
      rw [← h]
      exact Nat.ordCompl_self_pow hp
  rw [hdiv, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  simp only [hpower]

end MetaMathlibExt
