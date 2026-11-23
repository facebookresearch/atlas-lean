/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Totient

/-!
# A square-root lower bound for Euler's totient

For every positive integer `n`, Euler's totient function satisfies `√n / 2 ≤ φ n`
(`MetaMathlibExt.sqrt_div_two_le_totient`). Ömer Avcı states this bound, citing W. Feit, as
Lemma 2.1 of *Large Zsigmondy Primes* (arXiv:2011.06136v2), where it is used in the proof of the
classification of large Zsigmondy primes.

## Proof

By induction over coprime factorizations (`Nat.recOnPosPrimePosCoprime`), every natural number
`n` satisfies `n ≤ φ(n)² · gcd(2, n)`:

* for an odd prime power, `p ^ (k + 1) ≤ (p ^ k (p - 1))²` because `p ≤ (p - 1)²` for `p ≥ 3`;
* for a power of two, `2 ^ (k + 1) ≤ 2 · (2 ^ k)²`;
* both sides are multiplicative over coprime factors, since at most one of two coprime numbers
  is even.

Hence `n ≤ 2 φ(n)²`, that is, `φ(n) ≥ √(n / 2)`, which gives `n ≤ (2 φ(n))²` and so
`√n ≤ 2 φ(n)`. The argument also covers `n = 0`, so the hypothesis `0 < n` of the stated result
is not used.
-/

namespace MetaMathlibExt

/-- Every natural number `n` satisfies `n ≤ φ(n)² · gcd(2, n)`. -/
private theorem le_totient_sq_mul_gcd_two (n : ℕ) : n ≤ n.totient ^ 2 * Nat.gcd 2 n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
    rw [Nat.totient_prime_pow_succ hp]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · -- `2 ^ (k + 1) ≤ (2 ^ k)² · 2`
      rw [Nat.gcd_eq_left (dvd_pow_self 2 k.succ_ne_zero), pow_succ]
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      nlinarith
    · -- `p ^ (k + 1) ≤ (p ^ k (p - 1))²` for an odd prime `p`
      rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd.pow), mul_one]
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        rcases hodd with ⟨m, rfl⟩
        omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      have h1 : 1 ≤ (q + 1) ^ k := Nat.one_le_pow _ _ q.succ_pos
      have h2 : q + 1 ≤ q ^ 2 := by nlinarith
      calc (q + 1) ^ (k + 1) = (q + 1) ^ k * (q + 1) := pow_succ _ _
        _ ≤ (q + 1) ^ k * q ^ 2 := Nat.mul_le_mul_left _ h2
        _ ≤ (q + 1) ^ k * (q + 1) ^ k * q ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ h1)
        _ = ((q + 1) ^ k * q) ^ 2 := by ring
  | zero => simp
  | one => simp
  | coprime a b _ _ hab iha ihb =>
    rw [Nat.totient_mul hab, Nat.Coprime.gcd_mul 2 hab]
    calc a * b ≤ (a.totient ^ 2 * Nat.gcd 2 a) * (b.totient ^ 2 * Nat.gcd 2 b) :=
          Nat.mul_le_mul iha ihb
      _ = (a.totient * b.totient) ^ 2 * (Nat.gcd 2 a * Nat.gcd 2 b) := by ring

/-- Every natural number `n` satisfies `n ≤ 2 φ(n)²`, that is, `φ(n) ≥ √(n / 2)`. -/
private theorem le_two_mul_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 :=
  (le_totient_sq_mul_gcd_two n).trans <| by
    rw [mul_comm 2]
    exact Nat.mul_le_mul_left _ (Nat.gcd_le_left n two_pos)

/-- **Square-root lower bound for Euler's totient.** For every positive integer $n$,
$\varphi(n) \ge \sqrt{n}/2$, where $\varphi$ is Euler's totient function.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 1
(quoted from reference [2]). -/
public theorem sqrt_div_two_le_totient (n : ℕ) (hn : 0 < n) :
    Real.sqrt n / 2 ≤ (Nat.totient n : ℝ) := by
  have h : (n : ℝ) ≤ 2 * (n.totient : ℝ) ^ 2 := by exact_mod_cast le_two_mul_totient_sq n
  rw [div_le_iff₀ two_pos, Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (n.totient : ℝ)]

end MetaMathlibExt
