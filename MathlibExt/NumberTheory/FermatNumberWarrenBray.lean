/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Fermat

/-!
# The Warren–Bray congruence for Fermat numbers

Mathlib's `Nat.fermat_primeFactors_one_lt` incorporates the quadratic-residue criterion for `2`
and gives `2 ^ (n + 2) ∣ p - 1`. Thus `(p - 1) / 2` is a multiple of `2 ^ (n + 1)`, and raising
`2` to that basic exponent already gives `1` modulo the whole Fermat number.

## References

* Jiří Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*, INTEGERS 26 (2026),
  Article A77, pp. 1–11, Theorem 2 (<https://math.colgate.edu/~integers/aa77/aa77.pdf>).
* Le Roy J. Warren and Henry G. Bray, *On the square-freeness of Fermat and Mersenne numbers*,
  Pacific Journal of Mathematics 22 (1967), no. 3, pp. 563–564, Theorem 1 (Fermat-number case)
  (<https://msp.org/pjm/1967/22-3/pjm-v22-n3-p15-p.pdf>).
-/

namespace MetaMathlibExt

-- Keep the source's `hp2` hypothesis; the Mathlib prime-factor formula does not require it.
set_option linter.unusedVariables false in
/-- **Warren–Bray congruence for prime divisors of Fermat numbers.** Let $F_n = 2^{2^n} + 1$ be
the $n$-th Fermat number. For every $n \ge 2$ and every odd prime $p$ dividing $F_n$, we have
$2^{(p-1)/2} \equiv 1 \pmod{F_n}$. This result is due to Warren and Bray (1967).

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 2 (`integers-2026-A77-thm-2`), citing
Warren and Bray. -/
public theorem two_pow_half_modEq_one_fermatNumber {n p : ℕ} (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.fermatNumber n) :
    2 ^ ((p - 1) / 2) ≡ 1 [MOD Nat.fermatNumber n] := by
  obtain ⟨k, hk⟩ := Nat.fermat_primeFactors_one_lt n p hn hp hdvd
  have hhalf : (p - 1) / 2 = k * 2 ^ (n + 1) := by
    rw [hk, Nat.add_sub_cancel, pow_succ (2 : ℕ) (n + 1), ← mul_assoc,
      Nat.mul_div_cancel _ Nat.zero_lt_two]
  have hneg : (2 : ZMod (Nat.fermatNumber n)) ^ 2 ^ n = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast ZMod.natCast_self (Nat.fermatNumber n)
  have hpow : (2 : ZMod (Nat.fermatNumber n)) ^ 2 ^ (n + 1) = 1 := by
    rw [pow_succ (2 : ℕ), pow_mul, hneg, neg_one_sq]
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hhalf,
    mul_comm k, pow_mul, hpow, one_pow]

end MetaMathlibExt
