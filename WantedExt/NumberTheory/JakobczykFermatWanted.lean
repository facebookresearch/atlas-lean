/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Fermat
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.NumberTheory.WieferichPrime

/-!
# Notes on Jakóbczyk's hypothesis on Fermat numbers

Statements from Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat
Numbers*, INTEGERS 26 (2026), Article A77, about the Fermat numbers
`F_n = 2^{2^n} + 1` (Mathlib's `Nat.fermatNumber`), their generalizations
`F_n(a, b) = a^{b^n} + 1`, and Wieferich primes to base `2` (`Nat.IsWieferichPrime`, i.e.
`p² ∣ 2^{p-1} - 1`) and to base `a` (`a^{p-1} ≡ 1 (mod p²)`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- Warren and Bray (1967), as recalled by the source: for `n ≥ 2` and an odd prime
`p ∣ F_n`, `2^{(p-1)/2} ≡ 1 (mod F_n)`.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 2 (`integers-2026-A77-thm-2`), citing
Warren and Bray. -/
public theorem_wanted two_pow_half_modEq_one_fermatNumber {n p : ℕ} (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.fermatNumber n) :
    2 ^ ((p - 1) / 2) ≡ 1 [MOD Nat.fermatNumber n]

/-- For a prime `p ∣ F_n`: `p² ∣ F_n` if and only if `2^{p-1} ≡ 1 (mod p²)`.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 3 (`integers-2026-A77-thm-3`), citing
Křížek, Luca, and Somer. -/
public theorem_wanted sq_dvd_fermatNumber_iff {n p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.fermatNumber n) :
    p ^ 2 ∣ Nat.fermatNumber n ↔ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2]

/-- For an odd prime `p`: `p² ∣ F_n` if and only if `p` is a Wieferich prime and
`ord_p(2) = 2^{n+1}` (the source's consequence (11) of Theorem 5). Derived from
`sq_dvd_fermatNumber_iff` (Theorem 3): `p ∣ F_n` exactly when `ord_p(2) = 2^{n+1}`.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 5, Equation (11)
(`integers-2026-A77-thm-5`). -/
public theorem_wanted sq_dvd_fermatNumber_iff_wieferich_orderOf {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    p ^ 2 ∣ Nat.fermatNumber n ↔ p.IsWieferichPrime ∧ orderOf (2 : ZMod p) = 2 ^ (n + 1) := by
  have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  have : Fact p.Prime := ⟨hp⟩
  have hF : ((Nat.fermatNumber n : ℕ) : ZMod p) = (2 : ZMod p) ^ 2 ^ n + 1 := by
    simp [Nat.fermatNumber]
  have hdvd : p ∣ Nat.fermatNumber n ↔ orderOf (2 : ZMod p) = 2 ^ (n + 1) := by
    rw [← ZMod.natCast_eq_zero_iff, hF]
    constructor
    · intro h
      have h1 : (2 : ZMod p) ^ 2 ^ n = -1 := eq_neg_of_add_eq_zero_left h
      refine orderOf_eq_prime_pow ?_ ?_
      · rw [h1]; exact ZMod.neg_one_ne_one
      · rw [pow_succ, pow_mul, h1]; norm_num
    · intro h
      have h2 : (2 : ZMod p) ^ 2 ^ (n + 1) = 1 := by rw [← h]; exact pow_orderOf_eq_one _
      have h3 : (2 : ZMod p) ^ 2 ^ n ≠ 1 := by
        intro h4
        have h7 := Nat.le_of_dvd (by positivity) (h ▸ orderOf_dvd_of_pow_eq_one h4)
        have h8 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have h5 : (2 : ZMod p) ^ 2 ^ n * (2 : ZMod p) ^ 2 ^ n = 1 := by
        rw [← pow_add, ← two_mul, ← pow_succ']; exact h2
      rcases mul_self_eq_one_iff.mp h5 with h6 | h6
      · exact absurd h6 h3
      · rw [h6]; ring
  rw [Nat.isWieferichPrime_iff_modEq]
  constructor
  · intro h
    have hpd : p ∣ Nat.fermatNumber n := (dvd_pow_self p two_ne_zero).trans h
    exact ⟨⟨hp, (❰sq_dvd_fermatNumber_iff❱ hp hpd).mp h⟩, hdvd.mp hpd⟩
  · rintro ⟨⟨-, hw⟩, ho⟩
    exact (❰sq_dvd_fermatNumber_iff❱ hp (hdvd.mpr ho)).mpr hw

/-- Divisibility of the generalized Fermat numbers `F_n(a, b) = a^{b^n} + 1` for `a, b ≥ 2` and
`n < m`: (i) if `a` and `b` are even, `gcd(F_m(a, b), F_n(a, b)) = 1`; (ii) if `a` is odd and `b`
even, the gcd is `2`; (iii) if `b` is odd, the gcd is `F_n(a, b)` (here `n ≤ m` suffices). The
source assumes `2 < a, b` and `0 ≤ n ≤ m`; its proof uses only `a, b ≥ 2` and treats `m > n`
("Since `m > n`"), and (i), (ii) fail at `m = n` (`a = b = 4`, `m = n = 0`:
`gcd(5, 5) = 5`; `a = 3`, `b = 4`, `m = n = 0`: `gcd(4, 4) = 4`).

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Proposition 1 (`integers-2026-A77-prop-1`). -/
public theorem_wanted gcd_pow_pow_add_one {a b m n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (n < m → Even a → Even b → Nat.gcd (a ^ b ^ m + 1) (a ^ b ^ n + 1) = 1) ∧
      (n < m → Odd a → Even b → Nat.gcd (a ^ b ^ m + 1) (a ^ b ^ n + 1) = 2) ∧
      (n ≤ m → Odd b → Nat.gcd (a ^ b ^ m + 1) (a ^ b ^ n + 1) = a ^ b ^ n + 1)

/-- For `a, b ≥ 2` with `b` odd, the number `φ_n(a, b) = Ω(F_n(a, b))` of prime factors of
`F_n(a, b) = a^{b^n} + 1`, counted with multiplicity, is monotone in `n`. The open question on
`φ_n(2, 2)` and the listed values of `φ_n(2, 2)` that the record appends are omitted.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Corollary 1 (`integers-2026-A77-cor-1`). -/
public theorem_wanted monotone_cardFactors_pow_pow_add_one {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hbo : Odd b) :
    Monotone fun n : ℕ => ArithmeticFunction.cardFactors (a ^ b ^ n + 1)

/-- For `a, b, m ≥ 2` and `n ≥ 1`: if `a^{b^n} ≢ 1 (mod m)`, then `a^{b^t} ≢ 1 (mod m)` for every
`t < n`.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Lemma 2 (`integers-2026-A77-lem-2`). -/
public theorem_wanted not_pow_pow_modEq_one_of_lt {a b m n t : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hm : 2 ≤ m) (hn : 1 ≤ n) (h : ¬ a ^ b ^ n ≡ 1 [MOD m]) (ht : t < n) :
    ¬ a ^ b ^ t ≡ 1 [MOD m]

/-- For `a, b ≥ 2`, `n ≥ 0` and an odd prime `p` with `gcd(ab, p) = 1`, writing `p ∈ W(a)` (a
Wieferich prime to base `a`) for `a^{p-1} ≡ 1 (mod p²)` (with `p ∤ a`, given here) and `ord_p(a)`
for the order of `a` in `ZMod p`: (i) if `p² ∣ F_n(a, b)` then `p ∈ W(a)` and
`ord_p(a) ∣ 2b^n`; (ii) if `p ∈ W(a)` and `ord_p(a) = 2b^n` then `p² ∣ F_n(a, b)`.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 4 (`integers-2026-A77-thm-4`). -/
public theorem_wanted sq_dvd_pow_pow_add_one_wieferich {a b n p : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime (a * b) p) :
    (p ^ 2 ∣ a ^ b ^ n + 1 →
        a ^ (p - 1) ≡ 1 [MOD p ^ 2] ∧ orderOf (a : ZMod p) ∣ 2 * b ^ n) ∧
      (a ^ (p - 1) ≡ 1 [MOD p ^ 2] → orderOf (a : ZMod p) = 2 * b ^ n →
        p ^ 2 ∣ a ^ b ^ n + 1)

/-- For an odd prime `p ∤ a`: `p² ∣ F_n(a, 2) = a^{2^n} + 1` if and only if
`p ∈ W(a)` and `ord_p(a) = 2^{n+1}` (the source's `a ≥ 2` is dropped: at `a = 1` both sides are
false). Membership `p ∈ W(a)` (Wieferich prime to base `a`) is written `a^{p-1} ≡ 1 (mod p²)`, the paper's equation (8); `ord_p(a)` is `orderOf (a : ZMod p)`.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 5 (`integers-2026-A77-thm-5`). -/
public theorem_wanted sq_dvd_pow_two_pow_add_one_iff_wieferich {a n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpa : ¬ p ∣ a) :
    p ^ 2 ∣ a ^ 2 ^ n + 1 ↔ a ^ (p - 1) ≡ 1 [MOD p ^ 2] ∧ orderOf (a : ZMod p) = 2 ^ (n + 1)

/-- For a prime `p ∤ a`: `p ∈ W(a)` if and only if `ord_{p²}(a) = ord_p(a)`, with `p ∈ W(a)`
written `a^{p-1} ≡ 1 (mod p²)` (the paper's equation (8)); the source's `a ≥ 2` is dropped (both
sides hold at `a = 1`).

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Lemma 1 (iii) (`integers-2026-A77-lem-1`). -/
public theorem_wanted pow_sub_one_modEq_one_sq_iff_orderOf_eq {a p : ℕ} (hp : p.Prime)
    (hpa : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p ^ 2] ↔ orderOf (a : ZMod (p ^ 2)) = orderOf (a : ZMod p)

/-- For `a, b, D ≥ 2` and `D ∣ F_n(a, b) = a^{b^n} + 1`: (i) if `b` is odd, `D ∣ F_{n+k}(a, b)` for
every `k ≥ 1`; (ii) if `b` is even and `D ≥ 3`, `D ∤ F_{n+k}(a, b)` for every `k ≥ 1`. The source
states (ii) for `D ≥ 2`; its proof gives `F_{n+k}(a, b) ≡ 2 (mod D)`, which excludes only
`D = 2`, and (ii) is false there (`a = 3`, `b = 2`, `n = 0`, `k = 1`: `2 ∣ 4` and `2 ∣ 10`).

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 7 (`integers-2026-A77-thm-7`). -/
public theorem_wanted dvd_pow_pow_add_one_shift {a b D n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hD : 2 ≤ D) (h : D ∣ a ^ b ^ n + 1) :
    (Odd b → ∀ k, 1 ≤ k → D ∣ a ^ b ^ (n + k) + 1) ∧
      (Even b → 3 ≤ D → ∀ k, 1 ≤ k → ¬ D ∣ a ^ b ^ (n + k) + 1)

/-- For `a, b ≥ 2` and a prime `p`, let `n₀` be the least `n` with `p² ∣ F_n(a, b) = a^{b^n} + 1`.
The residues `F_n(a, b) mod p²` are eventually periodic; let the period start at the least index
`m` from which they are periodic. (i) If `b` is odd, the period starts at `n₀` (the index of the
first term of the period); (ii) if `b` is even, it starts at `n₀ + 1` (`n₀` is the index of the
last term of the pre-period).

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Corollary 2 (`integers-2026-A77-cor-2`). -/
public theorem_wanted isLeast_periodic_start_pow_pow_add_one_mod_sq {a b p n₀ : ℕ} (ha : 2 ≤ a)
    (hb : 2 ≤ b) (hp : p.Prime) (hn₀ : p ^ 2 ∣ a ^ b ^ n₀ + 1)
    (hmin : ∀ n < n₀, ¬ p ^ 2 ∣ a ^ b ^ n + 1) :
    (Odd b → IsLeast {m : ℕ | ∃ T, 0 < T ∧
        Function.Periodic (fun k => (a ^ b ^ (m + k) + 1) % p ^ 2) T} n₀) ∧
      (Even b → IsLeast {m : ℕ | ∃ T, 0 < T ∧
        Function.Periodic (fun k => (a ^ b ^ (m + k) + 1) % p ^ 2) T} (n₀ + 1))

end

end MetaMathlibExt
