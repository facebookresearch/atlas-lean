/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomic
public import MathlibExt.NumberTheory.PrimitiveDivisor

/-!
# Large Zsigmondy primes

Statements from Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62.

For integers `a`, `b` and `n ≥ 1`, `Φ_n(a, b) = b ^ φ(n) Φ_n(a / b)` is the homogenized
cyclotomic polynomial `MetaMathlibExt.homogenizedCyclotomic` (the paper's Section 3 displays
`Φ_4(a, b) = a² + b²`, `Φ_6(a, b) = a² - ab + b²`, ... and uses
`aⁿ - bⁿ = ∏_{d ∣ n} Φ_d(a, b)`).
A Zsigmondy prime for `(a, b, n)` is a primitive prime divisor of `aⁿ - bⁿ`
(`IntegerSequence.IsPrimitivePrimeDivisor`); it is large if moreover `p² ∣ aⁿ - bⁿ` or
`p > n + 1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A large Zsigmondy prime for `(a, b, n)`: a prime `p` dividing `aⁿ - bⁿ` but no
`aᵐ - bᵐ` with `1 ≤ m < n`, such that `p² ∣ aⁿ - bⁿ` or `p > n + 1`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 1
(definition after Theorem 1). -/
def IsLargeZsigmondyPrime (a b n p : ℕ) : Prop :=
  IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p ∧
    ((p : ℤ) ^ 2 ∣ (a : ℤ) ^ n - (b : ℤ) ^ n ∨ n + 1 < p)

/-- `7` is a large Zsigmondy prime for `(2, 1, 3)`: `7 = 2³ - 1`, `7 ∤ 2 - 1, 2² - 1`, and
`7 > 3 + 1`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 1
(definition after Theorem 1). -/
theorem isLargeZsigmondyPrime_two_one_three_seven : IsLargeZsigmondyPrime 2 1 3 7 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩, Or.inr (by norm_num)⟩
  intro s hs hs3
  interval_cases s <;> norm_num

/-- For every positive integer `n`, `φ(n) ≥ √n / 2`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 1
(quoted from reference [2]). -/
theorem_wanted sqrt_div_two_le_totient (n : ℕ) (hn : 0 < n) :
    Real.sqrt n / 2 ≤ (Nat.totient n : ℝ)

/-- For a prime `p` and `n = p^β k` with `β, k ≥ 1`, `p ∤ k`:
`Φ_n(a, b) = Φ_{pk}(a^{p^{β-1}}, b^{p^{β-1}})` and
`Φ_n(a, b) · Φ_k(a^{p^{β-1}}, b^{p^{β-1}}) = Φ_k(a^{p^β}, b^{p^β})` (the paper's quotient,
cleared of its denominator), for all integers `a`, `b`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Corollary 1. -/
theorem_wanted homogenizedCyclotomic_prime_pow_mul {p β k : ℕ} (hp : p.Prime) (hβ : 0 < β)
    (hk : 0 < k) (hpk : ¬ p ∣ k) (a b : ℤ) :
    homogenizedCyclotomic (p ^ β * k) a b =
        homogenizedCyclotomic (p * k) (a ^ p ^ (β - 1)) (b ^ p ^ (β - 1)) ∧
      homogenizedCyclotomic (p ^ β * k) a b *
          homogenizedCyclotomic k (a ^ p ^ (β - 1)) (b ^ p ^ (β - 1)) =
        homogenizedCyclotomic k (a ^ p ^ β) (b ^ p ^ β)

/-- `aⁿ - bⁿ = ∏_{d ∣ n} Φ_d(a, b)` for every positive integer `n` and all integers `a`, `b`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (i)
(quoted from reference [6]). -/
theorem_wanted prod_divisors_homogenizedCyclotomic {n : ℕ} (hn : 0 < n) (a b : ℤ) :
    ∏ d ∈ n.divisors, homogenizedCyclotomic d a b = a ^ n - b ^ n

/-- For positive integers `a > b` and `n`, `(a - b)^φ(n) ≤ Φ_n(a, b) ≤ (a + b)^φ(n)`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (ii)
(quoted from reference [6]). -/
theorem_wanted homogenizedCyclotomic_mem_Icc {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (hn : 0 < n) :
    ((a : ℤ) - b) ^ Nat.totient n ≤ homogenizedCyclotomic n a b ∧
      homogenizedCyclotomic n a b ≤ ((a : ℤ) + b) ^ Nat.totient n

/-- For a prime `p` and a positive integer `n`: `Φ_{pn}(a, b) = Φ_n(aᵖ, bᵖ)` if `p ∣ n`, and
`Φ_{pn}(a, b) · Φ_n(a, b) = Φ_n(aᵖ, bᵖ)` (the paper's quotient, cleared of its denominator)
if `p ∤ n`, for all integers `a`, `b`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (iii)
(quoted from reference [6]). -/
theorem_wanted homogenizedCyclotomic_prime_mul {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (a b : ℤ) :
    (p ∣ n → homogenizedCyclotomic (p * n) a b = homogenizedCyclotomic n (a ^ p) (b ^ p)) ∧
      (¬ p ∣ n → homogenizedCyclotomic (p * n) a b * homogenizedCyclotomic n a b =
        homogenizedCyclotomic n (a ^ p) (b ^ p))

/-- Let `a > b` be positive integers, `p` an odd prime dividing neither `a` nor `b`, and `k`
the least positive integer with `p ∣ aᵏ - bᵏ`. Then for `n ≥ 1`, `v_p(Φ_n(a, b))` is
`v_p(aᵏ - bᵏ)` if `n = k`, `1` if `n = p^β k` with `β ≥ 1`, and `0` otherwise.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (iv)
(quoted from reference [6]). -/
theorem_wanted padicValInt_homogenizedCyclotomic_odd {a b n p k : ℕ} (hb : 0 < b)
    (hba : b < a) (hn : 0 < n) (hp : p.Prime) (hp2 : p ≠ 2) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hk : 0 < k) (hpk : (p : ℤ) ∣ (a : ℤ) ^ k - (b : ℤ) ^ k)
    (hkmin : ∀ m, 0 < m → m < k → ¬ (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m) :
    (n = k → padicValInt p (homogenizedCyclotomic n a b) =
        padicValInt p ((a : ℤ) ^ k - (b : ℤ) ^ k)) ∧
      ((∃ β, 1 ≤ β ∧ n = p ^ β * k) → padicValInt p (homogenizedCyclotomic n a b) = 1) ∧
      (n ≠ k → (¬ ∃ β, 1 ≤ β ∧ n = p ^ β * k) →
        padicValInt p (homogenizedCyclotomic n a b) = 0)

/-- Let `a > b` be odd positive integers. Then for `n ≥ 1`, `v_2(Φ_n(a, b))` is `v_2(a - b)` if
`n = 1`, `v_2(a + b)` if `n = 2`, `1` if `n = 2^β` with `β ≥ 2`, and `0` otherwise.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (v)
(quoted from reference [6]). -/
theorem_wanted padicValInt_two_homogenizedCyclotomic {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (ha : Odd a) (hb' : Odd b) (hn : 0 < n) :
    (n = 1 → padicValInt 2 (homogenizedCyclotomic n a b) = padicValInt 2 ((a : ℤ) - b)) ∧
      (n = 2 → padicValInt 2 (homogenizedCyclotomic n a b) = padicValInt 2 ((a : ℤ) + b)) ∧
      ((∃ β, 2 ≤ β ∧ n = 2 ^ β) → padicValInt 2 (homogenizedCyclotomic n a b) = 1) ∧
      ((¬ ∃ β, n = 2 ^ β) → padicValInt 2 (homogenizedCyclotomic n a b) = 0)

/-- Let `a > b` be coprime positive integers, `n ≥ 2`, `p` a prime divisor of `Φ_n(a, b)`, and
`k` the least positive integer with `p ∣ aᵏ - bᵏ`. Then (i) `p = 2` and `n = 2^β` with `β ≥ 1`,
or (ii) `p ≥ 3` and `n = k`, so `p` is a Zsigmondy prime for `(a, b, n)`, or (iii) `p` is the
greatest prime factor of `n`, `p > 2`, `n = p^β k` with `β ≥ 1`, and `v_p(Φ_n(a, b)) = 1`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 4. -/
theorem_wanted prime_dvd_homogenizedCyclotomic_cases {a b n p k : ℕ} (hb : 0 < b)
    (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) (hp : p.Prime)
    (hpΦ : (p : ℤ) ∣ homogenizedCyclotomic n a b) (hk : 0 < k)
    (hpk : (p : ℤ) ∣ (a : ℤ) ^ k - (b : ℤ) ^ k)
    (hkmin : ∀ m, 0 < m → m < k → ¬ (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m) :
    (p = 2 ∧ ∃ β, 1 ≤ β ∧ n = 2 ^ β) ∨
      (3 ≤ p ∧ n = k ∧
        IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p) ∨
      (p ∈ n.primeFactors ∧ (∀ r ∈ n.primeFactors, r ≤ p) ∧ 2 < p ∧
        (∃ β, 1 ≤ β ∧ n = p ^ β * k) ∧ padicValInt p (homogenizedCyclotomic n a b) = 1)

/-- For distinct coprime positive integers `a`, `b` and `n ≥ 2`, every Zsigmondy prime for
`(a, b, n)` divides `Φ_n(a, b)`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 5. -/
theorem_wanted dvd_homogenizedCyclotomic_of_isPrimitivePrimeDivisor {a b n p : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (hcop : a.Coprime b) (hn : 2 ≤ n)
    (hp : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p) :
    (p : ℤ) ∣ homogenizedCyclotomic n a b

/-- For coprime positive integers `a > b` and `n ≥ 2`, a Zsigmondy prime `q` for `(a, b, n)`
that is not a large Zsigmondy prime satisfies `n = q - 1`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 6. -/
theorem_wanted eq_sub_one_of_not_isLargeZsigmondyPrime {a b n q : ℕ} (hb : 0 < b)
    (hba : b < a) (hcop : a.Coprime b) (hn : 2 ≤ n)
    (hq : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q)
    (hql : ¬ IsLargeZsigmondyPrime a b n q) :
    n = q - 1

/-- For distinct coprime positive integers `a`, `b` and `n ≥ 3`, if `(n + 1) · gpf(n) < Φ_n(a, b)`
(stated for every prime factor of `n`, equivalently for the greatest one), then there is a
large Zsigmondy prime for `(a, b, n)`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 7. -/
theorem_wanted exists_isLargeZsigmondyPrime_of_lt {a b n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (hcop : a.Coprime b) (hn : 3 ≤ n)
    (hlt : ∀ q ∈ n.primeFactors, ((n + 1) * q : ℤ) < homogenizedCyclotomic n a b) :
    ∃ p, IsLargeZsigmondyPrime a b n p

/-- For `n > 1` outside `{2, 4, 6, 10, 12, 18}` and coprime positive integers `a > b`, there is
a large Zsigmondy prime for `(a, b, n)`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 8. -/
theorem_wanted exists_isLargeZsigmondyPrime_of_not_mem {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (hcop : a.Coprime b) (hn : 1 < n) (hn' : n ∉ ({2, 4, 6, 10, 12, 18} : Finset ℕ)) :
    ∃ p, IsLargeZsigmondyPrime a b n p

/-- For coprime positive integers `a > b` and `n > 1`, a large Zsigmondy prime for `(a, b, n)`
exists if and only if `(a, b, n)` is none of the exceptional cases: `n = 2` with `a + b = 2ˢ`
or `3 · 2ˢ`; `n = 4` with `(a, b) ∈ {(2, 1), (3, 1)}`; `n = 6` with
`(a, b) ∈ {(2, 1), (3, 1), (3, 2), (5, 1), (5, 4)}`; `n = 10` with `(a, b) ∈ {(2, 1), (3, 2)}`;
`n = 12` or `n = 18` with `(a, b) = (2, 1)`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Theorem 1
(the converse is the classification in the proof of Theorem 1). -/
theorem_wanted exists_isLargeZsigmondyPrime_iff {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (hcop : a.Coprime b) (hn : 1 < n) :
    (∃ p, IsLargeZsigmondyPrime a b n p) ↔
      ¬ ((n = 2 ∧ ∃ s : ℕ, a + b = 2 ^ s ∨ a + b = 3 * 2 ^ s) ∨
        (n = 4 ∧ (a, b) ∈ ({(2, 1), (3, 1)} : Finset (ℕ × ℕ))) ∨
        (n = 6 ∧ (a, b) ∈ ({(2, 1), (3, 1), (3, 2), (5, 1), (5, 4)} : Finset (ℕ × ℕ))) ∨
        (n = 10 ∧ (a, b) ∈ ({(2, 1), (3, 2)} : Finset (ℕ × ℕ))) ∨
        (n = 12 ∧ (a, b) = (2, 1)) ∨ (n = 18 ∧ (a, b) = (2, 1)))

end

end MetaMathlibExt
