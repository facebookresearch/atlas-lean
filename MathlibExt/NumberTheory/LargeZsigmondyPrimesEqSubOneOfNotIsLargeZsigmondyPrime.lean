/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimitiveDivisor
import Mathlib.FieldTheory.Finite.Basic

/-!
# A non-large Zsigmondy prime satisfies `n = q - 1`

Statements from Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62.

A Zsigmondy prime for `(a, b, n)` is a primitive prime divisor of `aⁿ - bⁿ`
(`IntegerSequence.IsPrimitivePrimeDivisor`); it is large if moreover `p² ∣ aⁿ - bⁿ` or
`p > n + 1` (`MetaMathlibExt.IsLargeZsigmondyPrime`). A Zsigmondy prime that is not large
satisfies `n = q - 1` (`MetaMathlibExt.eq_sub_one_of_not_isLargeZsigmondyPrime`): since `a` and
`b` are coprime and `q` divides `aⁿ - bⁿ`, `q` divides neither `a` nor `b`, so Fermat's little
theorem gives `q ∣ a^(q - 1) - b^(q - 1)` and primitivity gives `n ≤ q - 1`, while not being
large forces `q ≤ n + 1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Large Zsigmondy prime.** Let $a$, $b$, $n$ and $p$ be natural numbers. Then $p$ is a large
Zsigmondy prime for $(a, b, n)$ when $p$ is a primitive prime divisor of the term $a^n - b^n$ of
the integer sequence $(a^m - b^m)_{m \ge 0}$, that is, $n \ge 1$, $p$ is prime, $p$ divides
$a^n - b^n$ and $p$ divides no $a^m - b^m$ with $1 \le m < n$, and moreover $p^2$ divides
$a^n - b^n$ or $p > n + 1$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 1
(definition after Theorem 1). -/
def IsLargeZsigmondyPrime (a b n p : ℕ) : Prop :=
  IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p ∧
    ((p : ℤ) ^ 2 ∣ (a : ℤ) ^ n - (b : ℤ) ^ n ∨ n + 1 < p)

/-- A prime dividing $a^m - b^m$ with $m \ge 1$ cannot divide $b$ when $a$ and $b$ are coprime. -/
private theorem not_dvd_b_of_prime_dvd_sub {a b m p : ℕ} (hp : Nat.Prime p)
    (hcop : Nat.Coprime a b)
    (hdvd : (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m) (hm : 1 ≤ m) : ¬ p ∣ b := by
  intro hpb
  have hpbm : (p : ℤ) ∣ (b : ℤ) ^ m :=
    dvd_pow (Int.natCast_dvd_natCast.mpr hpb) (by omega)
  have hpam : (p : ℤ) ∣ (a : ℤ) ^ m := by
    have h := dvd_add hdvd hpbm
    rwa [sub_add_cancel] at h
  have hpa : p ∣ a ^ m := Int.natCast_dvd_natCast.mp (by simpa using hpam)
  have hpa' : p ∣ a := hp.dvd_of_dvd_pow hpa
  have hgcd : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa' hpb
  have h1 : Nat.gcd a b = 1 := hcop
  rw [h1] at hgcd
  exact hp.not_dvd_one hgcd

/-- A prime dividing $a^m - b^m$ with $m \ge 1$ cannot divide $a$ either, once it does not
divide $b$. -/
private theorem not_dvd_a_of_prime_dvd_sub {a b m p : ℕ} (hp : Nat.Prime p)
    (hdvd : (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m) (hm : 1 ≤ m)
    (hpb : ¬ p ∣ b) : ¬ p ∣ a := by
  intro hpa
  have hpam : (p : ℤ) ∣ (a : ℤ) ^ m :=
    dvd_pow (Int.natCast_dvd_natCast.mpr hpa) (by omega)
  have hpbm : (p : ℤ) ∣ (b : ℤ) ^ m := by
    have h : (b : ℤ) ^ m = (a : ℤ) ^ m - ((a : ℤ) ^ m - (b : ℤ) ^ m) := by ring
    rw [h]
    exact dvd_sub hpam hdvd
  have hpbm' : p ∣ b ^ m := Int.natCast_dvd_natCast.mp (by simpa using hpbm)
  exact hpb (hp.dvd_of_dvd_pow hpbm')

set_option linter.unusedVariables false in
/-- **A Zsigmondy prime $q$ that is not large satisfies $n = q - 1$.** Let $a > b$ be coprime
positive integers and let $n \ge 2$. If $q$ is a primitive prime divisor of the term $a^n - b^n$
of the integer sequence $(a^m - b^m)_{m \ge 0}$ and $q$ is not a large Zsigmondy prime for
$(a, b, n)$, then $n = q - 1$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 6. -/
theorem eq_sub_one_of_not_isLargeZsigmondyPrime {a b n q : ℕ} (hb : 0 < b)
    (hba : b < a) (hcop : a.Coprime b) (hn : 2 ≤ n)
    (hq : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q)
    (hql : ¬ IsLargeZsigmondyPrime a b n q) :
    n = q - 1 := by
  have hprime : q.Prime := hq.prime
  have hle : q ≤ n + 1 := not_lt.mp fun h => hql ⟨hq, Or.inr h⟩
  have hqb : ¬ q ∣ b := not_dvd_b_of_prime_dvd_sub hprime hcop hq.dvd hq.one_le
  have hqa : ¬ q ∣ a := not_dvd_a_of_prime_dvd_sub hprime hq.dvd hq.one_le hqb
  have hfermat : ∀ x : ℕ, ¬ q ∣ x → (x : ℤ) ^ (q - 1) ≡ 1 [ZMOD q] := fun x hx =>
    Int.ModEq.pow_card_sub_one_eq_one hprime
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hprime).mpr hx)).isCoprime
  have hdvd : (q : ℤ) ∣ (a : ℤ) ^ (q - 1) - (b : ℤ) ^ (q - 1) :=
    ((hfermat b hqb).trans (hfermat a hqa).symm).dvd
  have hq2 : 2 ≤ q := hprime.two_le
  have hnle : n ≤ q - 1 := hq.toIsPrimitiveDivisor.le_of_dvd (by omega) hdvd
  exact le_antisymm hnle (by omega)

end

end MetaMathlibExt
