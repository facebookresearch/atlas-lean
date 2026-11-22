/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- A `k`-generalized Markov triple: a positive integer solution of the `k`-generalized
Markov equation `GME(k)`: `x² + y² + z² + k(yz + zx + xy) = (3 + 3k) x y z`. For `k = 0`
these are the classical Markov triples.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.2. -/
public def IsGenMarkovTriple (k a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧
    a ^ 2 + b ^ 2 + c ^ 2 + k * (b * c + c * a + a * b) = (3 + 3 * k) * a * b * c

/-- Characteristic value: `(1, 1, 1)` is a `k`-generalized Markov triple for every `k`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.2. -/
public theorem isGenMarkovTriple_one_one_one (k : ℕ) : IsGenMarkovTriple k 1 1 1 := by
  refine ⟨Nat.one_pos, Nat.one_pos, Nat.one_pos, ?_⟩
  ring

/-- Characteristic value: `(1, 1, 2)` is a classical (`k = 0`) Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.1. -/
public theorem isGenMarkovTriple_zero_one_one_two : IsGenMarkovTriple 0 1 1 2 := by
  refine ⟨Nat.one_pos, Nat.one_pos, Nat.two_pos, ?_⟩
  norm_num

/-- A `k`-generalized Markov number: an entry of some `k`-generalized Markov triple (the
equation is symmetric, so the middle entry is no restriction).

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.2. -/
public def IsGenMarkovNumber (k b : ℕ) : Prop :=
  ∃ a c, IsGenMarkovTriple k a b c

/-- `b` is the maximum of a unique `k`-generalized Markov triple up to order: there is a
triple `(a, b, c)` with `max {a, b, c} = b`, and any other such triple `(a', b, c')` has
`{a', c'} = {a, c}`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Conjecture 1.8. -/
public def HasUniqueMaxGenMarkovTriple (k b : ℕ) : Prop :=
  ∃ a c, IsGenMarkovTriple k a b c ∧ a ≤ b ∧ c ≤ b ∧
    ∀ a' c', IsGenMarkovTriple k a' b c' → a' ≤ b → c' ≤ b →
      (a' = a ∧ c' = c) ∨ (a' = c ∧ c' = a)

/-- Characteristic lemma: a number that is the maximum of a unique triple is a
`k`-generalized Markov number.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Conjecture 1.8. -/
public theorem HasUniqueMaxGenMarkovTriple.isGenMarkovNumber {k b : ℕ}
    (h : HasUniqueMaxGenMarkovTriple k b) : IsGenMarkovNumber k b := by
  obtain ⟨a, c, h, -⟩ := h
  exact ⟨a, c, h⟩

/-- The number of solutions `x ∈ {0, …, b - 1}` of `x² + k x + 1 ≡ 0 (mod b)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.5. -/
public def genMarkovCongruenceCount (k b : ℕ) : ℕ :=
  ((range b).filter fun x => b ∣ x ^ 2 + k * x + 1).card

/-- Characteristic value: `x² + 1 ≡ 0 (mod 5)` has the two solutions `2, 3`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.2. -/
public theorem genMarkovCongruenceCount_zero_five : genMarkovCongruenceCount 0 5 = 2 := by
  decide

/-- Theorem 1.5 (criterion): for a `k`-generalized Markov number `b ∉ {1, k + 2}`, if
`x² + k x + 1 ≡ 0 (mod b)` has at most two solutions then `b` is the maximum of a unique
`k`-generalized Markov triple up to order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.5. -/
public theorem_wanted hasUniqueMaxGenMarkovTriple_of_congruenceCount_le_two {k b : ℕ}
    (hb : IsGenMarkovNumber k b) (hb1 : b ≠ 1) (hbk : b ≠ k + 2)
    (hcount : genMarkovCongruenceCount k b ≤ 2) : HasUniqueMaxGenMarkovTriple k b

/-- Theorem 1.6: a `k`-generalized Markov number `b = p` or `b = 2p` with `p` prime is the
maximum of a unique `k`-generalized Markov triple up to order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.6. -/
public theorem_wanted hasUniqueMaxGenMarkovTriple_prime {k b p : ℕ} (hb : IsGenMarkovNumber k b)
    (hp : p.Prime) (hbp : b = p ∨ b = 2 * p) : HasUniqueMaxGenMarkovTriple k b

/-- Theorem 1.7: a `k`-generalized Markov number `b = p^m` or `2p^m` (`p` prime, `m ≥ 2`) is
the maximum of a unique triple when `k = 2`, or `k ≥ 4` is even and `p² ∤ k/2 + 1`,
`p² ∤ k/2 - 1`, or `k` is odd and `p² ∤ k + 2`, `p² ∤ k - 2` (in `ℤ`).

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.7. -/
public theorem_wanted hasUniqueMaxGenMarkovTriple_prime_pow {k b p m : ℕ}
    (hb : IsGenMarkovNumber k b) (hp : p.Prime) (hm : 2 ≤ m) (hbp : b = p ^ m ∨ b = 2 * p ^ m)
    (hk : k = 2 ∨ (4 ≤ k ∧ Even k ∧ ¬ p ^ 2 ∣ k / 2 + 1 ∧ ¬ p ^ 2 ∣ k / 2 - 1) ∨
      (Odd k ∧ ¬ (p : ℤ) ^ 2 ∣ (k : ℤ) + 2 ∧ ¬ (p : ℤ) ^ 2 ∣ (k : ℤ) - 2)) :
    HasUniqueMaxGenMarkovTriple k b

/-- Theorem 4.10: a `k`-generalized Markov number `b = p^m` or `2p^m` with `p` an odd prime,
`m ≥ 2` and `k² - 4 ≢ 0 (mod p)` is the maximum of a unique triple up to order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 4.10. -/
public theorem_wanted hasUniqueMaxGenMarkovTriple_odd_prime_pow {k b p m : ℕ}
    (hb : IsGenMarkovNumber k b) (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m)
    (hbp : b = p ^ m ∨ b = 2 * p ^ m) (hk : ¬ (p : ℤ) ∣ (k : ℤ) ^ 2 - 4) :
    HasUniqueMaxGenMarkovTriple k b

open Classical in
/-- Theorem 4.20: if `k ≥ 4` is even with `k/2 + 1`, `k/2 - 1` squarefree, or `k` is odd
with `k + 2`, `k - 2` squarefree (in `ℤ`), then a `k`-generalized Markov number
`b = p_1^{a_1} ⋯ p_n^{a_n}` or `2 p_1^{a_1} ⋯ p_n^{a_n}` (distinct odd primes `p_i`,
`n ≥ 1`) is the maximum of at most `2^{n-1}` triples up to order. Here `b` not divisible by
`4` encodes the two shapes and `n` is the number of odd prime factors of `b`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 4.20. -/
public theorem_wanted card_maxGenMarkovTriples_le {k b : ℕ}
    (hk : (4 ≤ k ∧ Even k ∧ Squarefree (k / 2 + 1) ∧ Squarefree (k / 2 - 1)) ∨
      (Odd k ∧ Squarefree ((k : ℤ) + 2) ∧ Squarefree ((k : ℤ) - 2)))
    (hb : IsGenMarkovNumber k b) (hb4 : ¬ 4 ∣ b)
    (hn : 1 ≤ (b.primeFactors.filter (· ≠ 2)).card) :
    ((range (b + 1) ×ˢ range (b + 1)).filter fun q =>
        q.1 ≤ q.2 ∧ IsGenMarkovTriple k q.1 b q.2).card ≤
      2 ^ ((b.primeFactors.filter (· ≠ 2)).card - 1)

/-- Proposition 2.3: the entries of a `k`-generalized Markov triple are pairwise coprime.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.3 (citing Gyoda and
Matsushita, Corollary 8). -/
public theorem_wanted IsGenMarkovTriple.pairwise_coprime {k a b c : ℕ}
    (h : IsGenMarkovTriple k a b c) :
    Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c

/-- Proposition 2.4: a rational triple `(a, b, c)` solves `GME(k)` if and only if
`((3 + 3k)a - k, (3 + 3k)b - k, (3 + 3k)c - k)` solves the `k`-generalized second Markov
equation `GSME(k)`: `x² + y² + z² + (k² + 2k)(x + y + z) + 2k³ + 3k² = x y z`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.4. -/
public theorem_wanted genMarkov_iff_genSecondMarkov (k : ℕ) (a b c : ℚ) :
    a ^ 2 + b ^ 2 + c ^ 2 + k * (b * c + c * a + a * b) = (3 + 3 * k) * a * b * c ↔
      let x := (3 + 3 * k) * a - k
      let y := (3 + 3 * k) * b - k
      let z := (3 + 3 * k) * c - k
      x ^ 2 + y ^ 2 + z ^ 2 + ((k : ℚ) ^ 2 + 2 * k) * (x + y + z) + 2 * (k : ℚ) ^ 3 +
          3 * (k : ℚ) ^ 2 = x * y * z

/-- Proposition 2.6: if `(a, b, c)` is an integer solution of `GSME(k)` then so are
`(a, ab - c - k² - 2k, b)` and `(b, bc - a - k² - 2k, c)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.6. -/
public theorem_wanted genSecondMarkov_vieta (k : ℕ) {a b c : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (a + b + c) + 2 * (k : ℤ) ^ 3 +
      3 * (k : ℤ) ^ 2 = a * b * c) :
    (let c' := a * b - c - (k : ℤ) ^ 2 - 2 * k;
      a ^ 2 + c' ^ 2 + b ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (a + c' + b) + 2 * (k : ℤ) ^ 3 +
        3 * (k : ℤ) ^ 2 = a * c' * b) ∧
    (let a' := b * c - a - (k : ℤ) ^ 2 - 2 * k;
      b ^ 2 + a' ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (b + a' + c) + 2 * (k : ℤ) ^ 3 +
        3 * (k : ℤ) ^ 2 = b * a' * c)

/-- Lemma 3.6: for `A, B ∈ SL(2, ℤ)`, `tr A = tr A⁻¹`, `tr(AB) = tr A tr B - tr(AB⁻¹)` and
`A² = (tr A) A - I`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.6 (citing Aigner, Lemma 4.2). -/
public theorem_wanted specialLinearGroup_two_trace_identities
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.trace ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ∧
      Matrix.trace ((A * B : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.trace (B : Matrix (Fin 2) (Fin 2) ℤ) -
          Matrix.trace ((A * B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
            Matrix (Fin 2) (Fin 2) ℤ) ∧
      (A : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 =
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) • (A : Matrix (Fin 2) (Fin 2) ℤ) - 1

/-- Lemma 4.9: for a prime `p`, `x² + k x + 1 ≡ 0 (mod p)` has at most two solutions.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.9. -/
public theorem_wanted genMarkovCongruenceCount_prime_le_two {p : ℕ} (hp : p.Prime) (k : ℕ) :
    genMarkovCongruenceCount k p ≤ 2

/-- Lemma 4.11: for an odd prime `p`, `m ≥ 2` and `k² - 4 ≢ 0 (mod p)`,
`x² + k x + 1 ≡ 0 (mod p^m)` has at most two solutions.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.11. -/
public theorem_wanted genMarkovCongruenceCount_prime_pow_le_two {p m k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 2 ≤ m) (hk : ¬ (p : ℤ) ∣ (k : ℤ) ^ 2 - 4) :
    genMarkovCongruenceCount k (p ^ m) ≤ 2

/-- Lemma 4.13: if some `k`-generalized Markov number is even, then `k` is even.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.13. -/
public theorem_wanted even_of_even_genMarkovNumber {k b : ℕ} (hb : IsGenMarkovNumber k b)
    (he : Even b) : Even k

/-- Proposition 4.14: if some `k`-generalized Markov number is a multiple of `4`, then
`k ≡ 2 (mod 4)`. (The paper's "in particular" consequence, a parity statement whose
displayed fraction is garbled in the record, is omitted.)

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.14. -/
public theorem_wanted mod_four_eq_two_of_four_dvd_genMarkovNumber {k b : ℕ}
    (hb : IsGenMarkovNumber k b) (h4 : 4 ∣ b) : k % 4 = 2

/-- Proposition 4.15: for an odd prime `p`, if `k ≥ 4` is even and `p > k/2 + 1`, or `k` is
odd and `p > k + 2`, then `k² - 4 ≢ 0 (mod p)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.15. -/
public theorem_wanted not_dvd_sq_sub_four_of_large_prime {k p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : (4 ≤ k ∧ Even k ∧ k / 2 + 1 < p) ∨ (Odd k ∧ k + 2 < p)) :
    ¬ (p : ℤ) ∣ (k : ℤ) ^ 2 - 4

/-- Proposition 4.16, in the setting of its proof: for an odd prime `p`, if some
`k`-generalized Markov number equals `p^m` or `2p^m` with `m ≥ 2`, and `k ≥ 4` is even with
`p² ∤ k/2 + 1`, `p² ∤ k/2 - 1`, or `k` is odd with `p² ∤ k + 2`, `p² ∤ k - 2`, then
`k² - 4 ≢ 0 (mod p)`. As printed (without the Markov-number hypothesis) the claim is false:
`k = 4`, `p = 3` satisfy the divisibility conditions (`9 ∤ 3`, `9 ∤ 1`) but `3 ∣ 12`; the
paper's proof assumes `b = p^m` is a `k`-generalized Markov number and uses `m ≥ 2`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.16 and its proof. -/
public theorem_wanted not_dvd_sq_sub_four_of_genMarkovNumber_prime_pow {k p m b : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m) (hb : IsGenMarkovNumber k b)
    (hbp : b = p ^ m ∨ b = 2 * p ^ m)
    (hk : (4 ≤ k ∧ Even k ∧ ¬ p ^ 2 ∣ k / 2 + 1 ∧ ¬ p ^ 2 ∣ k / 2 - 1) ∨
      (Odd k ∧ ¬ (p : ℤ) ^ 2 ∣ (k : ℤ) + 2 ∧ ¬ (p : ℤ) ^ 2 ∣ (k : ℤ) - 2)) :
    ¬ (p : ℤ) ∣ (k : ℤ) ^ 2 - 4

/-- Proposition 4.17: `(a, b, c)` is a Markov triple (`k = 0`) exactly when `(a², b², c²)` is
a `2`-generalized Markov triple; conversely every `2`-generalized Markov triple consists of
squares of a Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.17 (citing Gyoda and
Matsushita, Theorem 2.9). -/
public theorem_wanted genMarkovTriple_two_iff_sq :
    (∀ a b c : ℕ, IsGenMarkovTriple 0 a b c → IsGenMarkovTriple 2 (a ^ 2) (b ^ 2) (c ^ 2)) ∧
      ∀ A B C : ℕ, IsGenMarkovTriple 2 A B C →
        ∃ a b c : ℕ, A = a ^ 2 ∧ B = b ^ 2 ∧ C = c ^ 2 ∧ IsGenMarkovTriple 0 a b c

/-- Theorem 1.2 (classical criterion, `k = 0`): for a Markov number `b ∉ {1, 2}`, if
`x² + 1 ≡ 0 (mod b)` has at most two solutions, then `b` is the maximum of a unique Markov
triple up to order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.2 (citing Aigner,
Corollary 3.17). -/
public theorem_wanted markov_hasUniqueMaxTriple_of_congruenceCount_le_two {b : ℕ}
    (hb : IsGenMarkovNumber 0 b) (hb1 : b ≠ 1) (hb2 : b ≠ 2)
    (hcount : genMarkovCongruenceCount 0 b ≤ 2) : HasUniqueMaxGenMarkovTriple 0 b

/-- Theorem 1.3 (classical, `k = 0`): a Markov number `b = p^m` or `2p^m` with `p` an odd
prime and `m ≥ 1` is the maximum of a unique Markov triple up to order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.3 (citing Aigner,
Corollary 3.20). -/
public theorem_wanted markov_hasUniqueMaxTriple_odd_prime_pow {b p m : ℕ}
    (hb : IsGenMarkovNumber 0 b) (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hbp : b = p ^ m ∨ b = 2 * p ^ m) : HasUniqueMaxGenMarkovTriple 0 b

/-- Proposition 1.11 (classical, `k = 0`): let `m ≥ 5` be a Markov number and `(m, m₂, m₃)`,
`(m, n₂, n₃)` Markov triples with maximum `m`. If they share a characteristic number, i.e.
some `0 < x < m` satisfies `m₂ x ≡ ± m₃` and `n₂ x ≡ ± n₃ (mod m)`, then
`{m₂, m₃} = {n₂, n₃}`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 1.11 (citing Aigner,
Proposition 3.15). -/
public theorem_wanted markov_eq_of_characteristic_number_eq {m m₂ m₃ n₂ n₃ x : ℕ}
    (hm : 5 ≤ m) (h₁ : IsGenMarkovTriple 0 m m₂ m₃) (h₂ : IsGenMarkovTriple 0 m n₂ n₃)
    (hm₁ : m₂ ≤ m ∧ m₃ ≤ m) (hm₂ : n₂ ≤ m ∧ n₃ ≤ m) (hx : 0 < x ∧ x < m)
    (hu₁ : (m : ℤ) ∣ m₂ * x - m₃ ∨ (m : ℤ) ∣ m₂ * x + m₃)
    (hu₂ : (m : ℤ) ∣ n₂ * x - n₃ ∨ (m : ℤ) ∣ n₂ * x + n₃) :
    (m₂ = n₂ ∧ m₃ = n₃) ∨ (m₂ = n₃ ∧ m₃ = n₂)

/-! ### Part 2: Markov trees, generalized Cohn trees, Farey tree and fraction labeling -/

/-- One Vieta jumping of `GME(k)`: `false` is the left jumping
`(a, b, c) ↦ (a, (a² + kab + b²)/c, b)`, `true` the right jumping
`(a, b, c) ↦ (b, (b² + kbc + c²)/a, c)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def genMarkovVieta (k : ℕ) : Bool → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | false, (a, b, c) => (a, (a ^ 2 + k * a * b + b ^ 2) / c, b)
  | true, (a, b, c) => (b, (b ^ 2 + k * b * c + c ^ 2) / a, c)

/-- The vertex of the wide `k`-generalized Markov tree `WMT(k)` reached from the root
`(1, 1, 1)` along the path `w` (`false` = left child, `true` = right child).

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def wideGenMarkovTree (k : ℕ) (w : List Bool) : ℕ × ℕ × ℕ :=
  w.foldl (fun t d => genMarkovVieta k d t) (1, 1, 1)

/-- The vertex of the `k`-generalized Markov tree `MT(k)`, the full subtree of `WMT(k)` rooted
at the left child of the root, reached along the path `w`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def genMarkovTree (k : ℕ) (w : List Bool) : ℕ × ℕ × ℕ :=
  wideGenMarkovTree k (false :: w)

/-- Characteristic lemma: children in `WMT(k)` are Vieta jumpings of their parent.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public theorem wideGenMarkovTree_append_singleton (k : ℕ) (w : List Bool) (d : Bool) :
    wideGenMarkovTree k (w ++ [d]) = genMarkovVieta k d (wideGenMarkovTree k w) := by
  simp [wideGenMarkovTree, List.foldl_append]

/-- Characteristic value: the root of `MT(k)` is `(1, k + 2, 1)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 4. -/
public theorem genMarkovTree_nil (k : ℕ) : genMarkovTree k [] = (1, k + 2, 1) := by
  simp only [genMarkovTree, wideGenMarkovTree, List.foldl_cons, List.foldl_nil, genMarkovVieta]
  congr 2
  rw [Nat.div_one]
  ring

/-- Characteristic value: for `k = 0` the left child of the root of `MT(0)` is `(1, 5, 2)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public theorem genMarkovTree_zero_false : genMarkovTree 0 [false] = (1, 5, 2) := by
  decide

/-- Proposition 2.1: every vertex of `WMT(k)` is a `k`-generalized Markov triple, and every
`k`-generalized Markov triple `(a, b, c)` with `b > max {a, c}` appears exactly twice in
`WMT(k)`: once among the left descendants of the root and once among the right ones.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.1 (citing Gyoda and
Matsushita, Theorem 1). -/
public theorem_wanted wideGenMarkovTree_isGenMarkovTriple_and_twice (k : ℕ) :
    (∀ w, IsGenMarkovTriple k (wideGenMarkovTree k w).1 (wideGenMarkovTree k w).2.1
      (wideGenMarkovTree k w).2.2) ∧
    ∀ a b c, IsGenMarkovTriple k a b c → a < b → c < b →
      (∃! w, wideGenMarkovTree k (false :: w) = (a, b, c)) ∧
        ∃! w, wideGenMarkovTree k (true :: w) = (a, b, c)

/-- Corollary 2.2: every vertex of `MT(k)` is a `k`-generalized Markov triple, and every
`k`-generalized Markov triple `(a, b, c)` with `b > max {a, c}` appears exactly once in
`MT(k)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 2.2. -/
public theorem_wanted genMarkovTree_isGenMarkovTriple_and_once (k : ℕ) :
    (∀ w, IsGenMarkovTriple k (genMarkovTree k w).1 (genMarkovTree k w).2.1
      (genMarkovTree k w).2.2) ∧
    ∀ a b c, IsGenMarkovTriple k a b c → a < b → c < b → ∃! w, genMarkovTree k w = (a, b, c)

/-- The integer presentation of the Vieta jumpings displayed after Corollary 2.2: for a
`k`-generalized Markov triple, `(a² + kab + b²)/c = (3 + 3k)ab - c - k(a + b)` and
`(b² + kbc + c²)/a = (3 + 3k)bc - a - k(b + c)`, stated without division.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2 (display after
Corollary 2.2). -/
public theorem_wanted IsGenMarkovTriple.vieta_eq {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    ((a : ℤ) ^ 2 + k * a * b + b ^ 2 = c * ((3 + 3 * k) * a * b - c - k * (a + b))) ∧
      ((b : ℤ) ^ 2 + k * b * c + c ^ 2 = a * ((3 + 3 * k) * b * c - a - k * (b + c)))

/-- An induced positive solution of the `k`-generalized second Markov equation `GSME(k)`:
a positive integer solution `(a, b, c)` with `(a + k)/(3 + 3k)`, `(b + k)/(3 + 3k)`,
`(c + k)/(3 + 3k)` positive integers (positivity is automatic from `a, b, c > 0`).

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def IsInducedGenSecondMarkovSolution (k : ℕ) (a b c : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧
    a ^ 2 + b ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (a + b + c) + 2 * (k : ℤ) ^ 3 +
      3 * (k : ℤ) ^ 2 = a * b * c ∧
    (3 + 3 * (k : ℤ)) ∣ a + k ∧ (3 + 3 * (k : ℤ)) ∣ b + k ∧ (3 + 3 * (k : ℤ)) ∣ c + k

/-- Characteristic value: `(3 + 2k, 3 + 2k, 3 + 2k)`, the image of `(1, 1, 1)`, is an induced
solution of `GSME(k)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public theorem isInducedGenSecondMarkovSolution_root (k : ℕ) :
    IsInducedGenSecondMarkovSolution k (3 + 2 * k) (3 + 2 * k) (3 + 2 * k) := by
  refine ⟨by positivity, by positivity, by positivity, by ring, ⟨1, by ring⟩, ⟨1, by ring⟩,
    ⟨1, by ring⟩⟩

/-- Proposition 2.7: if `(a, b, c)` is an induced solution of `GSME(k)`, then so are
`(a, ab - c - k² - 2k, b)` and `(b, bc - a - k² - 2k, c)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.7. -/
public theorem_wanted IsInducedGenSecondMarkovSolution.vieta {k : ℕ} {a b c : ℤ}
    (h : IsInducedGenSecondMarkovSolution k a b c) :
    IsInducedGenSecondMarkovSolution k a (a * b - c - (k : ℤ) ^ 2 - 2 * k) b ∧
      IsInducedGenSecondMarkovSolution k b (b * c - a - (k : ℤ) ^ 2 - 2 * k) c

/-- Corollary 2.8: the tree `SMT(k)`, obtained from `MT(k)` by replacing each vertex
`(a, b, c)` with `((3 + 3k)a - k, (3 + 3k)b - k, (3 + 3k)c - k)`, consists of induced solutions
of `GSME(k)`, and each induced solution `(a, b, c)` with `b > max {a, c}` appears exactly once.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 2.8. -/
public theorem_wanted genSecondMarkovTree_induced_and_once (k : ℕ) :
    (∀ w, IsInducedGenSecondMarkovSolution k ((3 + 3 * k) * ((genMarkovTree k w).1 : ℤ) - k)
      ((3 + 3 * k) * ((genMarkovTree k w).2.1 : ℤ) - k)
      ((3 + 3 * k) * ((genMarkovTree k w).2.2 : ℤ) - k)) ∧
    ∀ a b c, IsInducedGenSecondMarkovSolution k a b c → a < b → c < b →
      ∃! w, ((3 + 3 * k) * ((genMarkovTree k w).1 : ℤ) - k,
        (3 + 3 * k) * ((genMarkovTree k w).2.1 : ℤ) - k,
        (3 + 3 * k) * ((genMarkovTree k w).2.2 : ℤ) - k) = (a, b, c)

/-- The matrix `S = [[k, 0], [3k² + 3k, k]]` of the `k`-generalized Cohn triple relation
`Q = PR - S`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.2. -/
public def genCohnS (k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(k : ℤ), 0; 3 * (k : ℤ) ^ 2 + 3 * k, k]

/-- Characteristic value: for `k = 0` the matrix `S` vanishes (classical Cohn triples
`Q = PR`).

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.3. -/
public theorem genCohnS_zero : genCohnS 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [genCohnS]

/-- A `k`-generalized Cohn matrix: an integer `2 × 2` matrix `P` of determinant `1` whose
`(1, 2)`-entry `p₁₂` is a `k`-generalized Markov number and whose trace is
`(3 + 3k) p₁₂ - k`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.1. -/
public def IsGenCohnMatrix (k : ℕ) (P : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  P.det = 1 ∧ ∃ n : ℕ, P 0 1 = n ∧ IsGenMarkovNumber k n ∧ P.trace = (3 + 3 * k) * n - k

/-- `(P, Q, R)` is a `k`-generalized Cohn triple associated with `(a, b, c)`: `P, Q, R` are
`k`-generalized Cohn matrices, `Q = PR - S`, and their `(1, 2)`-entries `(a, b, c)` form a
`k`-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.2. -/
public def IsGenCohnTriple (k : ℕ) (P Q R : Matrix (Fin 2) (Fin 2) ℤ) (a b c : ℕ) : Prop :=
  IsGenCohnMatrix k P ∧ IsGenCohnMatrix k Q ∧ IsGenCohnMatrix k R ∧ Q = P * R - genCohnS k ∧
    P 0 1 = a ∧ Q 0 1 = b ∧ R 0 1 = c ∧ IsGenMarkovTriple k a b c

/-- Characteristic lemma: the associated triple of a `k`-generalized Cohn triple is a
`k`-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.2. -/
public theorem IsGenCohnTriple.isGenMarkovTriple {k : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    {a b c : ℕ} (h : IsGenCohnTriple k P Q R a b c) : IsGenMarkovTriple k a b c :=
  h.2.2.2.2.2.2.2

/-- The matrix `P_{1;ℓ} = [[ℓ, 1], [-ℓ² + 2kℓ + 3ℓ - 1, -ℓ + 2k + 3]]`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnP1 (k : ℕ) (ℓ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![ℓ, 1; -ℓ ^ 2 + 2 * k * ℓ + 3 * ℓ - 1, -ℓ + 2 * k + 3]

/-- The matrix `Q_{1;ℓ} = [[k + ℓ + 1, 1], [k² - ℓ² + 3k + ℓ + 1, k - ℓ + 2]]`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnQ1 (k : ℕ) (ℓ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![k + ℓ + 1, 1; (k : ℤ) ^ 2 - ℓ ^ 2 + 3 * k + ℓ + 1, k - ℓ + 2]

/-- The matrix `R_{1;ℓ} = [[2k + ℓ + 2, 1], [-ℓ² - 2kℓ + 2k - ℓ + 1, -ℓ + 1]]`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnR1 (k : ℕ) (ℓ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2 * k + ℓ + 2, 1; -ℓ ^ 2 - 2 * k * ℓ + 2 * k - ℓ + 1, -ℓ + 1]

/-- Characteristic lemma: `P_{1;ℓ}`, `Q_{1;ℓ}`, `R_{1;ℓ}` have determinant `1`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public theorem genCohnPQR1_det (k : ℕ) (ℓ : ℤ) :
    (genCohnP1 k ℓ).det = 1 ∧ (genCohnQ1 k ℓ).det = 1 ∧ (genCohnR1 k ℓ).det = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [genCohnP1, genCohnQ1, genCohnR1, Matrix.det_fin_two_of] <;> ring

/-- One step of the wide `k`-generalized Cohn tree: `false` maps `(P, Q, R)` to its left
child `(P, PQ - S, Q)`, `true` to its right child `(Q, QR - S, R)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnStep (k : ℕ) : Bool →
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ →
      Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ
  | false, (P, Q, _) => (P, P * Q - genCohnS k, Q)
  | true, (_, Q, R) => (Q, Q * R - genCohnS k, R)

/-- The triple reached from `T` by applying the steps of the path `w` in order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.10. -/
public def genCohnPath (k : ℕ)
    (T : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ)
    (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ :=
  w.foldl (fun T d => genCohnStep k d T) T

/-- The vertex of the wide `k`-generalized Cohn tree `WGCT(k, ℓ)`, rooted at
`(P_{1;ℓ}, Q_{1;ℓ}, R_{1;ℓ})`, reached along the path `w`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def wideGenCohnTree (k : ℕ) (ℓ : ℤ) (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ :=
  genCohnPath k (genCohnP1 k ℓ, genCohnQ1 k ℓ, genCohnR1 k ℓ) w

/-- The vertex of the `k`-generalized Cohn tree `GCT(k, ℓ)`, the full subtree of
`WGCT(k, ℓ)` rooted at the left child of its root, reached along the path `w`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnTree (k : ℕ) (ℓ : ℤ) (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ :=
  wideGenCohnTree k ℓ (false :: w)

/-- Characteristic lemma: children in `WGCT(k, ℓ)` are steps from their parent.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public theorem wideGenCohnTree_append_singleton (k : ℕ) (ℓ : ℤ) (w : List Bool) (d : Bool) :
    wideGenCohnTree k ℓ (w ++ [d]) = genCohnStep k d (wideGenCohnTree k ℓ w) := by
  simp [wideGenCohnTree, genCohnPath, List.foldl_append]

/-- Theorem 1.9 (classical, `k = 0`, where `S = 0` so the steps are `(P, PQ, Q)` and
`(Q, QR, R)`): every Cohn triple associated with `(a, b, c)`, `b ≥ max {a, c}`, is obtained by
applying the steps successively to a Cohn triple associated with `(1, 1, 1)`, and on
`(1, 2)`-entries the steps are the Vieta jumpings of Markov triples.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.9 (citing Aigner,
Theorem 4.7). -/
public theorem_wanted cohnTriple_reachable :
    (∀ P Q R a b c, IsGenCohnTriple 0 P Q R a b c → a ≤ b → c ≤ b →
      ∃ P₀ Q₀ R₀ w, IsGenCohnTriple 0 P₀ Q₀ R₀ 1 1 1 ∧ genCohnPath 0 (P₀, Q₀, R₀) w = (P, Q, R)) ∧
    ∀ P Q R a b c d, IsGenCohnTriple 0 P Q R a b c →
      (genCohnStep 0 d (P, Q, R)).1 0 1 = (genMarkovVieta 0 d (a, b, c)).1 ∧
        (genCohnStep 0 d (P, Q, R)).2.1 0 1 = (genMarkovVieta 0 d (a, b, c)).2.1 ∧
        (genCohnStep 0 d (P, Q, R)).2.2 0 1 = (genMarkovVieta 0 d (a, b, c)).2.2

/-- Theorem 1.10: every `k`-generalized Cohn triple associated with `(a, b, c)`,
`b ≥ max {a, c}`, is obtained by applying `(P, Q, R) ↦ (P, PQ - S, Q)` or
`(P, Q, R) ↦ (Q, QR - S, R)` successively to a `k`-generalized Cohn triple associated with
`(1, 1, 1)`, and on `(1, 2)`-entries these steps are the Vieta jumpings of `GME(k)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.10. -/
public theorem_wanted genCohnTriple_reachable (k : ℕ) :
    (∀ P Q R a b c, IsGenCohnTriple k P Q R a b c → a ≤ b → c ≤ b →
      ∃ P₀ Q₀ R₀ w, IsGenCohnTriple k P₀ Q₀ R₀ 1 1 1 ∧ genCohnPath k (P₀, Q₀, R₀) w = (P, Q, R)) ∧
    ∀ P Q R a b c d, IsGenCohnTriple k P Q R a b c →
      (genCohnStep k d (P, Q, R)).1 0 1 = (genMarkovVieta k d (a, b, c)).1 ∧
        (genCohnStep k d (P, Q, R)).2.1 0 1 = (genMarkovVieta k d (a, b, c)).2.1 ∧
        (genCohnStep k d (P, Q, R)).2.2 0 1 = (genMarkovVieta k d (a, b, c)).2.2

/-- Proposition 3.4: for every `ℓ ∈ ℤ`, `(P_{1;ℓ}, Q_{1;ℓ}, R_{1;ℓ})` is a `k`-generalized Cohn
triple (associated with `(1, 1, 1)`); conversely every `k`-generalized Cohn triple associated
with `(1, 1, 1)` is of this form.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 3.4. -/
public theorem_wanted isGenCohnTriple_one_iff (k : ℕ) :
    (∀ ℓ, IsGenCohnTriple k (genCohnP1 k ℓ) (genCohnQ1 k ℓ) (genCohnR1 k ℓ) 1 1 1) ∧
    ∀ P Q R, IsGenCohnTriple k P Q R 1 1 1 →
      ∃ ℓ, P = genCohnP1 k ℓ ∧ Q = genCohnQ1 k ℓ ∧ R = genCohnR1 k ℓ

/-- Theorem 3.5: if `(P, Q, R)` is a `k`-generalized Cohn triple associated with `(a, b, c)`,
then `(P, PQ - S, Q)` is one associated with `(a, (a² + kab + b²)/c, b)` and `(Q, QR - S, R)`
one associated with `(b, (b² + kbc + c²)/a, c)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 3.5. -/
public theorem_wanted IsGenCohnTriple.step {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    IsGenCohnTriple k P (P * Q - genCohnS k) Q a ((a ^ 2 + k * a * b + b ^ 2) / c) b ∧
      IsGenCohnTriple k Q (Q * R - genCohnS k) R b ((b ^ 2 + k * b * c + c ^ 2) / a) c

/-- Lemma 3.7: for a `k`-generalized Cohn matrix `M` and `E = [[0, 0], [3 + 3k, 0]]`,
`M E M = (tr M + k) M + E` and `M⁻¹ E M⁻¹ = -(tr M⁻¹ + k) M⁻¹ + E`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.7. -/
public theorem_wanted IsGenCohnMatrix.mul_E_mul {k : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : IsGenCohnMatrix k M) :
    M * !![0, 0; 3 + 3 * (k : ℤ), 0] * M =
        (M.trace + (k : ℤ)) • M + !![0, 0; 3 + 3 * (k : ℤ), 0] ∧
      M⁻¹ * !![0, 0; 3 + 3 * (k : ℤ), 0] * M⁻¹ =
        (-(M⁻¹.trace + (k : ℤ))) • M⁻¹ + !![0, 0; 3 + 3 * (k : ℤ), 0]

/-- Corollary 3.9: the map `(P, Q, R) ↦ (p₁₂, q₁₂, r₁₂)` is the canonical graph isomorphism
`WGCT(k, ℓ) → WMT(k)`: the vertex of `WGCT(k, ℓ)` at each path is a `k`-generalized Cohn triple
associated with the vertex of `WMT(k)` at the same path. In particular every
`k`-generalized Markov triple `(a, b, c)` with `b ≥ max {a, c}` has an associated
`k`-generalized Cohn triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 3.9. -/
public theorem_wanted wideGenCohnTree_isGenCohnTriple (k : ℕ) (ℓ : ℤ) :
    (∀ w, IsGenCohnTriple k (wideGenCohnTree k ℓ w).1 (wideGenCohnTree k ℓ w).2.1
      (wideGenCohnTree k ℓ w).2.2 (wideGenMarkovTree k w).1 (wideGenMarkovTree k w).2.1
      (wideGenMarkovTree k w).2.2) ∧
    ∀ a b c, IsGenMarkovTriple k a b c → a ≤ b → c ≤ b → ∃ P Q R, IsGenCohnTriple k P Q R a b c

/-- Proposition 3.10: every `k`-generalized Cohn triple associated with `(a, b, c)`,
`b ≥ max {a, c}`, is a vertex of `WGCT(k, ℓ)` for some `ℓ ∈ ℤ`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 3.10. -/
public theorem_wanted IsGenCohnTriple.mem_wideGenCohnTree {k a b c : ℕ}
    {P Q R : Matrix (Fin 2) (Fin 2) ℤ} (h : IsGenCohnTriple k P Q R a b c) (hab : a ≤ b)
    (hcb : c ≤ b) : ∃ ℓ w, wideGenCohnTree k ℓ w = (P, Q, R)

/-- Lemma 3.11: if `(P, Q, R)` is a `k`-generalized Cohn triple associated with `(a, b, c)`,
then `(P, R, P⁻¹(R + S))` is one associated with `(a, c, b')` and `((P + S)R⁻¹, P, R)` one
associated with `(b', a, c)`, where `b' = (a² + kac + c²)/b`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.11. -/
public theorem_wanted IsGenCohnTriple.parent {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    IsGenCohnTriple k P R (P⁻¹ * (R + genCohnS k)) a c ((a ^ 2 + k * a * c + c ^ 2) / b) ∧
      IsGenCohnTriple k ((P + genCohnS k) * R⁻¹) P R ((a ^ 2 + k * a * c + c ^ 2) / b) a c

/-- Theorem 3.13: the second entries of the vertices of `WGCT(k, ℓ)` are pairwise distinct.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 3.13. -/
public theorem_wanted wideGenCohnTree_snd_injective (k : ℕ) (ℓ : ℤ) :
    Function.Injective fun w => (wideGenCohnTree k ℓ w).2.1

/-- Corollary 3.15: the vertex of `GCT(k, ℓ)` at each path is a `k`-generalized Cohn triple
associated with the vertex of `MT(k)` at the same path (the canonical graph isomorphism
`GCT(k, ℓ) → MT(k)`).

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 3.15. -/
public theorem_wanted genCohnTree_isGenCohnTriple (k : ℕ) (ℓ : ℤ) (w : List Bool) :
    IsGenCohnTriple k (genCohnTree k ℓ w).1 (genCohnTree k ℓ w).2.1 (genCohnTree k ℓ w).2.2
      (genMarkovTree k w).1 (genMarkovTree k w).2.1 (genMarkovTree k w).2.2

/-- Corollary 3.16: the second entries of the vertices of `GCT(k, ℓ)` are pairwise distinct.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 3.16. -/
public theorem_wanted genCohnTree_snd_injective (k : ℕ) (ℓ : ℤ) :
    Function.Injective fun w => (genCohnTree k ℓ w).2.1

/-- Proposition 3.17: a `k`-generalized Cohn triple associated with `(a, b, c)`,
`b > max {a, c}`, is the vertex of `GCT(k, ℓ)` for a unique pair of `ℓ ∈ ℤ` and path.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 3.17. -/
public theorem_wanted IsGenCohnTriple.existsUnique_mem_genCohnTree {k a b c : ℕ}
    {P Q R : Matrix (Fin 2) (Fin 2) ℤ} (h : IsGenCohnTriple k P Q R a b c) (hab : a < b)
    (hcb : c < b) : ∃! p : ℤ × List Bool, genCohnTree k p.1 p.2 = (P, Q, R)

/-- The vertex of the Farey tree `FT`, rooted at `(0/1, 1/1, 1/0)` with children
`(a/b, (a+c)/(b+d), c/d)` and `(c/d, (c+e)/(d+f), e/f)`, reached along the path `w`.
A fraction `n/d` is the pair `(n, d)`, and `1/0` stands for `∞`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public def fareyTree (w : List Bool) : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) :=
  w.foldl (fun T d => match d, T with
    | false, (x, y, _) => (x, (x.1 + y.1, x.2 + y.2), y)
    | true, (_, y, z) => (y, (y.1 + z.1, y.2 + z.2), z)) ((0, 1), (1, 1), (1, 0))

/-- Characteristic value: the left child of the root of `FT` is `(0/1, 1/2, 1/1)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 4. -/
public theorem fareyTree_false : fareyTree [false] = ((0, 1), (1, 2), (1, 1)) := by
  decide

/-- A Farey triple `(a/b, c/d, e/f)`: all three fractions are irreducible (`gcd = 1`, which
admits `0/1` and `1/0`) and `|det(a/b, c/d)| = |det(c/d, e/f)| = |det(e/f, a/b)| = 1`, where
`det(a/b, c/d) = ad - bc`. (The printed condition writes `d/e` for `e/f`.)

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public def IsFareyTriple (x y z : ℕ × ℕ) : Prop :=
  Nat.Coprime x.1 x.2 ∧ Nat.Coprime y.1 y.2 ∧ Nat.Coprime z.1 z.2 ∧
    |(x.1 : ℤ) * y.2 - x.2 * y.1| = 1 ∧ |(y.1 : ℤ) * z.2 - y.2 * z.1| = 1 ∧
    |(z.1 : ℤ) * x.2 - z.2 * x.1| = 1

/-- Characteristic value: the root `(0/1, 1/1, 1/0)` of `FT` is a Farey triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public theorem isFareyTriple_root : IsFareyTriple (0, 1) (1, 1) (1, 0) := by
  unfold IsFareyTriple
  decide

/-- Proposition 3.22: (1) the children of a Farey triple are Farey triples, so every vertex
of `FT` is one; (2) every irreducible `a/b > 0` is the second entry of a unique vertex of
`FT`; (3) every vertex `(a/b, c/d, e/f)` of `FT` has `a/b < c/d < e/f` (compared by cross
multiplication, so that `1/0 = ∞` is largest).

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 3.22 (citing Aigner,
Section 3.2). -/
public theorem_wanted fareyTree_properties :
    (∀ x y z, IsFareyTriple x y z →
      IsFareyTriple x (x.1 + y.1, x.2 + y.2) y ∧ IsFareyTriple y (y.1 + z.1, y.2 + z.2) z) ∧
    (∀ w, IsFareyTriple (fareyTree w).1 (fareyTree w).2.1 (fareyTree w).2.2) ∧
    (∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → ∃! w, (fareyTree w).2.1 = (a, b)) ∧
    ∀ w, (fareyTree w).1.1 * (fareyTree w).2.1.2 < (fareyTree w).2.1.1 * (fareyTree w).1.2 ∧
      (fareyTree w).2.1.1 * (fareyTree w).2.2.2 < (fareyTree w).2.2.1 * (fareyTree w).2.1.2

/-- The fraction labeling of `k`-generalized Cohn matrices: `C = C_q(k, ℓ)` when `q` and `C`
sit at the same position of the vertices of `FT` and `GCT(k, ℓ)` at the same path (the
paper labels second entries; first and third entries carry the labels of the vertex where
they were created, which gives `C_{0/1}` and `C_{1/0}`).

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public def IsGenCohnLabel (k : ℕ) (ℓ : ℤ) (q : ℕ × ℕ) (C : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ w, ((fareyTree w).1 = q ∧ (genCohnTree k ℓ w).1 = C) ∨
    ((fareyTree w).2.1 = q ∧ (genCohnTree k ℓ w).2.1 = C) ∨
    ((fareyTree w).2.2 = q ∧ (genCohnTree k ℓ w).2.2 = C)

/-- Characteristic lemma: the second entry of the root of `GCT(k, ℓ)` is labeled `1/1`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public theorem isGenCohnLabel_one (k : ℕ) (ℓ : ℤ) :
    IsGenCohnLabel k ℓ (1, 1) (genCohnTree k ℓ []).2.1 :=
  ⟨[], Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

/-- Corollary 3.23: the fraction labeling of `k`-generalized Cohn matrices is injective, and
it is strictly increasing for the index `I_M = m₁₁/m₁₂`: `p < q` implies
`I_{C_p(k, ℓ)} < I_{C_q(k, ℓ)}` (fractions compared by cross multiplication).

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 3.23. -/
public theorem_wanted genCohnLabel_injective_index_strictMono (k : ℕ) (ℓ : ℤ) :
    (∀ q q' C, IsGenCohnLabel k ℓ q C → IsGenCohnLabel k ℓ q' C → q = q') ∧
    ∀ q q' C C', IsGenCohnLabel k ℓ q C → IsGenCohnLabel k ℓ q' C' → q.1 * q'.2 < q'.1 * q.2 →
      (C 0 0 : ℚ) / C 0 1 < (C' 0 0 : ℚ) / C' 0 1

/-- The fraction labeling of `k`-generalized Markov numbers: `m = m_q` when `q` and `m` sit
at the same position of the vertices of `FT` and `MT(k)` at the same path; on `[0, 1]` this
gives `m_{0/1} = 1`, `m_{1/1} = k + 2` and the paper's `m_t` for `t ∈ (0, 1)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 4. -/
public def IsGenMarkovLabel (k : ℕ) (q : ℕ × ℕ) (m : ℕ) : Prop :=
  ∃ w, ((fareyTree w).1 = q ∧ (genMarkovTree k w).1 = m) ∨
    ((fareyTree w).2.1 = q ∧ (genMarkovTree k w).2.1 = m) ∨
    ((fareyTree w).2.2 = q ∧ (genMarkovTree k w).2.2 = m)

/-- Characteristic value: `m_{1/1} = k + 2`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 4. -/
public theorem isGenMarkovLabel_one (k : ℕ) : IsGenMarkovLabel k (1, 1) (k + 2) :=
  ⟨[], Or.inr (Or.inl ⟨rfl, by rw [genMarkovTree_nil]⟩)⟩

/-- Proposition 4.1: a `k`-generalized Markov number `b` is the maximum of a unique
`k`-generalized Markov triple up to order if and only if `b = m_t` for a unique irreducible
fraction `t ∈ [0, 1]`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.1. -/
public theorem_wanted hasUniqueMaxGenMarkovTriple_iff_existsUnique_label {k b : ℕ}
    (hb : IsGenMarkovNumber k b) :
    HasUniqueMaxGenMarkovTriple k b ↔ ∃! q : ℕ × ℕ, q.1 ≤ q.2 ∧ IsGenMarkovLabel k q b

/-- Corollary 4.2: Conjecture 1.8 for `k` (every `k`-generalized Markov number is the maximum
of a unique triple up to order) holds if and only if the fraction labeling `t ↦ m_t` on
`[0, 1]` is injective.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 4.2. -/
public theorem_wanted genMarkovUniqueness_iff_label_injective (k : ℕ) :
    (∀ b, IsGenMarkovNumber k b → HasUniqueMaxGenMarkovTriple k b) ↔
      ∀ q q' m, q.1 ≤ q.2 → q'.1 ≤ q'.2 → IsGenMarkovLabel k q m → IsGenMarkovLabel k q' m →
        q = q'

/-- `x` is the characteristic number of `(m_r, m_t, m_s)`: `0 < x < m_t/2` and
`m_r x ≡ ± m_s (mod m_t)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 4.3. -/
public def IsGenMarkovCharNumber (mr mt ms x : ℕ) : Prop :=
  0 < x ∧ 2 * x < mt ∧ ((mt : ℤ) ∣ mr * x - ms ∨ (mt : ℤ) ∣ mr * x + ms)

/-- Characteristic value: `2` is the characteristic number of the Markov triple `(1, 5, 2)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 4.3. -/
public theorem isGenMarkovCharNumber_one_five_two : IsGenMarkovCharNumber 1 5 2 2 := by
  refine ⟨by norm_num, by norm_num, Or.inl ⟨0, by norm_num⟩⟩

/-- Lemma 4.4: for an irreducible fraction `t ∈ (0, 1)`, the `(1, 1)`-entry of `C_t(k, -k)` is
positive.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.4. -/
public theorem_wanted genCohnTree_neg_snd_entry_pos (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) :
    0 < (genCohnTree k (-k) w).2.1 0 0

/-- Lemma 4.5: for an irreducible fraction `t ∈ (0, 1)` with Farey vertex `(r, t, s)`,
`C_t(k, -k) = [[u_t, m_t], [*, (3 + 3k)m_t - u_t - k]]`, where `u_t` is the characteristic
number of `(m_r, m_t, m_s)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.5. -/
public theorem_wanted genCohnTree_neg_snd_eq (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) :
    ∃ u, IsGenMarkovCharNumber (genMarkovTree k w).1 (genMarkovTree k w).2.1
        (genMarkovTree k w).2.2 u ∧
      (genCohnTree k (-k) w).2.1 0 0 = u ∧
      (genCohnTree k (-k) w).2.1 0 1 = (genMarkovTree k w).2.1 ∧
      (genCohnTree k (-k) w).2.1 1 1 = (3 + 3 * k) * ((genMarkovTree k w).2.1 : ℤ) - u - k

/-- Corollary 4.6: for `t ∈ (0, 1)` the characteristic number `u_t` solves
`m_r x ≡ m_s (mod m_t)` (with the plus sign).

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 4.6. -/
public theorem_wanted genMarkovCharNumber_dvd_sub (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) (u : ℕ)
    (hu : IsGenMarkovCharNumber (genMarkovTree k w).1 (genMarkovTree k w).2.1
      (genMarkovTree k w).2.2 u) :
    ((genMarkovTree k w).2.1 : ℤ) ∣ (genMarkovTree k w).1 * u - (genMarkovTree k w).2.2

/-- Lemma 4.7: for `t ∈ (0, 1)` the characteristic number `u_t` solves
`x² + k x + 1 ≡ 0 (mod m_t)`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.7. -/
public theorem_wanted genMarkovCharNumber_sq_add (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) (u : ℕ)
    (hu : IsGenMarkovCharNumber (genMarkovTree k w).1 (genMarkovTree k w).2.1
      (genMarkovTree k w).2.2 u) :
    (genMarkovTree k w).2.1 ∣ u ^ 2 + k * u + 1

/-- Lemma 4.8: for `t ∈ (0, 1)` the characteristic number satisfies `u_t + k < m_t / 2`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.8. -/
public theorem_wanted genMarkovCharNumber_add_lt (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) (u : ℕ)
    (hu : IsGenMarkovCharNumber (genMarkovTree k w).1 (genMarkovTree k w).2.1
      (genMarkovTree k w).2.2 u) :
    2 * (u + k) < (genMarkovTree k w).2.1

end

end MetaMathlibExt
