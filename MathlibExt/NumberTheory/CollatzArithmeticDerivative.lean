/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.ArithmeticDerivative
public import MathlibExt.NumberTheory.Collatz
import Mathlib.Tactic.NormNum.Prime

/-!
# The arithmetic derivative, the accelerated Collatz map and compatible semiprimes

Every positive solution `n` of the arithmetic differential equation `D(C(n)) = C(D(n))` is odd,
where `D` is the arithmetic derivative and `C` the accelerated Collatz map. For compatible
semiprimes, the equations for the sums and products of the prime factors determine their
residues modulo three up to the order of each pair. The factors of the first semiprime have
opposite odd residues modulo four.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The accelerated Collatz map.** The accelerated Collatz map $C : \mathbb{N} \to \mathbb{N}$
sends a natural number $n$ to $n/2$ if $n$ is even and to $(3n + 1)/2$ if $n$ is odd.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2. -/
def collatzAccelerated (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- **The accelerated Collatz map on odd numbers.** Let $C$ be the accelerated Collatz map and
$T$ the Collatz map. For every odd natural number $n$, $C(n) = T(T(n))$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2. -/
theorem collatzAccelerated_of_odd {n : ℕ} (hn : n % 2 = 1) :
    collatzAccelerated n = Nat.collatzStep (Nat.collatzStep n) := by
  have h : (3 * n + 1) % 2 = 0 := by omega
  simp [collatzAccelerated, Nat.collatzStep, hn, h]

/-- **The accelerated Collatz map on even numbers.** Let $C$ be the accelerated Collatz map and
$T$ the Collatz map. For every even natural number $n$, $C(n) = T(n)$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2. -/
theorem collatzAccelerated_of_even {n : ℕ} (hn : n % 2 = 0) :
    collatzAccelerated n = Nat.collatzStep n := by
  simp [collatzAccelerated, Nat.collatzStep, hn]

/-- **Positive solutions of the Collatz arithmetic differential equation are odd.** Let $D$ be
the arithmetic derivative and $C$ the accelerated Collatz map. Every positive integer $n$ with
$D(C(n)) = C(D(n))$ is odd.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 2 (`jis-2025-25.1.8-prop-2`). -/
theorem odd_of_arithmeticDerivative_collatz_comm (n : ℕ) (hn : 0 < n)
    (h : arithmeticDerivative (collatzAccelerated n) =
      collatzAccelerated (arithmeticDerivative n)) :
    Odd n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- For `n = 2m`, `C(n) = m` and the Leibniz rule gives `D(n) = m + 2 D(m)`, so the equation
    -- reads `D(m) = C(m + 2 D(m))`. If `m` is even, this says `D(m) = m / 2 + D(m)`, so `m = 0`;
    -- if `m` is odd, the right side `(3m + 6 D(m) + 1) / 2` exceeds `D(m)`.
    exfalso
    have hC : collatzAccelerated (2 * m) = m := by
      unfold collatzAccelerated
      split_ifs <;> omega
    rw [hC, arithmeticDerivative_mul, arithmeticDerivative_prime Nat.prime_two, one_mul] at h
    unfold collatzAccelerated at h
    split_ifs at h <;> omega
  · exact odd_two_mul_add_one m

/-- **Compatible semiprimes.** Natural numbers $p, q, r, s$ form a compatible semiprime pair,
and the semiprimes $pq$ and $rs$ are called compatible, when $p, q, r, s$ are primes with
$2(r + s) = p + q$ and $2rs = 3pq + 1$; equivalently, $r$ and $s$ are the roots of
$2x^2 - (p + q)x + 3pq + 1 = 0$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 3,
definition after Proposition 7. -/
def IsCompatibleSemiprimePair (p q r s : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ 2 * (r + s) = p + q ∧ 2 * (r * s) = 3 * (p * q) + 1

/-- **An example of compatible semiprimes.** The semiprimes $71 \cdot 1609 = 114239$ and
$349 \cdot 491$ are compatible.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Table 1. -/
theorem isCompatibleSemiprimePair_71_1609 : IsCompatibleSemiprimePair 71 1609 349 491 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Compatible semiprimes modulo 3.** Let $p, q, r, s$ be primes with $2(r + s) = p + q$ and
$2rs = 3pq + 1$, so that the semiprimes $pq$ and $rs$ are compatible. Then
$pq \equiv rs \equiv 2 \pmod 3$; moreover one of $p, q$ is congruent to $1$ and the other to $2$
modulo $3$, and likewise one of $r, s$ is congruent to $1$ and the other to $2$ modulo $3$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 8 (`jis-2025-25.1.8-prop-8`). -/
theorem IsCompatibleSemiprimePair.mod_three {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    p * q % 3 = 2 ∧ r * s % 3 = 2 ∧
      ((p % 3 = 1 ∧ q % 3 = 2) ∨ (p % 3 = 2 ∧ q % 3 = 1)) ∧
      ((r % 3 = 1 ∧ s % 3 = 2) ∨ (r % 3 = 2 ∧ s % 3 = 1)) := by
  obtain ⟨hp, hq, hr, hs, hsum, hprod⟩ := h
  have hrs : r * s % 3 = 2 := by omega
  have hrs' : (r % 3 = 1 ∧ s % 3 = 2) ∨ (r % 3 = 2 ∧ s % 3 = 1) := by
    have residues (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rw [Nat.mul_mod] at hrs
    rcases residues r with h₁ | h₁ | h₁ <;> rcases residues s with h₂ | h₂ | h₂ <;>
      simp [h₁, h₂] at hrs ⊢
  have hsum₃ : (p + q) % 3 = 0 := by rcases hrs' with h | h <;> omega
  -- If both residues vanish, primality forces p = q = 3, whereas r + s ≥ 4.
  have hp₃ : p % 3 ≠ 0 := by
    intro hzero
    have hp_eq : p = 3 := (hp.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero hzero)
    have hq_eq : q = 3 := (hq.dvd_iff_eq (by decide)).mp (by omega)
    have := hr.two_le
    have := hs.two_le
    omega
  have hpq : (p % 3 = 1 ∧ q % 3 = 2) ∨ (p % 3 = 2 ∧ q % 3 = 1) := by omega
  refine ⟨?_, hrs, hpq, hrs'⟩
  rw [Nat.mul_mod]
  rcases hpq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]

/-- **Compatible semiprimes modulo 4.** Let $p, q, r, s$ be primes with $2(r + s) = p + q$ and
$2rs = 3pq + 1$, so that the semiprime $pq$ is compatible with the semiprime $rs$. Then
$pq \equiv 3 \pmod 4$, and one of $p, q$ is congruent to $1$ and the other to $3$ modulo $4$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 10 (`jis-2025-25.1.8-prop-10`). -/
theorem IsCompatibleSemiprimePair.mod_four {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    p * q % 4 = 3 ∧ ((p % 4 = 1 ∧ q % 4 = 3) ∨ (p % 4 = 3 ∧ q % 4 = 1)) := by
  obtain ⟨hp, hq, hr, hs, hsum, hprod⟩ := h
  -- If either r or s were two, the compatibility equations would give p * q < p + q.
  have hpq : p + q ≤ p * q := Nat.add_le_mul hp.two_le hq.two_le
  obtain rfl | hr_odd := hr.eq_two_or_odd
  · omega
  obtain rfl | hs_odd := hs.eq_two_or_odd
  · omega
  have hrs : r * s % 2 = 1 := by rw [Nat.mul_mod, hr_odd, hs_odd]
  have hmod : p * q % 4 = 3 := by omega
  refine ⟨hmod, ?_⟩
  obtain rfl | hp_odd := hp.eq_two_or_odd
  · omega
  -- Since r and s are odd, the sum equation makes p + q a multiple of four.
  omega

end

end MetaMathlibExt
