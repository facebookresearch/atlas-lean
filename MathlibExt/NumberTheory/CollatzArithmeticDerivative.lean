/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ArithmeticDerivative
public import MathlibExt.NumberTheory.Collatz
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# The arithmetic derivative, the accelerated Collatz map and compatible semiprimes

Every positive solution `n` of the arithmetic differential equation `D(C(n)) = C(D(n))` is odd,
where `D` is the arithmetic derivative and `C` the accelerated Collatz map. For compatible
semiprimes, the equations for the sums and products of the prime factors determine their
residues modulo three up to the order of each pair. The factors of the first semiprime have
opposite odd residues modulo four. A semiprime solution `pq` with `q < p` satisfies the prime gap
bound `p - q ≥ 2 √(30 p² + 2) - 10 p`; its proof uses `D(m)² ≥ 4m` for composite `m`.
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

/-- The arithmetic derivative of every natural number $b \ge 2$ is positive. -/
private theorem one_le_arithmeticDerivative_of_two_le {b : ℕ} (hb : 2 ≤ b) :
    1 ≤ arithmeticDerivative b := by
  obtain ⟨c, hc⟩ := Nat.minFac_dvd b
  have ha := Nat.minFac_prime (by omega : b ≠ 1)
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · omega
    · exact h
  rw [hc, arithmeticDerivative_mul, arithmeticDerivative_prime ha, one_mul]
  omega

/-- For a composite number $m$, the arithmetic derivative satisfies $4m \le D(m)^2$: writing
$m = ab$ with $a$ prime and $b \ge 2$ gives $D(m) = b + a D(b) \ge a + b$. -/
private theorem four_mul_le_arithmeticDerivative_sq {m : ℕ} (hm : 2 ≤ m) (hmp : ¬ m.Prime) :
    4 * m ≤ arithmeticDerivative m ^ 2 := by
  obtain ⟨b, hb⟩ := Nat.minFac_dvd m
  have ha := Nat.minFac_prime (by omega : m ≠ 1)
  generalize m.minFac = a at hb ha
  have hb2 : 2 ≤ b := by
    by_contra hlt
    interval_cases b
    · omega
    · rw [mul_one] at hb
      exact hmp (hb ▸ ha)
  have hDb := one_le_arithmeticDerivative_of_two_le hb2
  have hD : a + b ≤ arithmeticDerivative (a * b) := by
    rw [arithmeticDerivative_mul, arithmeticDerivative_prime ha, one_mul]
    nlinarith [ha.two_le]
  rw [← hb] at hD
  have hsq : (a + b) ^ 2 ≤ arithmeticDerivative m ^ 2 := Nat.pow_le_pow_left hD 2
  have hamgm : 4 * (a * b) ≤ (a + b) ^ 2 := by
    zify
    nlinarith [sq_nonneg ((a : ℤ) - b)]
  omega

/-- **Prime gap bound for semiprime solutions.** Let $D$ be the arithmetic derivative and let $C$
be the accelerated Collatz map, $C(n) = n/2$ for even $n$ and $C(n) = (3n + 1)/2$ for odd $n$.
If $p$ and $q$ are primes with $q < p$ and $D(C(pq)) = C(D(pq))$, then
$p - q \ge 2\sqrt{30p^2 + 2} - 10p$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 5 (`jis-2025-25.1.8-prop-5`). -/
theorem prime_gap_bound_of_arithmeticDerivative_collatz_comm (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (h : arithmeticDerivative (collatzAccelerated (p * q)) =
      collatzAccelerated (arithmeticDerivative (p * q))) :
    2 * Real.sqrt (30 * (p : ℝ) ^ 2 + 2) - 10 * p ≤ (p : ℝ) - q := by
  -- The solution `pq` is odd, so `p` and `q` are odd primes, `D(pq) = p + q` is even, and the
  -- equation reads `D(m) = (p + q) / 2` for `m = C(pq) = (3pq + 1) / 2`.
  have hodd := odd_of_arithmeticDerivative_collatz_comm _ (Nat.mul_pos hp.pos hq.pos) h
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp hodd).1
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp hodd).2
  have hpq : p * q % 2 = 1 := Nat.odd_iff.mp hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hpq9 : 9 ≤ p * q := Nat.mul_le_mul hp3 hq3
  rw [arithmeticDerivative_mul, arithmeticDerivative_prime hp, arithmeticDerivative_prime hq,
    one_mul, mul_one] at h
  have hC₁ : collatzAccelerated (p * q) = (3 * (p * q) + 1) / 2 := by
    simp [collatzAccelerated, hpq]
  have hC₂ : collatzAccelerated (q + p) = (q + p) / 2 := by
    have hev : (q + p) % 2 = 0 := by omega
    simp [collatzAccelerated, hev]
  rw [hC₁, hC₂] at h
  -- `m` is composite: if it were prime, `D(m) = 1` would force `p + q < 4`.
  have hm2 : 2 ≤ (3 * (p * q) + 1) / 2 := by omega
  have hmp : ¬ ((3 * (p * q) + 1) / 2).Prime := fun hmp => by
    rw [arithmeticDerivative_prime hmp] at h
    omega
  have key := four_mul_le_arithmeticDerivative_sq hm2 hmp
  rw [h] at key
  -- Clearing the halves gives `8 (3pq + 1) ≤ (p + q)²`, that is `x² + 20px - 20p² - 8 ≥ 0`
  -- for `x = p - q`.
  have hkey : 8 * (3 * (p * q) + 1) ≤ (q + p) ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, q + p = 2 * k := ⟨(q + p) / 2, by omega⟩
    have hm' : 2 * ((3 * (p * q) + 1) / 2) = 3 * (p * q) + 1 := by omega
    rw [hk, Nat.mul_div_cancel_left _ two_pos] at key
    rw [hk]
    nlinarith
  have hR : 8 * (3 * ((p : ℝ) * q) + 1) ≤ ((q : ℝ) + p) ^ 2 := by exact_mod_cast hkey
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hA : (0 : ℝ) ≤ 30 * (p : ℝ) ^ 2 + 2 := by positivity
  have hs := Real.sq_sqrt hA
  have hs0 := Real.sqrt_nonneg (30 * (p : ℝ) ^ 2 + 2)
  -- With `B = x + 10p ≥ 0`, the inequality says `B² ≥ 4 (30p² + 2)`, so `B ≥ 2 √(30p² + 2)`.
  have hB : 4 * (30 * (p : ℝ) ^ 2 + 2) ≤ ((p : ℝ) - q + 10 * p) ^ 2 := by nlinarith
  nlinarith

end

end MetaMathlibExt
