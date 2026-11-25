/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Logic.Function.Iterate
public import MathlibExt.NumberTheory.GibonacciNumber
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.Ring

/-!
# Integer values of Gibonacci generating functions

At the ratio of consecutive Fibonacci numbers, Cassini's identity reduces the denominator
of the generating function to a sign divided by the square of a Fibonacci number.
At $-G_{n+1}/G_n$, the generating function also takes an integer value whenever $G_n \ne 0$.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Gibonacci generating function.** For integers $a$ and $b$ and a rational number $x$, the
value of the Gibonacci generating function at $x$ is the rational number

$$G^{(a,b)}(x) = \frac{(b - a)x + a}{1 - x - x^2}.$$

It is the generating function of the Gibonacci sequence $(G_n)_{n \ge 0}$ with $G_0 = a$,
$G_1 = b$ and $G_{n+2} = G_{n+1} + G_n$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public def gibonacciGeneratingValue (a b : ℤ) (x : ℚ) : ℚ :=
  (((b : ℚ) - (a : ℚ)) * x + (a : ℚ)) / (1 - x - x ^ 2)

/-- **Value of the Gibonacci generating function at zero.** For all integers $a$ and $b$, the
Gibonacci generating function $G^{(a,b)}(x) = \frac{(b - a)x + a}{1 - x - x^2}$ takes the value
$G^{(a,b)}(0) = a$ at $x = 0$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem gibonacciGeneratingValue_zero (a b : ℤ) :
    gibonacciGeneratingValue a b 0 = (a : ℚ) := by
  simp [gibonacciGeneratingValue]

/-- **Value of the Gibonacci generating function at one.** For all integers $a$ and $b$, the
Gibonacci generating function $G^{(a,b)}(x) = \frac{(b - a)x + a}{1 - x - x^2}$ takes the value
$G^{(a,b)}(1) = -b$ at $x = 1$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem gibonacciGeneratingValue_one (a b : ℤ) :
    gibonacciGeneratingValue a b 1 = -(b : ℚ) := by
  rw [gibonacciGeneratingValue]
  norm_num
  ring

/-- **Good rationals for a Gibonacci generating function.** Let $a$ and $b$ be integers and let
$G^{(a,b)}(x) = \frac{(b - a)x + a}{1 - x - x^2}$ be the generating function of the Gibonacci
sequence with initial terms $a$ and $b$. A rational number $x$ is good for $(a, b)$ when
$1 - x - x^2 \ne 0$ and $G^{(a,b)}(x)$ is an integer.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1 (the paper says `x = p / q` is good
for `(a, b)` when `G^{(a,b)}(x)` is an integer; Theorem 1 uses the same
integrality without the word good). -/
public def IsGibonacciGood (a b : ℤ) (x : ℚ) : Prop :=
  1 - x - x ^ 2 ≠ 0 ∧ ∃ z : ℤ, gibonacciGeneratingValue a b x = (z : ℚ)

/-- **Zero is good for every pair.** For all integers $a$ and $b$, the rational number $0$ is good
for $(a, b)$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem isGibonacciGood_zero (a b : ℤ) : IsGibonacciGood a b 0 :=
  ⟨by norm_num, a, gibonacciGeneratingValue_zero a b⟩

/-- **One is good for every pair.** For all integers $a$ and $b$, the rational number $1$ is good
for $(a, b)$.

The value of the Gibonacci generating function there is $G^{(a,b)}(1) = -b$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem isGibonacciGood_one (a b : ℤ) : IsGibonacciGood a b 1 :=
  ⟨by norm_num, -b, by rw [gibonacciGeneratingValue_one]; simp⟩

-- Multiplying numerator and denominator by q² gives a quotient of integers.
private theorem isGibonacciGood_div_iff_dvd (a b p q : ℤ) (hq : q ≠ 0) :
    IsGibonacciGood a b ((p : ℚ) / q) ↔
      q ^ 2 - p * q - p ^ 2 ≠ 0 ∧ q ^ 2 - p * q - p ^ 2 ∣ q * ((b - a) * p + a * q) := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  let d := q ^ 2 - p * q - p ^ 2
  have hden : 1 - (p : ℚ) / q - ((p : ℚ) / q) ^ 2 = (d : ℚ) / (q : ℚ) ^ 2 := by
    dsimp [d]
    push_cast
    field_simp
  have hval : gibonacciGeneratingValue a b ((p : ℚ) / q) =
      ((q * ((b - a) * p + a * q) : ℤ) : ℚ) / (d : ℚ) := by
    rw [gibonacciGeneratingValue, hden, div_div_eq_mul_div]
    congr 1
    push_cast
    field_simp
  rw [IsGibonacciGood, hden, div_ne_zero_iff, and_iff_left (pow_ne_zero 2 hq'),
    Int.cast_ne_zero, hval]
  refine and_congr_right fun hd => exists_congr fun z => ?_
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [div_eq_iff hd', mul_comm (z : ℚ), ← Int.cast_mul, Int.cast_inj]

/-- **Goodness passes to two transformed fractions.** Let $a$, $b$, $p$, $q$ be integers with
$q \ne 0$ and $\gcd(p, q) = 1$, and suppose that $p/q$ is good for $(a, b)$. If $p + q \ne 0$,
then $q/(p + q)$ is good for $(a, b)$; and if $p \ne 0$, then $(q - p)/p$ is good for $(a, b)$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Theorem 1
(`jis-2024-24.3.1-thm-1`). -/
public theorem isGibonacciGood_transform (a b p q : ℤ)
    (hcop : Int.gcd p q = 1) (hq : q ≠ 0)
    (h : IsGibonacciGood a b ((p : ℚ) / (q : ℚ))) :
    (p + q ≠ 0 → IsGibonacciGood a b ((q : ℚ) / ((p : ℚ) + (q : ℚ)))) ∧
    (p ≠ 0 → IsGibonacciGood a b (((q : ℚ) - (p : ℚ)) / (p : ℚ))) := by
  let d := q ^ 2 - p * q - p ^ 2
  let u := (b - a) * p + a * q
  obtain ⟨hd, hqu⟩ := (isGibonacciGood_div_iff_dvd a b p q hq).mp h
  have hcop' : IsCoprime d q := by
    rw [show d = (q - p) * q - p ^ 2 by dsimp [d]; ring, IsCoprime.mul_sub_right_left_iff]
    exact (Int.isCoprime_iff_gcd_eq_one.mpr hcop).pow_left
  have hu : d ∣ u := hcop'.dvd_of_dvd_mul_left hqu
  -- Modulo d, multiplying the forward linear numerator by q gives (p + q) * u.
  have hv : d ∣ a * p + b * q := by
    apply hcop'.dvd_of_dvd_mul_left
    rw [show q * (a * p + b * q) = (p + q) * u + (b - a) * d by dsimp [u, d]; ring]
    exact dvd_add (dvd_mul_of_dvd_right hu _) (dvd_mul_left ..)
  have step (r s : ℤ) (hs : s ≠ 0) (hform : s ^ 2 - r * s - r ^ 2 = -d)
      (hnum : d ∣ (b - a) * r + a * s) : IsGibonacciGood a b ((r : ℚ) / s) := by
    apply (isGibonacciGood_div_iff_dvd a b r s hs).mpr
    rw [hform]
    exact ⟨neg_ne_zero.mpr hd, neg_dvd.mpr (dvd_mul_of_dvd_right hnum _)⟩
  constructor
  · intro hs
    rw [← Int.cast_add]
    apply step q (p + q) hs (by dsimp [d]; ring)
    rwa [show (b - a) * q + a * (p + q) = a * p + b * q by ring]
  · intro hp
    rw [← Int.cast_sub]
    apply step (q - p) p hp (by dsimp [d]; ring)
    rw [show (b - a) * (q - p) + a * p = (a * p + b * q) - u by dsimp [u]; ring]
    exact dvd_sub hv hu

/-- **Consecutive Fibonacci ratios are good.** For all integers $a$ and $b$ and every natural
number $n$, the ratio $F_n / F_{n+1}$ of consecutive Fibonacci numbers is good for $(a, b)$.

The source allows every integer $n \ne -1$, using the Fibonacci numbers at negative indices.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 7
(`jis-2024-24.3.1-lem-7`). -/
public theorem isGibonacciGood_fib_div (a b : ℤ) (n : ℕ) :
    IsGibonacciGood a b ((Nat.fib n : ℚ) / (Nat.fib (n + 1) : ℚ)) := by
  let p := Nat.fib n
  let q := Nat.fib (n + 1)
  have hq : (q : ℚ) ≠ 0 := by simp [q]
  have cassini : (q : ℤ) ^ 2 - p * ((p : ℤ) + q) = (-1) ^ n := by
    have h := Int.fib_add_sq_sub_fib_mul_fib_add_two_mul (n : ℤ) 1
    change (q : ℤ) ^ 2 - p * (Nat.fib (n + 2) : ℤ) = (-1) ^ n * 1 ^ 2 at h
    simpa only [Nat.fib_add_two, Nat.cast_add, one_pow, mul_one] using h
  have norm_eq : (q : ℚ) ^ 2 - p * ((p : ℚ) + q) = (-1) ^ n := by
    exact_mod_cast cassini
  have hden : 1 - (p : ℚ) / q - ((p : ℚ) / q) ^ 2 = (-1 : ℚ) ^ n / q ^ 2 := by
    field_simp [hq]
    linear_combination norm_eq
  change IsGibonacciGood a b ((p : ℚ) / q)
  refine ⟨?_, ((b - a) * p + a * q) * q * (-1) ^ n, ?_⟩
  · simp [hden, hq]
  · rw [gibonacciGeneratingValue, hden, div_div_eq_mul_div, div_eq_mul_inv, ← inv_pow, inv_neg_one]
    push_cast
    field_simp [hq]

/-- **Two standard families of good values.** Let $a$ and $b$ be integers and let $(G_n)_{n \ge 0}$
be the Gibonacci sequence with $G_0 = a$ and $G_1 = b$. For every natural number $n$, the ratio
$F_n / F_{n+1}$ of consecutive Fibonacci numbers is good for $(a, b)$, and if $G_n \ne 0$, then
$-G_{n+1} / G_n$ is good for $(a, b)$.

The source indexes both families by all integers ($n \ne -1$ for the first).

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Corollary 2
(`jis-2024-24.3.1-cor-2`). -/
public theorem isGibonacciGood_standard_values (a b : ℤ) :
    (∀ n : ℕ, IsGibonacciGood a b ((Nat.fib n : ℚ) / (Nat.fib (n + 1) : ℚ))) ∧
    (∀ n : ℕ, gibonacciNumber a b n ≠ 0 →
      IsGibonacciGood a b
        (-(gibonacciNumber a b (n + 1) : ℚ) / (gibonacciNumber a b n : ℚ))) := by
  refine ⟨isGibonacciGood_fib_div a b, ?_⟩
  let G := gibonacciNumber a b
  have hrec (n : ℕ) : G (n + 2) = G (n + 1) + G n := rfl
  -- Express the seeds in the current pair by reversing each recurrence step.
  have seeds (n : ℕ) : ∃ u v : ℤ, a = u * G n + v * G (n + 1) ∧
      b = v * G n + (u + v) * G (n + 1) := by
    induction n with
    | zero => exact ⟨1, 0, by simp [G, gibonacciNumber], by simp [G, gibonacciNumber]⟩
    | succ n ih =>
      obtain ⟨u, v, ha, hb⟩ := ih
      refine ⟨v - u, u, ?_, ?_⟩
      · rw [ha, hrec n]
        ring
      · rw [hb, hrec n]
        ring
  have den (x : ℚ) : 1 - x - x ^ 2 ≠ 0 := by
    intro h
    exact (by norm_num : ¬ IsSquare (5 : ℚ)) ⟨2 * x + 1, by linear_combination 4 * h⟩
  intro n hn
  obtain ⟨u, v, ha, hb⟩ := seeds n
  have hn' : (G n : ℚ) ≠ 0 := by exact_mod_cast hn
  change IsGibonacciGood a b (-(G (n + 1) : ℚ) / G n)
  refine ⟨den _, u * G n, ?_⟩
  rw [gibonacciGeneratingValue, div_eq_iff (den _), ha, hb]
  push_cast
  field_simp [hn']
  ring

/-- One step along a two-sided sequence with the Fibonacci recurrence:
`(H_n, H_{n+1}) ↦ (H_{n+1}, H_n + H_{n+1})`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Section 2 (sequences `H_n` with
`H_n = H_{n-1} + H_{n-2}` for all `n ∈ ℤ`). -/
public def fibonacciPairStep (v : ℤ × ℤ) : ℤ × ℤ :=
  (v.2, v.1 + v.2)

/-- One step backwards: `(H_n, H_{n+1}) ↦ (H_{n+1} - H_n, H_n)`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Section 2. -/
public def fibonacciPairStepBack (v : ℤ × ℤ) : ℤ × ℤ :=
  (v.2 - v.1, v.1)

/-- The backward step undoes the forward step.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Section 2. -/
public theorem fibonacciPairStepBack_step (v : ℤ × ℤ) :
    fibonacciPairStepBack (fibonacciPairStep v) = v := by
  simp [fibonacciPairStep, fibonacciPairStepBack]

/-- The forward step undoes the backward step.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Section 2. -/
public theorem fibonacciPairStep_stepBack (v : ℤ × ℤ) :
    fibonacciPairStep (fibonacciPairStepBack v) = v := by
  simp [fibonacciPairStep, fibonacciPairStepBack]

/-- The consecutive pairs `(H_n, H_{n+1})`, `n ∈ ℤ`, of the two-sided
sequence with the Fibonacci recurrence and `(H_0, H_1) = v`. For a good
`x = p / q` in lowest terms, the family of good values containing `x`
is `{H_n / H_{n+1} : H_{n+1} ≠ 0}` for the orbit of `(p, q)`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Section 2 (families of good
values). -/
public def fibonacciPairOrbit (v : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {w | ∃ n : ℕ, w = fibonacciPairStep^[n] v ∨ w = fibonacciPairStepBack^[n] v}

/-- Characteristic members: the orbit of `(0, 1)` (the Fibonacci
numbers) contains `(0, 1)`, `(1, 1)` and `(1, 0)`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Section 2. -/
public theorem fibonacciPairOrbit_zero_one :
    (0, 1) ∈ fibonacciPairOrbit (0, 1) ∧ (1, 1) ∈ fibonacciPairOrbit (0, 1) ∧
      (1, 0) ∈ fibonacciPairOrbit (0, 1) :=
  ⟨⟨0, Or.inl rfl⟩, ⟨1, Or.inl rfl⟩, ⟨1, Or.inr rfl⟩⟩

/-- The quantity `M(a, b, p, q) = (2p + q)((b - a)p + aq) / (q² - pq - p²) - a + b`,
the signed square root in `p / q = (a - b - k + M) / (2k)` with
`k = G^{(a,b)}(p / q)`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Section 3 (the displayed formula for
`M(a,b,p,q)`). -/
public def knappM (a b p q : ℤ) : ℚ :=
  (2 * (p : ℚ) + q) * (((b : ℚ) - a) * p + (a : ℚ) * q) / ((q : ℚ) ^ 2 - p * q - (p : ℚ) ^ 2)
    - a + b

/-- Characteristic value: `M(a, b, 1, 0) = a - b` (the paper's
`M(1, 11, 1, 0) = -10`).

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Section 3 (remark after the example
`(a, b) = (1, 11)`). -/
public theorem knappM_one_zero (a b : ℤ) : knappM a b 1 0 = (a : ℚ) - b := by
  simp only [knappM]
  push_cast
  ring

end

end MetaMathlibExt
