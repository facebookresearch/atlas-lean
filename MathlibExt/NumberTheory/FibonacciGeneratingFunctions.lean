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
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer values of Gibonacci generating functions

At the ratio of consecutive Fibonacci numbers, Cassini's identity reduces the denominator
of the generating function to a sign divided by the square of a Fibonacci number.
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
