/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.GibonacciNumber

namespace MetaMathlibExt

@[expose] public section

/-- The value at `x` of the Fibonacci-like generating function
`G^{(a,b)}(x) = ((b - a) x + a) / (1 - x - x ^ 2)` attached to the
Gibonacci sequence with `G^{(a,b)}_0 = a` and `G^{(a,b)}_1 = b`
(`gibonacciNumber a b`).

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public def gibonacciGeneratingValue (a b : ℤ) (x : ℚ) : ℚ :=
  (((b : ℚ) - (a : ℚ)) * x + (a : ℚ)) / (1 - x - x ^ 2)

/-- Characteristic value at `x = 0`: `G^{(a,b)}(0) = a`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem gibonacciGeneratingValue_zero (a b : ℤ) :
    gibonacciGeneratingValue a b 0 = (a : ℚ) := by
  simp [gibonacciGeneratingValue]

/-- Characteristic value at `x = 1`: `G^{(a,b)}(1) = -b`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem gibonacciGeneratingValue_one (a b : ℤ) :
    gibonacciGeneratingValue a b 1 = -(b : ℚ) := by
  rw [gibonacciGeneratingValue]
  norm_num
  ring

/-- The rational `x` is good for `(a, b)`: the generating function is
defined at `x` (its denominator does not vanish) and takes an integer
value there.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1 (the paper says `x = p / q` is good
for `(a, b)` when `G^{(a,b)}(x)` is an integer; Theorem 1 uses the same
integrality without the word good). -/
public def IsGibonacciGood (a b : ℤ) (x : ℚ) : Prop :=
  1 - x - x ^ 2 ≠ 0 ∧ ∃ z : ℤ, gibonacciGeneratingValue a b x = (z : ℚ)

/-- Characteristic example: `0` is good for every `(a, b)`, with value
`a`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem isGibonacciGood_zero (a b : ℤ) : IsGibonacciGood a b 0 :=
  ⟨by norm_num, a, gibonacciGeneratingValue_zero a b⟩

/-- Characteristic example: `1` is good for every `(a, b)`, with value
`-b`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem isGibonacciGood_one (a b : ℤ) : IsGibonacciGood a b 1 :=
  ⟨by norm_num, -b, by rw [gibonacciGeneratingValue_one]; simp⟩

/-- The generating series identity: multiplying the Gibonacci power
series by `1 - X - X ^ 2` leaves the linear polynomial `a + (b - a) X`.
This is the product form of the paper's displayed quotient
`G(x) = ((b - a) x + a) / (1 - x - x ^ 2)`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem_wanted gibonacci_powerSeries_mul (a b : ℤ) :
    (1 - PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries ℚ)
        * PowerSeries.mk (fun n => ((gibonacciNumber a b n : ℤ) : ℚ))
      = PowerSeries.C (a : ℚ)
        + PowerSeries.C ((b : ℚ) - (a : ℚ)) * PowerSeries.X

/-- Integrality propagates along the two fractional transforms: if
`p / q` (in lowest terms) is good for `(a, b)`, then so are
`q / (p + q)` (when `p + q ≠ 0`) and `(q - p) / p` (when `p ≠ 0`).

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Theorem 1
(`jis-2024-24.3.1-thm-1`). -/
public theorem_wanted isGibonacciGood_transform (a b p q : ℤ)
    (hcop : Int.gcd p q = 1) (hq : q ≠ 0)
    (h : IsGibonacciGood a b ((p : ℚ) / (q : ℚ))) :
    (p + q ≠ 0 → IsGibonacciGood a b ((q : ℚ) / ((p : ℚ) + (q : ℚ)))) ∧
    (p ≠ 0 → IsGibonacciGood a b (((q : ℚ) - (p : ℚ)) / (p : ℚ)))

/-- The congruence criterion for goodness: for `(a, b) ≠ (0, 0)` and
coprime `p, q`, the fraction `p / q` is good for `(a, b)` if and only
if `a ≡ -b p (q - p)⁻¹ ≡ -b q p⁻¹ (mod |q ^ 2 - p q - p ^ 2|)`. The
paper's modular inverses are written here with explicit inverse
witnesses `u` and `v`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 6
(`jis-2024-24.3.1-lem-6`). -/
public theorem_wanted isGibonacciGood_iff (a b p q : ℤ)
    (hab : (a, b) ≠ (0, 0)) (hcop : Int.gcd p q = 1) (hq : q ≠ 0) :
    IsGibonacciGood a b ((p : ℚ) / (q : ℚ)) ↔
    ∃ u v : ℤ, (q - p) * u ≡ 1 [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
      p * v ≡ 1 [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
      a ≡ -b * p * u [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
      a ≡ -b * q * v [ZMOD |q ^ 2 - p * q - p ^ 2|]

/-- Consecutive Fibonacci ratios are good: `F_n / F_{n+1}` is good for
every `(a, b)`. The paper allows every integer `n ≠ -1` with the
two-sided Fibonacci extension; this statement covers `n ∈ ℕ`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 7
(`jis-2024-24.3.1-lem-7`). -/
public theorem_wanted isGibonacciGood_fib_div (a b : ℤ) (n : ℕ) :
    IsGibonacciGood a b ((Nat.fib n : ℚ) / (Nat.fib (n + 1) : ℚ))

/-- The two standard families of good values: the Fibonacci ratios
`F_n / F_{n+1}`, and the negated Gibonacci ratios
`-G^{(a,b)}_{n+1} / G^{(a,b)}_n` whenever the denominator is nonzero.
The paper indexes both families by all integers (`n ≠ -1` for the
first); this statement covers `n ∈ ℕ`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Corollary 2
(`jis-2024-24.3.1-cor-2`). -/
public theorem_wanted isGibonacciGood_standard_values (a b : ℤ) :
    (∀ n : ℕ, IsGibonacciGood a b ((Nat.fib n : ℚ) / (Nat.fib (n + 1) : ℚ))) ∧
    (∀ n : ℕ, gibonacciNumber a b n ≠ 0 →
      IsGibonacciGood a b
        (-(gibonacciNumber a b (n + 1) : ℚ) / (gibonacciNumber a b n : ℚ)))

/-- Ratios of the Gibonacci sequence `H` with `H_0 = -b` and `H_1 = a`
are good for `(a, b)` whenever the denominator is nonzero. The paper
indexes `H` by all integers; this statement covers `n ∈ ℕ`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 8
(`jis-2024-24.3.1-lem-8`). -/
public theorem_wanted isGibonacciGood_shifted_ratio (a b : ℤ) (n : ℕ)
    (h : gibonacciNumber (-b) a (n + 1) ≠ 0) :
    IsGibonacciGood a b
      ((gibonacciNumber (-b) a n : ℚ) / (gibonacciNumber (-b) a (n + 1) : ℚ))

/-- For coprime `p, q`, let `H` be the Gibonacci sequence with
`H_0 = p` and `H_1 = q`. Then infinitely many pairs `(a, b)` make
every ratio `H_n / H_{n+1}` (with nonzero denominator) good, and this
holds for a given `(a, b)` if and only if
`a ≡ -b p (q - p)⁻¹ ≡ -b q p⁻¹ (mod |q ^ 2 - p q - p ^ 2|)`, with the
modular inverses written via explicit witnesses. The paper indexes
`H` by all integers; this statement covers `n ∈ ℕ`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Theorem 3
(`jis-2024-24.3.1-thm-3`). -/
public theorem_wanted isGibonacciGood_ratios_infinite_iff (p q : ℤ)
    (hcop : Int.gcd p q = 1) :
    (Set.Infinite {ab : ℤ × ℤ | ∀ n : ℕ, gibonacciNumber p q (n + 1) ≠ 0 →
        IsGibonacciGood ab.1 ab.2
          ((gibonacciNumber p q n : ℚ) / (gibonacciNumber p q (n + 1) : ℚ))}) ∧
    ∀ a b : ℤ, (∀ n : ℕ, gibonacciNumber p q (n + 1) ≠ 0 →
        IsGibonacciGood a b
          ((gibonacciNumber p q n : ℚ) / (gibonacciNumber p q (n + 1) : ℚ))) ↔
      ∃ u v : ℤ, (q - p) * u ≡ 1 [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
        p * v ≡ 1 [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
        a ≡ -b * p * u [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
        a ≡ -b * q * v [ZMOD |q ^ 2 - p * q - p ^ 2|]

end

end MetaMathlibExt
