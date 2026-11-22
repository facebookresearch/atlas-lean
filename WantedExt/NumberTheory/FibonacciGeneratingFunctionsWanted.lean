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

/-- Lemma 9: the values `H_n / H_{n+1}` (`n ∈ ℤ`, `H_{n+1} ≠ 0`) of the
sequence with `H_0 = -b`, `H_1 = a` are exactly the values
`-G_{n+1} / G_n` (`n ∈ ℤ`, `G_n ≠ 0`) of the Gibonacci sequence with
`G_0 = a`, `G_1 = b`; both index sets run over the two-sided orbits.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 9 (`jis-2024-24.3.1-lem-9`). -/
public theorem_wanted gibonacci_shifted_ratios_eq_negated_ratios (a b : ℤ) :
    {x : ℚ | ∃ v ∈ fibonacciPairOrbit (-b, a), v.2 ≠ 0 ∧ x = (v.1 : ℚ) / v.2} =
      {x : ℚ | ∃ w ∈ fibonacciPairOrbit (a, b), w.1 ≠ 0 ∧ x = -(w.2 : ℚ) / w.1}

/-- Lemma 11: `M(a, b, p+q, p+2q) = -3M(a, b, q, p+q) - M(a, b, p, q)` and
`M(a,b,p,q)² + 3M(a,b,p,q)M(a,b,q,p+q) + M(a,b,q,p+q)² = a² + ab - b²`.
Stated for every `(p, q) ≠ (0, 0)`; the paper assumes `q ≠ 0`,
`p + q ≠ 0`, `p + 2q ≠ 0`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 11 (`jis-2024-24.3.1-lem-11`). -/
public theorem_wanted knappM_recurrence_and_quadratic (a b p q : ℤ) (hpq : (p, q) ≠ (0, 0)) :
    knappM a b (p + q) (p + 2 * q) = -3 * knappM a b q (p + q) - knappM a b p q ∧
      knappM a b p q ^ 2 + 3 * knappM a b p q * knappM a b q (p + q) +
          knappM a b q (p + q) ^ 2 = ((a ^ 2 + a * b - b ^ 2 : ℤ) : ℚ)

/-- Lemma 12: if `a² + ab - b² < 0` and `p / q` (lowest terms) is good for
`(a, b)`, some consecutive pair `(H_n, H_{n+1})` of its family has
`M(a, b, H_n, H_{n+1})² ≤ |a² + ab - b²|`. The pairs include one with
`H_{n+1} = 0` when the family is the Fibonacci one, as in the paper's
remark on the example `(a, b) = (1, 11)` (`M(1, 11, 1, 0) = -10`); without it the bound fails for
`(a, b) = (1, 11)`, `x = 0` (least `|M|` over pairs with `H_{n+1} ≠ 0`
is `11 > √109`).

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 12 (`jis-2024-24.3.1-lem-12`). -/
public theorem_wanted knappM_small_of_neg (a b p q : ℤ) (hD : a ^ 2 + a * b - b ^ 2 < 0)
    (hcop : Int.gcd p q = 1) (hq : q ≠ 0) (hgood : IsGibonacciGood a b ((p : ℚ) / q)) :
    ∃ v ∈ fibonacciPairOrbit (p, q),
      knappM a b v.1 v.2 ^ 2 ≤ |((a ^ 2 + a * b - b ^ 2 : ℤ) : ℚ)|

/-- Lemma 13: if `a² + ab - b² > 0` and `p / q` (lowest terms) is good for
`(a, b)`, some consecutive pair of its family has
`5 M(a, b, H_n, H_{n+1})² ≤ a² + ab - b²`, with pairs as in Lemma 12.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 13 (`jis-2024-24.3.1-lem-13`). -/
public theorem_wanted knappM_small_of_pos (a b p q : ℤ) (hD : 0 < a ^ 2 + a * b - b ^ 2)
    (hcop : Int.gcd p q = 1) (hq : q ≠ 0) (hgood : IsGibonacciGood a b ((p : ℚ) / q)) :
    ∃ v ∈ fibonacciPairOrbit (p, q),
      5 * knappM a b v.1 v.2 ^ 2 ≤ ((a ^ 2 + a * b - b ^ 2 : ℤ) : ℚ)

/-- Theorem 4: for `(a, b) ≠ (0, 0)`, (i) every integer solution `(M, k)`,
`k ≠ 0`, of `M² = 5k² + (2b - 6a)k + (a - b)²` gives a good value
`x = (a - b - k + M) / 2k` (whose family is good by Theorem 1); (ii) every
family of good values other than the Fibonacci family (the one containing
`0`) and the family containing a zero of `G^{(a,b)}` has a member
`x = (a - b - k + M) / 2k` with `k ≠ 0`, `M² = 5k² + (2b - 6a)k + (a - b)²`,
`|M| ≤ C` (written `M² ≤ |a² + ab - b²|` if `a² + ab - b² < 0` and
`5M² ≤ a² + ab - b²` if it is positive) and an integer `N` with
`M² + 3MN + N² = a² + ab - b²`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Theorem 4 (`jis-2024-24.3.1-thm-4`). -/
public theorem_wanted gibonacci_good_families_classification (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    (∀ M k : ℤ, k ≠ 0 → M ^ 2 = 5 * k ^ 2 + (2 * b - 6 * a) * k + (a - b) ^ 2 →
        IsGibonacciGood a b (((a - b - k + M : ℤ) : ℚ) / (2 * k))) ∧
      ∀ p q : ℤ, Int.gcd p q = 1 → q ≠ 0 → IsGibonacciGood a b ((p : ℚ) / q) →
        (∀ v ∈ fibonacciPairOrbit (p, q), v.2 ≠ 0 →
          (v.1 : ℚ) / v.2 ≠ 0 ∧ gibonacciGeneratingValue a b ((v.1 : ℚ) / v.2) ≠ 0) →
        ∃ v ∈ fibonacciPairOrbit (p, q), v.2 ≠ 0 ∧ ∃ M k N : ℤ, k ≠ 0 ∧
          (a ^ 2 + a * b - b ^ 2 < 0 → M ^ 2 ≤ -(a ^ 2 + a * b - b ^ 2)) ∧
          (0 < a ^ 2 + a * b - b ^ 2 → 5 * M ^ 2 ≤ a ^ 2 + a * b - b ^ 2) ∧
          M ^ 2 + 3 * M * N + N ^ 2 = a ^ 2 + a * b - b ^ 2 ∧
          M ^ 2 = 5 * k ^ 2 + (2 * b - 6 * a) * k + (a - b) ^ 2 ∧
          (v.1 : ℚ) / v.2 = ((a - b - k + M : ℤ) : ℚ) / (2 * k)

end

end MetaMathlibExt
