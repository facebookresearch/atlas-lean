/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Set.Finite.Basic
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
For every integer seed $(a,b)$, the set of these ratios over the two-sided sequence $G$ with
initial terms $(a,b)$ equals the set of ratios $H_n/H_{n+1}$ with $n \in \mathbb{Z}$ and
$H_{n+1} \ne 0$ for the two-sided sequence $H$ with initial terms $(-b,a)$. Both sequences
satisfy the Fibonacci recurrence at every integer index. Unlike the paper's standing
assumption for Lemma 9, this equality also includes $(a,b)=(0,0)$, when both sets are empty.
For a fixed coprime seed, congruences characterize the pairs for which all defined consecutive
ratios are good.

## References

- Michael P. Knapp, [*Fibonacci Generating Functions*](https://cs.uwaterloo.ca/journals/JIS/VOL27/Knapp/knapp5.pdf),
  Journal of Integer Sequences 27 (2024), Article 24.3.1, pp. 1–12, Theorem 3 (which uses
  Lemma 6 and Theorem 1). See also Corollary 2, Lemmas 5–9, and Sections 2–3.
  The ratio-set equality follows the index reversal in Lemma 9, equation (4).
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

-- Keep the source's nonzero-seed hypothesis, although the calculation does not use it.
set_option linter.unusedVariables false in
/-- **Congruence criterion for good fractions.** Let $a, b, p, q$ be integers with
$(a, b) \ne (0, 0)$, $q \ne 0$ and $\gcd(p, q) = 1$, and put $m = |q^2 - pq - p^2|$. Then
$p / q$ is good for $(a, b)$ if and only if there are integers $u$ and $v$ with
$(q - p) u \equiv 1$, $p v \equiv 1$, $a \equiv -b p u$ and $a \equiv -b q v \pmod{m}$.

In the source's notation, with modular inverses, the condition reads
$a \equiv -bp(q - p)^{-1} \equiv -bqp^{-1} \pmod{m}$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 6
(`jis-2024-24.3.1-lem-6`). -/
public theorem isGibonacciGood_iff (a b p q : ℤ)
    (hab : (a, b) ≠ (0, 0)) (hcop : Int.gcd p q = 1) (hq : q ≠ 0) :
    IsGibonacciGood a b ((p : ℚ) / (q : ℚ)) ↔
    ∃ u v : ℤ, (q - p) * u ≡ 1 [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
      p * v ≡ 1 [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
      a ≡ -b * p * u [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
      a ≡ -b * q * v [ZMOD |q ^ 2 - p * q - p ^ 2|] := by
  let d := q ^ 2 - p * q - p ^ 2
  have hpq : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hfactor : q * (q - p) - p ^ 2 = d := by dsimp [d]; ring
  -- Reducing d modulo q or p leaves a signed square of the other term.
  have hdq : IsCoprime d q := by
    rw [← hfactor, IsCoprime.mul_sub_left_left_iff]
    exact hpq.pow_left
  have hdp : IsCoprime d p := by
    rw [show d = q ^ 2 - p * (q + p) by dsimp [d]; ring, IsCoprime.sub_mul_left_left_iff]
    exact hpq.symm.pow_left
  have hd : d ≠ 0 := by
    intro h
    simp only [h, isCoprime_zero_left, Int.isUnit_iff] at hdp hdq
    rcases hdp with rfl | rfl <;> rcases hdq with rfl | rfl <;> norm_num [d] at h
  have hdsub : IsCoprime d (q - p) := by
    rw [← hfactor, IsCoprime.mul_sub_right_left_iff]
    have hp_sub : IsCoprime p (q - p) := by
      simpa only [mul_one] using (IsCoprime.sub_mul_left_right_iff (z := (1 : ℤ))).mpr hpq
    exact hp_sub.pow_left
  have hinverse {c : ℤ} (hc : IsCoprime d c) : ∃ w : ℤ, c * w ≡ 1 [ZMOD d] := by
    obtain ⟨w, z, hw⟩ := hc.symm
    exact ⟨w, Int.modEq_of_dvd ⟨z, by linear_combination -hw⟩⟩
  have hsolve {c k w : ℤ} (hw : c * w ≡ 1 [ZMOD d]) :
      (a * c ≡ k [ZMOD d]) ↔ a ≡ k * w [ZMOD d] := by
    constructor
    · intro h
      calc
        a ≡ a * (c * w) [ZMOD d] := by simpa only [mul_one] using (hw.mul_left a).symm
        _ ≡ k * w [ZMOD d] := by simpa only [mul_assoc] using h.mul_right w
    · intro h
      calc
        a * c ≡ (k * w) * c [ZMOD d] := h.mul_right c
        _ ≡ k [ZMOD d] := by simpa only [mul_assoc, mul_comm w c, mul_one] using hw.mul_left k
  change _ ↔ ∃ u v : ℤ, (q - p) * u ≡ 1 [ZMOD |d|] ∧ p * v ≡ 1 [ZMOD |d|] ∧
    a ≡ -b * p * u [ZMOD |d|] ∧ a ≡ -b * q * v [ZMOD |d|]
  simp only [Int.modEq_abs]
  have hnum : (b - a) * p + a * q = a * (q - p) - (-b * p) := by ring
  rw [isGibonacciGood_div_iff_dvd a b p q hq, and_iff_right hd, hdq.dvd_mul_left_iff,
    hnum, ← Int.modEq_iff_dvd, Int.modEq_comm]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := hinverse hdsub
    obtain ⟨v, hv⟩ := hinverse hdp
    have ha := (hsolve hu).mp h
    -- The quadratic relation makes the two residue formulas agree.
    have hquad : p ^ 2 ≡ q * (q - p) [ZMOD d] := by
      rw [Int.modEq_iff_dvd, hfactor]
    have huv : p * u ≡ q * v [ZMOD d] := calc
      p * u ≡ (p * u) * (p * v) [ZMOD d] := by
        simpa only [mul_one] using (hv.mul_left (p * u)).symm
      _ ≡ (q * (q - p)) * (u * v) [ZMOD d] := by
        convert hquad.mul_right (u * v) using 1
        ring
      _ ≡ q * v [ZMOD d] := by
        convert hu.mul_left (q * v) using 1 <;> ring
    refine ⟨u, v, hu, hv, ha, ha.trans ?_⟩
    simpa only [mul_assoc] using huv.mul_left (-b)
  · rintro ⟨u, _, hu, _, ha, _⟩
    exact (hsolve hu).mpr ha

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

-- Reverse the recurrence to express both seeds in the current consecutive pair.
private theorem gibonacci_seed_coefficients (G : ℕ → ℤ)
    (hrec : ∀ n, G (n + 2) = G (n + 1) + G n) (n : ℕ) :
    ∃ u v : ℤ, G 0 = u * G n + v * G (n + 1) ∧
      G 1 = v * G n + (u + v) * G (n + 1) := by
  induction n with
  | zero => exact ⟨1, 0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨u, v, h₀, h₁⟩ := ih
    refine ⟨v - u, u, ?_, ?_⟩
    · rw [h₀, hrec n]
      ring
    · rw [h₁, hrec n]
      ring

private theorem gibonacci_denom_ne_zero (x : ℚ) : 1 - x - x ^ 2 ≠ 0 := by
  intro h
  exact (by norm_num : ¬ IsSquare (5 : ℚ)) ⟨2 * x + 1, by linear_combination 4 * h⟩

/-- **Good consecutive ratios of a Gibonacci sequence.** Let $p$ and $q$ be coprime integers,
let $(H_n)_{n \ge 0}$ be the Gibonacci sequence with $H_0 = p$ and $H_1 = q$, and put
$m = |q^2 - pq - p^2|$. Call a pair of integers $(a, b)$ admissible when $H_n / H_{n+1}$ is
good for $(a, b)$ for every natural number $n$ with $H_{n+1} \ne 0$. Then there are infinitely
many admissible pairs, and a pair $(a, b)$ is admissible if and only if there are integers $u$
and $v$ with $(q - p) u \equiv 1$, $p v \equiv 1$, $a \equiv -b p u$ and
$a \equiv -b q v \pmod{m}$.

In the source's notation, with modular inverses, the condition reads
$a \equiv -bp(q - p)^{-1} \equiv -bqp^{-1} \pmod{m}$. The source indexes $H$ by all integers.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Theorem 3
(`jis-2024-24.3.1-thm-3`). -/
public theorem isGibonacciGood_ratios_infinite_iff (p q : ℤ)
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
        a ≡ -b * q * v [ZMOD |q ^ 2 - p * q - p ^ 2|] := by
  let H := gibonacciNumber p q
  let d := q ^ 2 - p * q - p ^ 2
  have hunit (hq : q = 0) : |d| = 1 := by
    have hp : IsUnit p := by
      simpa only [hq, isCoprime_zero_right] using Int.isCoprime_iff_gcd_eq_one.mpr hcop
    rcases Int.isUnit_iff.mp hp with rfl | rfl <;> norm_num [d, hq]
  have hd : d ≠ 0 := by
    by_cases hq : q = 0
    · intro hd
      simpa [hd] using hunit hq
    · have hz : IsGibonacciGood 0 0 ((p : ℚ) / q) :=
        ⟨gibonacci_denom_ne_zero _, 0, by simp [gibonacciGeneratingValue]⟩
      exact ((isGibonacciGood_div_iff_dvd 0 0 p q hq).mp hz).1
  have hrec (n : ℕ) : H (n + 2) = H (n + 1) + H n := rfl
  -- The quadratic denominator changes sign at each step.
  have hdet (n : ℕ) : H (n + 1) ^ 2 - H n * H (n + 1) - H n ^ 2 = (-1 : ℤ) ^ n * d := by
    induction n with
    | zero => simp [H, gibonacciNumber, d]
    | succ n ih =>
      change H (n + 2) ^ 2 - H (n + 1) * H (n + 2) - H (n + 1) ^ 2 = (-1) ^ (n + 1) * d
      calc
        _ = -(H (n + 1) ^ 2 - H n * H (n + 1) - H n ^ 2) := by rw [hrec n]; ring
        _ = _ := by rw [ih, pow_succ]; ring
  -- Divisibility of the linear numerator propagates even across a zero term of H.
  have hall (a b : ℤ) (h₀ : d ∣ (b - a) * p + a * q) (h₁ : d ∣ a * p + b * q) :
      ∀ n : ℕ, H (n + 1) ≠ 0 → IsGibonacciGood a b ((H n : ℚ) / H (n + 1)) := by
    let u (n : ℕ) := (b - a) * H n + a * H (n + 1)
    have hstep (n : ℕ) : u (n + 2) = u (n + 1) + u n := by
      change (b - a) * H (n + 2) + a * H ((n + 1) + 2) =
        ((b - a) * H (n + 1) + a * H (n + 2)) + ((b - a) * H n + a * H (n + 1))
      rw [hrec (n + 1), hrec n]
      ring
    have hu (n : ℕ) : d ∣ u n ∧ d ∣ u (n + 1) := by
      induction n with
      | zero =>
        refine ⟨h₀, ?_⟩
        change d ∣ (b - a) * q + a * (q + p)
        convert h₁ using 1; ring
      | succ n ih =>
        refine ⟨ih.2, ?_⟩
        change d ∣ u (n + 2)
        rw [hstep]
        exact dvd_add ih.2 ih.1
    intro n hn
    apply (isGibonacciGood_div_iff_dvd a b (H n) (H (n + 1)) hn).mpr
    rw [hdet]
    have hsign : IsUnit ((-1 : ℤ) ^ n) := isUnit_one.neg.pow n
    exact ⟨mul_ne_zero hsign.ne_zero hd, hsign.mul_left_dvd.mpr (dvd_mul_of_dvd_right (hu n).1 _)⟩
  have hmultiple (t : ℤ) :
      ∀ n : ℕ, H (n + 1) ≠ 0 → IsGibonacciGood (d * t) 0 ((H n : ℚ) / H (n + 1)) :=
    hall (d * t) 0 ⟨t * (q - p), by ring⟩ ⟨t * p, by ring⟩
  constructor
  · refine Set.infinite_of_injective_forall_mem (f := fun t : ℤ => (d * t, (0 : ℤ))) ?_ hmultiple
    intro x y h
    exact mul_left_cancel₀ hd (congrArg Prod.fst h)
  · intro a b
    constructor
    · intro h
      by_cases hq : q = 0
      · rw [hunit hq]
        exact ⟨0, 0, Int.modEq_one, Int.modEq_one, Int.modEq_one, Int.modEq_one⟩
      · by_cases hab : (a, b) = (0, 0)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
          -- Use the nonzero pair (d, 0) to get the same modular inverses.
          obtain ⟨u, v, hu, hv, _, _⟩ := (isGibonacciGood_iff d 0 p q
            (fun he => hd (congrArg Prod.fst he)) hcop hq).mp
            (by simpa only [H, gibonacciNumber, mul_one] using hmultiple 1 0 hq)
          exact ⟨u, v, hu, hv, by simp, by simp⟩
        · exact (isGibonacciGood_iff a b p q hab hcop hq).mp (h 0 hq)
    · rintro ⟨u, v, hu, hv, ha, hb⟩
      simp only [Int.modEq_abs] at hu hv ha hb
      have hcancel {c w k : ℤ} (hw : c * w ≡ 1 [ZMOD d]) (h : a ≡ k * w [ZMOD d]) :
          d ∣ a * c - k := by
        have hc : a * c ≡ k [ZMOD d] := calc
          a * c ≡ (k * w) * c [ZMOD d] := h.mul_right c
          _ ≡ k [ZMOD d] := by simpa only [mul_assoc, mul_comm w c, mul_one] using hw.mul_left k
        exact hc.symm.dvd
      apply hall a b
      · convert hcancel hu ha using 1; ring
      · convert hcancel hv hb using 1; ring

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
  intro n hn
  obtain ⟨u, v, ha, hb⟩ := gibonacci_seed_coefficients G (fun _ => rfl) n
  change a = _ at ha
  change b = _ at hb
  have hn' : (G n : ℚ) ≠ 0 := by exact_mod_cast hn
  change IsGibonacciGood a b (-(G (n + 1) : ℚ) / G n)
  refine ⟨gibonacci_denom_ne_zero _, u * G n, ?_⟩
  rw [gibonacciGeneratingValue, div_eq_iff (gibonacci_denom_ne_zero _), ha, hb]
  push_cast
  field_simp [hn']
  ring

/-- **Consecutive ratios of a shifted Gibonacci sequence are good.** Let $a$ and $b$ be integers
and let $(H_n)_{n \ge 0}$ be the Gibonacci sequence with $H_0 = -b$ and $H_1 = a$. For every
natural number $n$ with $H_{n+1} \ne 0$, the ratio $H_n / H_{n+1}$ is good for $(a, b)$.

The source indexes $H$ by all integers.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 8
(`jis-2024-24.3.1-lem-8`). -/
public theorem isGibonacciGood_shifted_ratio (a b : ℤ) (n : ℕ)
    (h : gibonacciNumber (-b) a (n + 1) ≠ 0) :
    IsGibonacciGood a b
      ((gibonacciNumber (-b) a n : ℚ) / (gibonacciNumber (-b) a (n + 1) : ℚ)) := by
  let H := gibonacciNumber (-b) a
  obtain ⟨u, v, hb, ha⟩ := gibonacci_seed_coefficients H (fun _ => rfl) n
  change -b = _ at hb
  change a = _ at ha
  have hq : (H (n + 1) : ℚ) ≠ 0 := by exact_mod_cast h
  change IsGibonacciGood a b ((H n : ℚ) / H (n + 1))
  refine ⟨gibonacci_denom_ne_zero _, (u + v) * H (n + 1), ?_⟩
  rw [gibonacciGeneratingValue, div_eq_iff (gibonacci_denom_ne_zero _), ha,
    neg_eq_iff_eq_neg.mp hb]
  push_cast
  field_simp [hq]
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

/-- **Membership in a two-sided Fibonacci pair orbit.** Let $v,w\in\mathbb{Z}^2$ and let
$S(x,y)=(y,x+y)$ and $B(x,y)=(y-x,x)$ be the forward and backward Fibonacci steps.
Then $w$ belongs to the two-sided orbit of $v$ if and only if there exists
$n\in\mathbb{N}$ such that $w=S^n(v)$ or $w=B^n(v)$. -/
public theorem mem_fibonacciPairOrbit_iff (v w : ℤ × ℤ) :
    w ∈ fibonacciPairOrbit v ↔
      ∃ n : ℕ, w = fibonacciPairStep^[n] v ∨ w = fibonacciPairStepBack^[n] v :=
  Iff.rfl

private def signedReverseFibonacciPair (s : ℤ) (v : ℤ × ℤ) : ℤ × ℤ :=
  (s * -v.2, s * v.1)

/-- Lemma 9: the values `H_n / H_{n+1}` (`n ∈ ℤ`, `H_{n+1} ≠ 0`) of the
sequence with `H_0 = -b`, `H_1 = a` are exactly the values
`-G_{n+1} / G_n` (`n ∈ ℤ`, `G_n ≠ 0`) of the Gibonacci sequence with
`G_0 = a`, `G_1 = b`; both index sets run over the two-sided orbits.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 9 (`jis-2024-24.3.1-lem-9`). -/
public theorem gibonacci_shifted_ratios_eq_negated_ratios (a b : ℤ) :
    {x : ℚ | ∃ v ∈ fibonacciPairOrbit (-b, a), v.2 ≠ 0 ∧ x = (v.1 : ℚ) / v.2} =
      {x : ℚ | ∃ w ∈ fibonacciPairOrbit (a, b), w.1 ≠ 0 ∧ x = -(w.2 : ℚ) / w.1} := by
  by_cases hab : (a, b) = (0, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    have hmem (v : ℤ × ℤ) : v ∈ fibonacciPairOrbit (0, 0) ↔ v = (0, 0) := by
      rw [mem_fibonacciPairOrbit_iff]
      simp only [Function.iterate_fixed (f := fibonacciPairStep) (x := (0, 0)) rfl,
        Function.iterate_fixed (f := fibonacciPairStepBack) (x := (0, 0)) rfl, or_self,
        exists_const]
    ext x
    simp [hmem]
  -- Swapping the coordinates and negating the new first coordinate interchanges the steps,
  -- up to a common sign.
  have hiter (n : ℕ) :
      fibonacciPairStep^[n] (-b, a) =
        signedReverseFibonacciPair ((-1) ^ n) (fibonacciPairStepBack^[n] (a, b)) ∧
      fibonacciPairStepBack^[n] (-b, a) =
        signedReverseFibonacciPair ((-1) ^ n) (fibonacciPairStep^[n] (a, b)) := by
    induction n with
    | zero => simp [signedReverseFibonacciPair]
    | succ n ih =>
      simp only [Function.iterate_succ_apply', ih.1, ih.2, pow_succ]
      constructor <;> apply Prod.ext <;>
        simp only [fibonacciPairStep, fibonacciPairStepBack, signedReverseFibonacciPair] <;> ring
  refine Set.ext fun x => ?_
  simp only [Set.mem_ofPred_eq]
  -- The common nonzero sign cancels in the fraction and preserves its domain.
  have hratio (n : ℕ) (w : ℤ × ℤ) :
      let v := signedReverseFibonacciPair ((-1) ^ n) w
      (v.2 ≠ 0 ∧ x = (v.1 : ℚ) / v.2) ↔ (w.1 ≠ 0 ∧ x = -(w.2 : ℚ) / w.1) := by
    have hs : (-1 : ℤ) ^ n ≠ 0 := pow_ne_zero _ (by decide)
    have hs' : (↑((-1 : ℤ) ^ n) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs
    simp only [signedReverseFibonacciPair, mul_ne_zero_iff, and_iff_right hs, Int.cast_mul,
      Int.cast_neg, mul_div_mul_left _ _ hs']
  constructor
  · rintro ⟨v, hv, hx⟩
    rcases (mem_fibonacciPairOrbit_iff _ _).mp hv with ⟨n, rfl | rfl⟩
    · refine ⟨_, (mem_fibonacciPairOrbit_iff _ _).mpr ⟨n, Or.inr rfl⟩, (hratio n _).mp ?_⟩
      rwa [← (hiter n).1]
    · refine ⟨_, (mem_fibonacciPairOrbit_iff _ _).mpr ⟨n, Or.inl rfl⟩, (hratio n _).mp ?_⟩
      rwa [← (hiter n).2]
  · rintro ⟨w, hw, hx⟩
    rcases (mem_fibonacciPairOrbit_iff _ _).mp hw with ⟨n, rfl | rfl⟩
    · refine ⟨_, (mem_fibonacciPairOrbit_iff _ _).mpr ⟨n, Or.inr rfl⟩, ?_⟩
      rw [(hiter n).2]
      exact (hratio n _).mpr hx
    · refine ⟨_, (mem_fibonacciPairOrbit_iff _ _).mpr ⟨n, Or.inl rfl⟩, ?_⟩
      rw [(hiter n).1]
      exact (hratio n _).mpr hx

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
