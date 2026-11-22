/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.RingTheory.Radical.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
public import MathlibExt.Algebra.Polynomial.CoefficientDenominator

namespace MetaMathlibExt

@[expose] public section

open Polynomial Filter Asymptotics UniqueFactorizationMonoid

/-- `B_0(x) = 1` has denominator `1` (the convention `𝔇_0 = 1`).

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2, after
Theorem 7. -/
theorem polynomialDenominator_bernoulli_zero :
    polynomialDenominator (Polynomial.bernoulli 0) = 1 := by
  rw [polynomialDenominator_eq_one_iff, Polynomial.bernoulli_zero]
  intro i
  rw [Polynomial.coeff_one]
  split_ifs <;> rfl

/-- The denominator `𝔻_n = ∏_{p prime, s_p(n) ≥ p} p` of `B_n(x) - B_n`, where `s_p(n)` is the
sum of the base-`p` digits of `n`. The paper defines `𝔻_n := denom(B_n(x) - B_n)` and quotes this
product formula from Kellner (2017), Section 5; we take the product as the definition and record
the identification as `bernoulliDiffDenominator_eq_polynomialDenominator`. Primes with
`s_p(n) ≥ p` satisfy `p ≤ n`, so the range bound loses nothing.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2, equation
(2.3) (`eq:ddprod`); OEIS A195441. -/
def bernoulliDiffDenominator (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≤ (Nat.digits p n).sum), p

/-- First values `𝔻_1, …, 𝔻_10 = 1, 1, 2, 1, 6, 2, 6, 3, 10, 2`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2 (displayed
values of `𝔻_n`). -/
theorem bernoulliDiffDenominator_small :
    [bernoulliDiffDenominator 1, bernoulliDiffDenominator 2, bernoulliDiffDenominator 3,
      bernoulliDiffDenominator 4, bernoulliDiffDenominator 5, bernoulliDiffDenominator 6,
      bernoulliDiffDenominator 7, bernoulliDiffDenominator 8, bernoulliDiffDenominator 9,
      bernoulliDiffDenominator 10] = [1, 1, 2, 1, 6, 2, 6, 3, 10, 2] := by
  decide +kernel

/-- The factor `𝔻^⊥_n = ∏_{p ∤ n, s_p(n) ≥ p} p` of `𝔻_n` (primes not dividing `n`).

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2, equation
(2.8) (`eq:ddprod2`); OEIS A324370. -/
def bernoulliDiffDenominatorCoprimePart (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ ¬ p ∣ n ∧ p ≤ (Nat.digits p n).sum), p

/-- Values `𝔻^⊥_1 = 1`, `𝔻^⊥_2 = 1`, `𝔻^⊥_3 = 2`, `𝔻^⊥_5 = 6`, `𝔻^⊥_9 = 10`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2, equation
(2.8). -/
theorem bernoulliDiffDenominatorCoprimePart_small :
    [bernoulliDiffDenominatorCoprimePart 1, bernoulliDiffDenominatorCoprimePart 2,
      bernoulliDiffDenominatorCoprimePart 3, bernoulliDiffDenominatorCoprimePart 5,
      bernoulliDiffDenominatorCoprimePart 9] = [1, 1, 2, 6, 10] := by
  decide +kernel

/-- The factor `𝔻^+_n = ∏_{p > √n, s_p(n) ≥ p} p` of `𝔻_n`; `p > √n` is written `n < p ^ 2`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 1, equation
(1.4) (`eq:ddp`). -/
def bernoulliDiffDenominatorLargePart (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum), p

/-- Values `𝔻^+_4 = 1`, `𝔻^+_5 = 3`, `𝔻^+_9 = 5`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 1, equation
(1.4). -/
theorem bernoulliDiffDenominatorLargePart_small :
    [bernoulliDiffDenominatorLargePart 4, bernoulliDiffDenominatorLargePart 5,
      bernoulliDiffDenominatorLargePart 9] = [1, 3, 5] := by
  decide +kernel

/-- The set `\overline{𝒮}_k = {n ≥ 1 : B_n^{(k)}(x) ∈ ℤ[x]}` of indices whose `k`-th derivative
Bernoulli polynomial has only integral coefficients; `\overline{𝒮} = \overline{𝒮}_1`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 1
(`\overline{𝒮}`) and Section 3 (`\overline{𝒮}_k`). -/
def bernoulliIntegralDerivativeIndices (k : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ polynomialDenominator (derivative^[k] (Polynomial.bernoulli n)) = 1}

/-- `B_1'(x) = 1 ∈ ℤ[x]`, so `1 ∈ \overline{𝒮}`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 1 (`1 ∈ 𝒮`).
-/
theorem one_mem_bernoulliIntegralDerivativeIndices_one :
    1 ∈ bernoulliIntegralDerivativeIndices 1 := by
  refine ⟨le_rfl, ?_⟩
  rw [polynomialDenominator_eq_one_iff]
  intro i
  simp only [Function.iterate_one, Polynomial.bernoulli_one, derivative_sub, derivative_X,
    derivative_C, sub_zero, Polynomial.coeff_one]
  split_ifs <;> rfl

/-- Bridge: for `n ≥ 1`, the product `𝔻_n` is the denominator of `B_n(x) - B_n`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2,
definition of `𝔻_n` and equation (2.3), quoting Kellner (2017), Section 5. -/
public theorem_wanted bernoulliDiffDenominator_eq_polynomialDenominator (n : ℕ) (hn : 1 ≤ n) :
    bernoulliDiffDenominator n =
      polynomialDenominator (Polynomial.bernoulli n - C (_root_.bernoulli n))

/-- Kellner's conjecture (i): `𝔻^+_n > 1` for all `n > 192`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Conjecture 2 (i),
quoting Kellner (2017), Conjectures 1, 2. -/
def KellnerLargePartConjecture : Prop :=
  ∀ n : ℕ, 192 < n → 1 < bernoulliDiffDenominatorLargePart n

/-- Kellner's conjecture (ii): there is `κ > 1` with `ω(𝔻^+_n) ∼ κ √n / log n`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Conjecture 2 (ii),
equation (1.6). -/
def KellnerLargePartAsymptoticConjecture : Prop :=
  ∃ κ : ℝ, 1 < κ ∧
    (fun n : ℕ => (ArithmeticFunction.cardDistinctFactors (bernoulliDiffDenominatorLargePart n) :
      ℝ)) ~[atTop] fun n : ℕ => κ * Real.sqrt n / Real.log n

/-- Conjecture 2 (i) implies `\overline{𝒮} = 𝒮 = {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}`
(Conjecture 1 (ii)), and Conjecture 2 (ii) implies that `\overline{𝒮}` is finite
(Conjecture 1 (i)).

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 3
(`jis-2024-24.2.8-thm-3`). -/
public theorem_wanted kellner_conjectures_imply_bernoulli_integral_derivative_conjectures :
    (KellnerLargePartConjecture →
      bernoulliIntegralDerivativeIndices 1 = {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}) ∧
    (KellnerLargePartAsymptoticConjecture → (bernoulliIntegralDerivativeIndices 1).Finite)

/-- Conjecture 2 (ii) holds (Bordellès, Luca, Moree, and Shparlinski, with `κ = 2`), so the set
`\overline{𝒮}` of `n ≥ 1` with `B_n'(x) ∈ ℤ[x]` is finite.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Corollary 4, quoting
Bordellès, Luca, Moree, and Shparlinski (2018), Corollary 1.6 (`jis-2024-24.2.8-cor-4`). -/
public theorem_wanted kellnerLargePartAsymptoticConjecture_and_finite_integral_derivative :
    KellnerLargePartAsymptoticConjecture ∧ (bernoulliIntegralDerivativeIndices 1).Finite

/-- If `B_n'(x) ∈ ℤ[x]` then `n + 1` is prime, and any such `n` outside
`𝒮 = {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}` exceeds `10^7`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 5
(`jis-2024-24.2.8-thm-5`). -/
public theorem_wanted bernoulli_integral_derivative_succ_prime_and_large :
    (∀ n ∈ bernoulliIntegralDerivativeIndices 1, (n + 1).Prime) ∧
    ∀ n ∈ bernoulliIntegralDerivativeIndices 1,
      n ∉ ({1, 2, 4, 6, 10, 12, 28, 30, 36, 60} : Set ℕ) → 10 ^ 7 < n

/-- For `n ≥ 1`: `𝔇_n = rad(𝒟_n)` where `𝒟_n` is the denominator of
`S_n(x) = (B_{n+1}(x) - B_{n+1}) / (n + 1)`; `𝔇_n` is even, so `B_n(x) ∉ ℤ[x]`; and `𝔻^⊥_n` is
even for odd `n ≥ 3` and odd otherwise. Part (iii) is printed as "otherwise, `𝔻^⊥_n` is even",
which fails at `n = 2` (`𝔻^⊥_2 = 1`); the proof in the paper shows `𝔻^⊥_1 = 1` and
`2 ∤ 𝔻^⊥_n` for even `n`, and that corrected reading is formalized.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Corollary 8
(`jis-2024-24.2.8-cor-8`). -/
public theorem_wanted bernoulli_polynomial_denominator_rad_even (n : ℕ) (hn : 1 ≤ n) :
    polynomialDenominator (Polynomial.bernoulli n) =
        radical (polynomialDenominator
          (C ((n : ℚ) + 1)⁻¹ * (Polynomial.bernoulli (n + 1) - C (_root_.bernoulli (n + 1))))) ∧
      Even (polynomialDenominator (Polynomial.bernoulli n)) ∧
      (∃ i, ((Polynomial.bernoulli n).coeff i).den ≠ 1) ∧
      (3 ≤ n → Odd n → Even (bernoulliDiffDenominatorCoprimePart n)) ∧
      (n = 1 ∨ Even n → Odd (bernoulliDiffDenominatorCoprimePart n))

/-- For `n ≥ 1`: `B_n'(x) ∈ ℤ[x]` iff `𝔻^⊥_n = 1`, iff `𝔇_{n-1} = rad(n)`; in these cases `n + 1`
is prime.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 9
(`jis-2024-24.2.8-thm-9`). -/
public theorem_wanted bernoulli_derivative_integral_iff (n : ℕ) (hn : 1 ≤ n) :
    (n ∈ bernoulliIntegralDerivativeIndices 1 ↔ bernoulliDiffDenominatorCoprimePart n = 1) ∧
    (bernoulliDiffDenominatorCoprimePart n = 1 ↔
      polynomialDenominator (Polynomial.bernoulli (n - 1)) = radical n) ∧
    (n ∈ bernoulliIntegralDerivativeIndices 1 → (n + 1).Prime)

/-- Let `\overline{ℛ} = {n ≥ 1 : 𝔻_n = rad(n + 1)}`. For `n ∈ \overline{ℛ}`, `n + 1` is composite;
if `n` is odd then `𝔻^⊥_{n+1} = 1`, and otherwise `n = 2^e` with `e ≥ 1`. The set
`\overline{ℛ}` is finite. (Composite is `¬ (n + 1).Prime`, as `n + 1 ≥ 2`.)

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 10
(`jis-2024-24.2.8-thm-10`). -/
public theorem_wanted bernoulliDiffDenominator_eq_radical_succ_properties :
    (∀ n : ℕ, 1 ≤ n → bernoulliDiffDenominator n = radical (n + 1) →
      ¬ (n + 1).Prime ∧
      (Odd n → bernoulliDiffDenominatorCoprimePart (n + 1) = 1) ∧
      (Even n → ∃ e, 1 ≤ e ∧ n = 2 ^ e)) ∧
    {n : ℕ | 1 ≤ n ∧ bernoulliDiffDenominator n = radical (n + 1)}.Finite

/-- If the odd elements of `\overline{ℛ} = {n ≥ 1 : 𝔻_n = rad(n + 1)}` are exactly
`{3, 5, 9, 11, 27, 29, 35, 59}` (Conjecture 11 reduced to odd `n`), then
`\overline{𝒮} = {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}` (Conjecture 1; finiteness follows).

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 12
(`jis-2024-24.2.8-thm-12`). -/
public theorem_wanted odd_radical_conjecture_implies_bernoulli_integral_derivative_conjecture
    (h : {n : ℕ | 1 ≤ n ∧ bernoulliDiffDenominator n = radical (n + 1) ∧ Odd n} =
      {3, 5, 9, 11, 27, 29, 35, 59}) :
    bernoulliIntegralDerivativeIndices 1 = {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}

/-- For `k, n ≥ 1`, the denominator `𝔇_n^{(k)}` of `B_n^{(k)}(x)` equals, when `n ≥ k`,
`𝔇_{n-k} / gcd(𝔇_{n-k}, (n)_k) = 𝔻^⊥_{n-k+1} / gcd(𝔻^⊥_{n-k+1}, (n)_{k-1})
= ∏_{p ∤ (n)_k, s_p(n-k+1) ≥ p} p`, and `1` when `n < k`; no prime `p ≤ k` divides it; and
`𝔇_n^{(1)} = 𝔇_{n-1} / rad(n) = 𝔻^⊥_n`. Here `(n)_k = n.descFactorial k`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 13
(`jis-2024-24.2.8-thm-13`). -/
public theorem_wanted bernoulli_higher_derivative_denominator (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (k ≤ n →
      polynomialDenominator (derivative^[k] (Polynomial.bernoulli n)) =
          polynomialDenominator (Polynomial.bernoulli (n - k)) /
            Nat.gcd (polynomialDenominator (Polynomial.bernoulli (n - k))) (n.descFactorial k) ∧
        polynomialDenominator (derivative^[k] (Polynomial.bernoulli n)) =
          bernoulliDiffDenominatorCoprimePart (n - k + 1) /
            Nat.gcd (bernoulliDiffDenominatorCoprimePart (n - k + 1)) (n.descFactorial (k - 1)) ∧
        polynomialDenominator (derivative^[k] (Polynomial.bernoulli n)) =
          ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ n.descFactorial k ∧
            p ≤ (Nat.digits p (n - k + 1)).sum), p) ∧
    (n < k → polynomialDenominator (derivative^[k] (Polynomial.bernoulli n)) = 1) ∧
    (∀ p : ℕ, p.Prime → p ≤ k →
      ¬ p ∣ polynomialDenominator (derivative^[k] (Polynomial.bernoulli n))) ∧
    (k = 1 →
      polynomialDenominator (derivative (Polynomial.bernoulli n)) =
          polynomialDenominator (Polynomial.bernoulli (n - 1)) / radical n ∧
        polynomialDenominator (derivative (Polynomial.bernoulli n)) =
          bernoulliDiffDenominatorCoprimePart n)

/-- Every `\overline{𝒮}_k` (`k ≥ 1`) is finite, and `\overline{𝒮}_k ⊆ \overline{𝒮}_{k+1}`.
The paper writes `⊂`; its proof gives inclusion, which is what is formalized.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 14
(`jis-2024-24.2.8-thm-14`). -/
public theorem_wanted bernoulliIntegralDerivativeIndices_finite_and_mono :
    (∀ k : ℕ, 1 ≤ k → (bernoulliIntegralDerivativeIndices k).Finite) ∧
    ∀ k : ℕ, 1 ≤ k →
      bernoulliIntegralDerivativeIndices k ⊆ bernoulliIntegralDerivativeIndices (k + 1)

/-- For `n ≥ 1`: `𝔻_n` is odd iff `n = 2^e` (`e ≥ 0`); if `n + 1` is composite then
`rad(n + 1)` divides `𝔻_n` and `𝔻^⊥_n`; and for odd `n ≥ 3`,
`𝔻_n = lcm(𝔻_{n+1}, rad(n + 1))`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Lemma 16
(`jis-2024-24.2.8-lem-16`). -/
public theorem_wanted bernoulliDiffDenominator_parity_radical_lcm (n : ℕ) (hn : 1 ≤ n) :
    (Odd (bernoulliDiffDenominator n) ↔ ∃ e, n = 2 ^ e) ∧
    (¬ (n + 1).Prime → radical (n + 1) ∣ bernoulliDiffDenominator n ∧
      radical (n + 1) ∣ bernoulliDiffDenominatorCoprimePart n) ∧
    (3 ≤ n → Odd n →
      bernoulliDiffDenominator n = Nat.lcm (bernoulliDiffDenominator (n + 1)) (radical (n + 1)))

/-- For `n ≥ 1`, `𝔻^+_n` divides `𝔻^⊥_n`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Lemma 17
(`jis-2024-24.2.8-lem-17`). -/
public theorem_wanted bernoulliDiffDenominatorLargePart_dvd_coprimePart (n : ℕ) (hn : 1 ≤ n) :
    bernoulliDiffDenominatorLargePart n ∣ bernoulliDiffDenominatorCoprimePart n

/-- For `k ≥ 1` there is `n_k` with `𝔻^+_n > (n + k)_k = (n + 1) ⋯ (n + k)` for all `n > n_k`.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Lemma 18
(`jis-2024-24.2.8-lem-18`). -/
public theorem_wanted bernoulliDiffDenominatorLargePart_eventually_gt_descFactorial (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n, N < n → (n + k).descFactorial k < bernoulliDiffDenominatorLargePart n

end

end MetaMathlibExt
