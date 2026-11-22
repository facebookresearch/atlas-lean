/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- The Glaisher–Kinkelin constant `A`, defined by `log A = 1/12 - ζ'(-1)`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Section 2. -/
public noncomputable def glaisherKinkelinConstant : ℝ :=
  Real.exp (1 / 12 - (deriv riemannZeta (-1 : ℂ)).re)

/-- `log A = 1/12 - ζ'(-1)`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Section 2. -/
public theorem log_glaisherKinkelinConstant :
    Real.log glaisherKinkelinConstant = 1 / 12 - (deriv riemannZeta (-1 : ℂ)).re :=
  Real.log_exp _

/-- The constants `F_k` of the asymptotic formula for `∏_{ν ≤ n} (kν)!`, defined by the
closed form `log F_k = (k/4) log(2π) - ((k^2+1)/k) log A + (1 - log k)/(12k)
- ∑_{ν=1}^{k-1} (ν/k) log Γ(ν/k)`; that this closed form is the asymptotic constant of
the factorial product is `tendsto_prod_factorial_mul_div` below.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, equation (3) (Kellner 2009, Theorems 12
and 13). -/
public noncomputable def factorialProductConstant (k : ℕ) : ℝ :=
  Real.exp ((k : ℝ) / 4 * Real.log (2 * Real.pi) -
    ((k : ℝ) ^ 2 + 1) / k * Real.log glaisherKinkelinConstant +
    (1 - Real.log k) / (12 * k) -
    ∑ ν ∈ Finset.Ico 1 k, (ν : ℝ) / k * Real.log (Real.Gamma ((ν : ℝ) / k)))

/-- `log F_1 = (1/4) log(2π) + 1/12 - 2 log A`, i.e. `F_1 = (2π)^{1/4} e^{1/12} A^{-2}`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Table 1. -/
public theorem log_factorialProductConstant_one :
    Real.log (factorialProductConstant 1) =
      1 / 4 * Real.log (2 * Real.pi) + 1 / 12 - 2 * Real.log glaisherKinkelinConstant := by
  rw [factorialProductConstant, Real.log_exp]
  norm_num
  ring

/-- `F_k > 0`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Section 2. -/
public theorem factorialProductConstant_pos (k : ℕ) : 0 < factorialProductConstant k :=
  Real.exp_pos _

/-- The comparison function `P_k(x) = (k^k)^{x(x+1)/2} (2πk x / e)^{x/2} x^{(3k+1)/(12k)}`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5. -/
public noncomputable def factorialProductComparison (k : ℕ) (x : ℝ) : ℝ :=
  ((k : ℝ) ^ k) ^ (x * (x + 1) / 2) * (2 * Real.pi * k / Real.exp 1 * x) ^ (x / 2) *
    x ^ ((3 * (k : ℝ) + 1) / (12 * k))

/-- `P_k(1) = k^k (2πk/e)^{1/2}`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5. -/
public theorem factorialProductComparison_one (k : ℕ) :
    factorialProductComparison k 1 =
      (k : ℝ) ^ k * (2 * Real.pi * k / Real.exp 1) ^ ((1 : ℝ) / 2) := by
  simp [factorialProductComparison]

/-- The comparison function `P_{a,b}(x) = (a^a/(b^b c^c))^{x(x+1)/2}
x^{(1/a - a/(bc))/12 - 1/4} / ((2π/e)(bc/a) x)^{x/2}` with `c = a - b`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 6. -/
public noncomputable def binomialProductComparison (a b : ℕ) (x : ℝ) : ℝ :=
  ((a : ℝ) ^ a / ((b : ℝ) ^ b * ((a - b : ℕ) : ℝ) ^ (a - b))) ^ (x * (x + 1) / 2) *
    x ^ ((1 / (a : ℝ) - a / (b * ((a - b : ℕ) : ℝ))) / 12 - 1 / 4) /
    (2 * Real.pi / Real.exp 1 * (b * ((a - b : ℕ) : ℝ) / a) * x) ^ (x / 2)

/-- `P_{a,b}(1) = (a^a/(b^b c^c)) / ((2π/e)(bc/a))^{1/2}`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 6. -/
public theorem binomialProductComparison_one (a b : ℕ) :
    binomialProductComparison a b 1 =
      (a : ℝ) ^ a / ((b : ℝ) ^ b * ((a - b : ℕ) : ℝ) ^ (a - b)) /
        (2 * Real.pi / Real.exp 1 * (b * ((a - b : ℕ) : ℝ) / a)) ^ ((1 : ℝ) / 2) := by
  simp [binomialProductComparison]

/-- For `k ≥ 1`, `∏_{ν=1}^n (kν)! ∼ F_k A^k (2π)^{1/4} × (k e^{-3/2} n)^{k n(n+1)/2}
(2πk e^{k/2-1} n)^{n/2} n^{(k^2+3k+1)/(12k)}` with `F_k` given by the closed form (3).
The divergent expansion (4) is not formalized.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 1 (Kellner 2009, Theorems 12 and
13). -/
public theorem_wanted tendsto_prod_factorial_mul_div (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => (∏ ν ∈ Finset.Icc 1 n, ((k * ν).factorial : ℝ)) /
        (glaisherKinkelinConstant ^ k * (2 * Real.pi) ^ ((1 : ℝ) / 4) *
          ((k : ℝ) * Real.exp (-3 / 2) * n) ^ ((k : ℝ) * (n * (n + 1) / 2)) *
          (2 * Real.pi * k * Real.exp ((k : ℝ) / 2 - 1) * n) ^ ((n : ℝ) / 2) *
          (n : ℝ) ^ (((k : ℝ) ^ 2 + 3 * k + 1) / (12 * k))))
      atTop (𝓝 (factorialProductConstant k))

/-- The sequence `(F_k)_{k ≥ 1}` is strictly decreasing with limit `1`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Corollary 2. -/
public theorem_wanted factorialProductConstant_strictAnti_tendsto_one :
    StrictAnti (fun k : ℕ => factorialProductConstant (k + 1)) ∧
      Tendsto factorialProductConstant atTop (𝓝 1)

/-- For `a, b ≥ 1` with `a + b ≥ 3`, `g(a,b) = 1/a + 1/b - 1/(a+b)` satisfies
`7/6 ≥ g(a,b) > 0`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Lemma 3. -/
public theorem_wanted inv_add_inv_sub_inv_add_bounds (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 3 ≤ a + b) :
    0 < (1 / a + 1 / b - 1 / (a + b) : ℚ) ∧ (1 / a + 1 / b - 1 / (a + b) : ℚ) ≤ 7 / 6

/-- For `a > b ≥ 1`, `c_{a,b} = F_a/(F_b F_{a-b})` lies in `[c_{2,1}, 1)`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Lemma 4. -/
public theorem_wanted factorialProductConstant_ratio_mem_Ico (a b : ℕ) (hb : 1 ≤ b)
    (hab : b < a) :
    factorialProductConstant a / (factorialProductConstant b * factorialProductConstant (a - b))
      ∈ Set.Ico (factorialProductConstant 2 / factorialProductConstant 1 ^ 2) 1

/-- For `r ≥ 2`, `b_1, …, b_r ≥ 1` and `a = b_1 + ⋯ + b_r`,
`∏_{n=1}^m (an; b_1 n, …, b_r n) ∼ C_{a,b} × P_a(m)/(P_{b_1}(m) ⋯ P_{b_r}(m))`, with
`C_{a,b} = c_{a,b} (2π)^{(1-r)/4}` and `c_{a,b} = F_a/(F_{b_1} ⋯ F_{b_r}) ∈ (0, 1)`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5. -/
public theorem_wanted tendsto_prod_multinomial_div (r : ℕ) (hr : 2 ≤ r) (b : Fin r → ℕ)
    (hb : ∀ i, 1 ≤ b i) :
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m,
        (Nat.multinomial Finset.univ (fun i => b i * n) : ℝ)) /
        (factorialProductComparison (∑ i, b i) m /
          ∏ i, factorialProductComparison (b i) m))
      atTop (𝓝 (factorialProductConstant (∑ i, b i) / (∏ i, factorialProductConstant (b i)) *
        (2 * Real.pi) ^ ((1 - (r : ℝ)) / 4))) ∧
      factorialProductConstant (∑ i, b i) / (∏ i, factorialProductConstant (b i)) ∈
        Set.Ioo 0 1

/-- For `a > b ≥ 1` and `c = a - b`, `∏_{n=1}^m C(an, bn) ∼ C_{a,b} × P_{a,b}(m)` with
`C_{a,b} = c_{a,b} (2π)^{-1/4} ∈ [C_{2,1}, (2π)^{-1/4})`, `c_{a,b} = F_a/(F_b F_c)
∈ [c_{2,1}, 1)`, `c_{2,1} = F_2/F_1^2`, `C_{2,1} = c_{2,1} (2π)^{-1/4}`. The decimal
approximations are not part of this statement.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 6. -/
public theorem_wanted tendsto_prod_choose_div (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) :
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m, ((a * n).choose (b * n) : ℝ)) /
        binomialProductComparison a b m)
      atTop (𝓝 (factorialProductConstant a /
        (factorialProductConstant b * factorialProductConstant (a - b)) *
          (2 * Real.pi) ^ (-(1 : ℝ) / 4))) ∧
      factorialProductConstant a /
          (factorialProductConstant b * factorialProductConstant (a - b)) *
          (2 * Real.pi) ^ (-(1 : ℝ) / 4) ∈
        Set.Ico (factorialProductConstant 2 / factorialProductConstant 1 ^ 2 *
          (2 * Real.pi) ^ (-(1 : ℝ) / 4)) ((2 * Real.pi) ^ (-(1 : ℝ) / 4)) ∧
      factorialProductConstant a /
          (factorialProductConstant b * factorialProductConstant (a - b)) ∈
        Set.Ico (factorialProductConstant 2 / factorialProductConstant 1 ^ 2) 1

/-- Products of central binomial coefficients and of Catalan numbers:
`∏_{n=1}^m C(2n, n) ∼ C_{2,1} × 2^{m^2} (4e/π)^{m/2} / m^{m/2 + 3/8}` and
`∏_{n=1}^m Cat_n ∼ C_Cat × 2^{m^2} (4e^3/π)^{m/2} / m^{3m/2 + 15/8}`, with
`C_{2,1} = 2^{5/24} A^{3/2} / ((2π)^{1/2} e^{1/8})` and `C_Cat = C_{2,1} (2π)^{-1/2}`.
The decimal approximations are not part of this statement.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Corollary 7. -/
public theorem_wanted tendsto_prod_centralBinom_catalan_div :
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m, (n.centralBinom : ℝ)) /
        (2 ^ ((m : ℝ) ^ 2) * (4 * Real.exp 1 / Real.pi) ^ ((m : ℝ) / 2) /
          (m : ℝ) ^ ((m : ℝ) / 2 + 3 / 8)))
      atTop (𝓝 (2 ^ ((5 : ℝ) / 24) * glaisherKinkelinConstant ^ ((3 : ℝ) / 2) /
        ((2 * Real.pi) ^ ((1 : ℝ) / 2) * Real.exp (1 / 8)))) ∧
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m, (catalan n : ℝ)) /
        (2 ^ ((m : ℝ) ^ 2) * (4 * Real.exp 3 / Real.pi) ^ ((m : ℝ) / 2) /
          (m : ℝ) ^ (3 * (m : ℝ) / 2 + 15 / 8)))
      atTop (𝓝 (2 ^ ((5 : ℝ) / 24) * glaisherKinkelinConstant ^ ((3 : ℝ) / 2) /
        ((2 * Real.pi) ^ ((1 : ℝ) / 2) * Real.exp (1 / 8)) * (2 * Real.pi) ^ (-(1 : ℝ) / 2)))

/-- Binomial coefficients in a row of Pascal's triangle:
`∏_{ν=0}^n C(n, ν) ∼ C_row × e^{n^2/2 + n} / ((2π)^{n/2} n^{n/2 + 1/3})` with
`C_row = (F_1 (2π)^{1/4})^{-1} = A^2 / ((2π)^{1/2} e^{1/12})`.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 10. -/
public theorem_wanted tendsto_prod_choose_row_div :
    Tendsto (fun n : ℕ => (∏ ν ∈ Finset.range (n + 1), (n.choose ν : ℝ)) /
        (Real.exp ((n : ℝ) ^ 2 / 2 + n) /
          ((2 * Real.pi) ^ ((n : ℝ) / 2) * (n : ℝ) ^ ((n : ℝ) / 2 + 1 / 3))))
      atTop (𝓝 ((factorialProductConstant 1 * (2 * Real.pi) ^ ((1 : ℝ) / 4))⁻¹)) ∧
    (factorialProductConstant 1 * (2 * Real.pi) ^ ((1 : ℝ) / 4))⁻¹ =
      glaisherKinkelinConstant ^ 2 / ((2 * Real.pi) ^ ((1 : ℝ) / 2) * Real.exp (1 / 12))

/-- Theorem 10 as a limit of Theorem 6: `C_{a,1} → C_row` as `a → ∞`; for `n ≥ 1`,
`a^{-n(n+1)/2} ∏_{ν=1}^n C(aν, ν) → ∏_{ν=1}^n C(n, ν)`; and for real `x > 0`,
`a^{-x(x+1)/2} P_{a,1}(x) → P_row(x) = e^{x^2/2 + x}/((2π)^{x/2} x^{x/2+1/3})`. The paper
does not state the range of `x`; `x > 0` is assumed.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 11. -/
public theorem_wanted tendsto_binomialProduct_limit_row (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : 0 < x) :
    Tendsto (fun a : ℕ => factorialProductConstant a /
        (factorialProductConstant 1 * factorialProductConstant (a - 1)) *
          (2 * Real.pi) ^ (-(1 : ℝ) / 4))
      atTop (𝓝 ((factorialProductConstant 1 * (2 * Real.pi) ^ ((1 : ℝ) / 4))⁻¹)) ∧
    Tendsto (fun a : ℕ => (a : ℝ) ^ (-((n : ℝ) * (n + 1) / 2)) *
        ∏ ν ∈ Finset.Icc 1 n, ((a * ν).choose ν : ℝ))
      atTop (𝓝 (∏ ν ∈ Finset.Icc 1 n, (n.choose ν : ℝ))) ∧
    Tendsto (fun a : ℕ => (a : ℝ) ^ (-(x * (x + 1) / 2)) * binomialProductComparison a 1 x)
      atTop (𝓝 (Real.exp (x ^ 2 / 2 + x) / ((2 * Real.pi) ^ (x / 2) * x ^ (x / 2 + 1 / 3))))

/-- Hirschhorn's constant `C = lim_{n→∞} n^{-1/12} ∏_{k=1}^n k!/(√(2πk) (k/e)^k)` equals
`F_1 = (2π)^{1/4} e^{1/12} / A^2`. Only this identification of the constant is
formalized; Hirschhorn's asymptotic expansion with divergent Bernoulli sums is not.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 12 (Hirschhorn) and the discussion
after it. -/
public theorem_wanted tendsto_hirschhorn_constant :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 12) *
        ∏ k ∈ Finset.Icc 1 n, ((k.factorial : ℝ) /
          (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k)))
      atTop (𝓝 ((2 * Real.pi) ^ ((1 : ℝ) / 4) * Real.exp (1 / 12) /
        glaisherKinkelinConstant ^ 2)) ∧
    (2 * Real.pi) ^ ((1 : ℝ) / 4) * Real.exp (1 / 12) / glaisherKinkelinConstant ^ 2 =
      factorialProductConstant 1

end

end MetaMathlibExt
