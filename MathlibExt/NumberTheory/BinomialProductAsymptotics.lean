/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Constants and bounds for products of binomial coefficients

This module defines Kellner's factorial-product constants and comparison functions and proves
the sharp upper bound of `7 / 6` for `1 / a + 1 / b - 1 / (a + b)` on positive integers of sum
at least three.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Glaisher–Kinkelin constant.** The Glaisher–Kinkelin constant is the real number
$$A = \exp\left(\frac{1}{12} - \operatorname{Re} \zeta'(-1)\right),$$
where $\zeta'$ is the complex derivative of the Riemann zeta function $\zeta$. Since $\zeta'(-1)$
is real, $\log A = \frac{1}{12} - \zeta'(-1)$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Section 2. -/
public noncomputable def glaisherKinkelinConstant : ℝ :=
  Real.exp (1 / 12 - (deriv riemannZeta (-1 : ℂ)).re)

/-- **Logarithm of the Glaisher–Kinkelin constant.** The Glaisher–Kinkelin constant $A$ satisfies
$\log A = \frac{1}{12} - \operatorname{Re} \zeta'(-1)$, where $\zeta'$ is the complex derivative
of the Riemann zeta function.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Section 2. -/
public theorem log_glaisherKinkelinConstant :
    Real.log glaisherKinkelinConstant = 1 / 12 - (deriv riemannZeta (-1 : ℂ)).re :=
  Real.log_exp _

/-- **Factorial-product constants.** For a natural number $k \ge 1$, the constant $F_k$ is the
positive real number defined by
$$\log F_k = \frac{k}{4} \log(2\pi) - \frac{k^2+1}{k} \log A + \frac{1 - \log k}{12k} -
\sum_{\nu=1}^{k-1} \frac{\nu}{k} \log \Gamma\left(\frac{\nu}{k}\right),$$
where $A$ is the Glaisher–Kinkelin constant and $\Gamma$ is the gamma function. For $k = 0$ the
definition gives $F_0 = 1$.

The constant $F_k$ appears in the asymptotic formula for $\prod_{\nu=1}^{n} (k\nu)!$ as
$n \to \infty$; that formula is a separate statement.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, equation (3) (Kellner 2009, Theorems 12
and 13). -/
public noncomputable def factorialProductConstant (k : ℕ) : ℝ :=
  Real.exp ((k : ℝ) / 4 * Real.log (2 * Real.pi) -
    ((k : ℝ) ^ 2 + 1) / k * Real.log glaisherKinkelinConstant +
    (1 - Real.log k) / (12 * k) -
    ∑ ν ∈ Finset.Ico 1 k, (ν : ℝ) / k * Real.log (Real.Gamma ((ν : ℝ) / k)))

/-- **Logarithm of the first factorial product constant.** The factorial product constant $F_1$
satisfies $\log F_1 = \frac{1}{4} \log(2\pi) + \frac{1}{12} - 2 \log A$, where $A$ is the
Glaisher–Kinkelin constant.

Equivalently, $F_1 = (2\pi)^{1/4} e^{1/12} A^{-2}$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Table 1. -/
public theorem log_factorialProductConstant_one :
    Real.log (factorialProductConstant 1) =
      1 / 4 * Real.log (2 * Real.pi) + 1 / 12 - 2 * Real.log glaisherKinkelinConstant := by
  rw [factorialProductConstant, Real.log_exp]
  norm_num
  ring

/-- **Positivity of the factorial-product constants.** For every natural number $k$, the
factorial-product constant $F_k$ is positive.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Section 2. -/
public theorem factorialProductConstant_pos (k : ℕ) : 0 < factorialProductConstant k :=
  Real.exp_pos _

/-- **Comparison function for products of factorials.** For a natural number $k$, the comparison
function $P_k \colon \mathbb{R} \to \mathbb{R}$ is defined by
$$P_k(x) = (k^k)^{x(x+1)/2} \left(\frac{2\pi k x}{e}\right)^{x/2} x^{(3k+1)/(12k)}.$$

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5. -/
public noncomputable def factorialProductComparison (k : ℕ) (x : ℝ) : ℝ :=
  ((k : ℝ) ^ k) ^ (x * (x + 1) / 2) * (2 * Real.pi * k / Real.exp 1 * x) ^ (x / 2) *
    x ^ ((3 * (k : ℝ) + 1) / (12 * k))

/-- **Value of the factorial-product comparison function at $1$.** For every natural number
$k$, the factorial-product comparison function $P_k$ satisfies $P_k(1) = k^k (2\pi k/e)^{1/2}$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5. -/
public theorem factorialProductComparison_one (k : ℕ) :
    factorialProductComparison k 1 =
      (k : ℝ) ^ k * (2 * Real.pi * k / Real.exp 1) ^ ((1 : ℝ) / 2) := by
  simp [factorialProductComparison]

/-- **Comparison function for products of binomial coefficients.** For natural numbers $a$ and
$b$, let $c = a - b$ if $b \le a$ and $c = 0$ otherwise. The comparison function
$P_{a,b} \colon \mathbb{R} \to \mathbb{R}$ is defined by
$$P_{a,b}(x) = \left(\frac{a^a}{b^b c^c}\right)^{x(x+1)/2} x^{(1/a - a/(bc))/12 - 1/4} \Big/
\left(\frac{2\pi}{e} \cdot \frac{bc}{a} \cdot x\right)^{x/2}.$$

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 6. -/
public noncomputable def binomialProductComparison (a b : ℕ) (x : ℝ) : ℝ :=
  ((a : ℝ) ^ a / ((b : ℝ) ^ b * ((a - b : ℕ) : ℝ) ^ (a - b))) ^ (x * (x + 1) / 2) *
    x ^ ((1 / (a : ℝ) - a / (b * ((a - b : ℕ) : ℝ))) / 12 - 1 / 4) /
    (2 * Real.pi / Real.exp 1 * (b * ((a - b : ℕ) : ℝ) / a) * x) ^ (x / 2)

/-- **Value of the binomial-product comparison function at $1$.** For natural numbers $a$ and
$b$, let $c = a - b$ if $b \le a$ and $c = 0$ otherwise. Then the binomial-product comparison
function $P_{a,b}$ satisfies
$$P_{a,b}(1) = \frac{a^a / (b^b c^c)}{\bigl((2\pi/e)(bc/a)\bigr)^{1/2}}.$$

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 6. -/
public theorem binomialProductComparison_one (a b : ℕ) :
    binomialProductComparison a b 1 =
      (a : ℝ) ^ a / ((b : ℝ) ^ b * ((a - b : ℕ) : ℝ) ^ (a - b)) /
        (2 * Real.pi / Real.exp 1 * (b * ((a - b : ℕ) : ℝ) / a)) ^ ((1 : ℝ) / 2) := by
  simp [binomialProductComparison]

/-- **Bounds for $1/a + 1/b - 1/(a+b)$.** Let $a$ and $b$ be natural numbers with $a, b \ge 1$
and $a + b \ge 3$, and put $g(a,b) = 1/a + 1/b - 1/(a+b)$. Then $0 < g(a,b) \le 7/6$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Lemma 3. -/
public theorem inv_add_inv_sub_inv_add_bounds (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 3 ≤ a + b) :
    0 < (1 / a + 1 / b - 1 / (a + b) : ℚ) ∧ (1 / a + 1 / b - 1 / (a + b) : ℚ) ≤ 7 / 6 := by
  wlog h : a ≤ b generalizing a b
  · simpa only [add_comm (b : ℚ) a, add_comm (1 / (b : ℚ)) (1 / (a : ℚ))]
      using this b a hb ha (by omega) (by omega)
  have hb₂ : (2 : ℚ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
  have ha₀ : (0 : ℚ) < a := by exact_mod_cast ha
  constructor
  · rw [sub_pos]
    calc
      1 / ((a : ℚ) + b) ≤ 1 / b :=
        one_div_le_one_div_of_le (by linarith) (le_add_of_nonneg_left ha₀.le)
      _ < _ := lt_add_of_pos_left _ (by positivity)
  · by_cases ha₁ : a = 1
    · subst a
      rw [Nat.cast_one]
      calc
        _ = 1 + 1 / ((b : ℚ) * (1 + b)) := by
          field_simp
          ring
        _ ≤ 1 + 1 / (2 * (1 + 2) : ℚ) := by gcongr
        _ = _ := by norm_num
    · have ha₂ : (2 : ℚ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
      calc
        _ ≤ 1 / (a : ℚ) + 1 / b := sub_le_self _ (by positivity)
        _ ≤ 1 / (2 : ℚ) + 1 / 2 := by gcongr
        _ ≤ _ := by norm_num

end

end MetaMathlibExt
