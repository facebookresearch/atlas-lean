/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Real.Irrational
public import MathlibExt.NumberTheory.PerrinSequence

namespace MetaMathlibExt

@[expose] public section

/-- **Perrin sequence at negative indices.** The Perrin sequence $R_k$, given by $R_0 = 3$,
$R_1 = 0$, $R_2 = 2$ and $R_{k+3} = R_{k+1} + R_k$, extends uniquely to all integers $k$ by
running the recurrence backward. This defines the integers $R_{-n}$ for natural numbers $n$:
$R_0 = 3$, $R_{-1} = -1$, $R_{-2} = 1$ and $R_{-(n+3)} = R_{-n} - R_{-(n+2)}$ for every $n \ge 0$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2–4. -/
public def perrinNeg : ℕ → ℤ
  | 0 => 3
  | 1 => -1
  | 2 => 1
  | n + 3 => perrinNeg n - perrinNeg (n + 2)

/-- **The Perrin sequence and its backward extension fit together at index zero.** Write $R_n$
for the Perrin sequence and $R_{-n}$ for its extension to negative indices, for natural numbers
$n$. The two definitions give the same value at index $0$, and the Perrin recurrence holds across
index $0$: $R_2 = R_0 + R_{-1}$ and $R_1 = R_{-1} + R_{-2}$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2–4. -/
public theorem perrinNeg_bridge :
    perrinNeg 0 = (perrinSequence 0 : ℤ) ∧
      (perrinSequence 2 : ℤ) = perrinSequence 0 + perrinNeg 1 ∧
        (perrinSequence 1 : ℤ) = perrinNeg 1 + perrinNeg 2 := by
  decide

/-- **Perrin recurrence at negative indices.** Let $R_{-k}$ denote the Perrin sequence extended
to negative indices. For every natural number $n$, $R_{-n} = R_{-(n+2)} + R_{-(n+3)}$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2–4. -/
public theorem perrinNeg_rec (n : ℕ) :
    perrinNeg n = perrinNeg (n + 2) + perrinNeg (n + 3) := by
  rw [perrinNeg]; ring

/-- **Some values of the Perrin sequence at negative indices.** The Perrin sequence $R_k$
extended to negative indices satisfies $R_{-5} = 4$, $R_{-18} = 25$,
$R_{-1} = R_{-7} = R_{-11} = R_{-29} = -1$ and $R_{-2} = 1$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2 and 4. -/
public theorem perrinNeg_small_values :
    perrinNeg 5 = 4 ∧ perrinNeg 18 = 25 ∧ perrinNeg 1 = -1 ∧ perrinNeg 7 = -1 ∧
      perrinNeg 11 = -1 ∧ perrinNeg 29 = -1 ∧ perrinNeg 2 = 1 := by
  decide

/-- **Perrin numbers that are squares of Perrin numbers.** Let $R_n$ denote the $n$-th term of
the Perrin sequence. For positive integers $n$ and $m$, $R_n = R_m^2$ holds if and only if
$n = m = 1$ (where $R_1 = 0 = R_1^2$).

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 1
(`integers-2025-A70-thm-1`). -/
public theorem_wanted perrinSequence_eq_sq_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    perrinSequence n = perrinSequence m ^ 2 ↔ n = 1 ∧ m = 1

/-- **Negative-index Perrin numbers equal to plus or minus a Perrin square.** Let $R_k$ denote the
Perrin sequence, extended to negative indices. The pairs of positive integers $(n, m)$ with
$R_{-n} = R_m^2$ or $R_{-n} = -R_m^2$ are exactly $(5, 2)$, $(5, 4)$, $(18, 5)$ and $(18, 6)$;
that is, $R_{-5} = 4 = R_2^2 = R_4^2$ and $R_{-18} = 25 = R_5^2 = R_6^2$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 2
(`integers-2025-A70-thm-2`). -/
public theorem_wanted perrinNeg_eq_pm_perrinSequence_sq :
    {nm : ℕ × ℕ | 0 < nm.1 ∧ 0 < nm.2 ∧
      (perrinNeg nm.1 = (perrinSequence nm.2 : ℤ) ^ 2 ∨
        perrinNeg nm.1 = -((perrinSequence nm.2 : ℤ) ^ 2))} =
      {(5, 2), (5, 4), (18, 5), (18, 6)}

/-- **No positive-index Perrin number is the square of a negative-index one.** Let $R_n$ denote
the $n$-th term of the Perrin sequence and $R_{-m}$ the term at index $-m$ of its backward
extension to negative indices. For all positive integers $n$ and $m$, $R_n \ne R_{-m}^2$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 3
(`integers-2025-A70-thm-3`). -/
public theorem_wanted perrinSequence_ne_perrinNeg_sq {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (perrinSequence n : ℤ) ≠ perrinNeg m ^ 2

/-- **Negative-index Perrin numbers equal to plus or minus a negative-index Perrin square.** Let
$R_{-k}$ denote the Perrin sequence extended to negative indices. The pairs of positive integers
$(n, m)$ with $R_{-n} = R_{-m}^2$ or $R_{-n} = -R_{-m}^2$ are exactly the pairs with
$n, m \in \{1, 2, 7, 11, 29\}$, together with $(5, 3)$, $(5, 6)$, $(5, 20)$, $(18, 8)$ and
$(18, 16)$.

Here $R_{-m} = \pm 1$ for $m \in \{1, 2, 7, 11, 29\}$, while
$R_{-5} = 4 = R_{-3}^2 = R_{-6}^2 = R_{-20}^2$ and $R_{-18} = 25 = R_{-8}^2 = R_{-16}^2$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 4
(`integers-2025-A70-thm-4`). -/
public theorem_wanted perrinNeg_eq_pm_perrinNeg_sq :
    {nm : ℕ × ℕ | 0 < nm.1 ∧ 0 < nm.2 ∧
      (perrinNeg nm.1 = perrinNeg nm.2 ^ 2 ∨ perrinNeg nm.1 = -(perrinNeg nm.2 ^ 2))} =
      ({1, 2, 7, 11, 29} : Set ℕ) ×ˢ ({1, 2, 7, 11, 29} : Set ℕ) ∪
        {(5, 3), (5, 6), (5, 20), (18, 8), (18, 16)}

/-- **The only zero of the two-sided Perrin sequence.** Let $R_n$ denote the $n$-th term of
the Perrin sequence and $R_{-n}$ the term at index $-n$ of its backward extension to negative
indices. For every natural number $n$, $R_n = 0$ if and only if $n = 1$, and $R_{-n} \ne 0$.
Thus $R_1 = 0$ is the only zero of the sequence $(R_k)_{k \in \mathbb{Z}}$.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 5
(`integers-2025-A70-thm-5`). -/
public theorem_wanted perrin_zero_unique :
    (∀ n : ℕ, perrinSequence n = 0 ↔ n = 1) ∧ ∀ n : ℕ, perrinNeg n ≠ 0

/-- **Size of the Perrin numbers at negative indices.** Let $\alpha$ be a real number with
$\alpha^3 = \alpha + 1$ (the real root of $X^3 - X - 1$), and let $R_{-k}$ denote the Perrin
sequence extended to negative indices. For every integer $k \ge 6$,

$$\alpha^{k/2 - 3 \cdot 10^{15} \log k} < |R_{-k}| < 2.01 \, \alpha^{k/2}.$$

The source quotes this bound from Bravo, Bravo and Luca.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Lemma 1
(`integers-2025-A70-lem-1`). -/
public theorem_wanted perrinNeg_abs_bounds {α : ℝ} (hα : α ^ 3 = α + 1) {k : ℕ} (hk : 6 ≤ k) :
    α ^ ((k : ℝ) / 2 - 3 * 10 ^ 15 * Real.log k) < |(perrinNeg k : ℝ)| ∧
      |(perrinNeg k : ℝ)| < 2.01 * α ^ ((k : ℝ) / 2)

/-- **Matveev's lower bound for two logarithms (complex case).** Let $K$ be a number field of
degree $D = [K : \mathbb{Q}]$ with a field embedding $f : K \to \mathbb{C}$, let
$\eta_1, \eta_2 \in K$ be nonzero, and let $b_1, b_2$ be integers. Let $B$ be a real number with
$|b_1| \le B$ and $|b_2| \le B$, and let $A_1, A_2$ be real numbers with
$A_j \ge \max(D\,h(\eta_j), |\log f(\eta_j)|, 0.16)$ for $j = 1, 2$, where $h$ is the absolute
logarithmic Weil height and $\log$ is the principal branch of the complex logarithm. Put
$\Lambda = f(\eta_1)^{b_1} f(\eta_2)^{b_2} - 1$. If $\Lambda \ne 0$, then

$$|\Lambda| > \exp\bigl(-9.20483 \cdot 10^{11} \, D^2 A_1 A_2 (1 + \log D)(1 + \log(2B))\bigr).$$

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 6
(`integers-2025-A70-thm-6`). -/
public theorem_wanted matveev_two_logs_complex_lower_bound
    {K : Type*} [Field K] [NumberField K] (f : K →+* ℂ)
    {η₁ η₂ : K} (h₁ : η₁ ≠ 0) (h₂ : η₂ ≠ 0) (b₁ b₂ : ℤ) {B A₁ A₂ : ℝ}
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B)
    (hA₁ : max (max ((Module.finrank ℚ K : ℝ) * NumberField.absLogHeight₁ η₁)
      ‖Complex.log (f η₁)‖) 0.16 ≤ A₁)
    (hA₂ : max (max ((Module.finrank ℚ K : ℝ) * NumberField.absLogHeight₁ η₂)
      ‖Complex.log (f η₂)‖) 0.16 ≤ A₂)
    (hΛ : f η₁ ^ b₁ * f η₂ ^ b₂ - 1 ≠ 0) :
    Real.exp (-(9.20483 * 10 ^ 11 * (Module.finrank ℚ K : ℝ) ^ 2 * A₁ * A₂ *
        (1 + Real.log (Module.finrank ℚ K : ℝ)) * (1 + Real.log (2 * B)))) <
      ‖f η₁ ^ b₁ * f η₂ ^ b₂ - 1‖

/-- **Lower bound for $|x - p/q|$ from bounded partial quotients.** Let $x$ be an irrational real
number with continued fraction expansion $[a_0; a_1, a_2, \dots]$, where $a_0 = \lfloor x \rfloor$,
and with convergents $p_k / q_k$. Let $M \ge 1$ and $N \ge 0$ be integers with
$q_N \le M < q_{N+1}$, and let $a$ be a real number with $a \ge a_j$ for every $0 \le j \le N + 1$.
Then

$$\left|x - \frac{p}{q}\right| > \frac{1}{(a + 2) q^2}$$

for all integers $p$ and $q$ with $0 < q < M$.

The source takes $a$ to be the maximum of $a_0, \dots, a_{N+1}$; since the bound weakens as $a$
grows, the two forms are equivalent.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Lemma 3
(`integers-2025-A70-lem-3`). -/
public theorem_wanted one_div_partialQuotient_bound_lt_abs_sub {x : ℝ} (hx : Irrational x)
    {M N : ℕ} (hM : 0 < M) (hNM : (GenContFract.of x).dens N ≤ M)
    (hMN : (M : ℝ) < (GenContFract.of x).dens (N + 1)) {aM : ℝ} (ha0 : (⌊x⌋ : ℝ) ≤ aM)
    (ha : ∀ j ≤ N, ∀ b : ℝ, (GenContFract.of x).partDens.get? j = some b → b ≤ aM)
    {p q : ℤ} (hq : 0 < q) (hqM : q < M) :
    1 / ((aM + 2) * (q : ℝ) ^ 2) < |x - p / q|

/-- **Convergents minimize $|p - qx|$ up to their denominator.** Let $x$ be an irrational real
number with continued fraction convergents $p_k / q_k$, where $p_0 / q_0 = \lfloor x \rfloor / 1$.
If $n > 1$ is a natural number and $p, q$ are integers with $0 < q \le q_n$ and
$p / q \ne p_n / q_n$, then $|p_n - q_n x| < |p - q x|$.

This is Theorem 182 of Hardy and Wright.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 10
(`integers-2025-A70-thm-10`). -/
public theorem_wanted abs_convergent_num_sub_lt_of_le_den {x : ℝ} (hx : Irrational x)
    {n : ℕ} (hn : 1 < n) {p q : ℤ} (hq : 0 < q) (hqn : (q : ℝ) ≤ (GenContFract.of x).dens n)
    (hne : (p : ℝ) / q ≠ (GenContFract.of x).nums n / (GenContFract.of x).dens n) :
    |(GenContFract.of x).nums n - (GenContFract.of x).dens n * x| < |p - q * x|

end

end MetaMathlibExt
