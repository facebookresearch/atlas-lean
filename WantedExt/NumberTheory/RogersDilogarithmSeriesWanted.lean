/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Rogers dilogarithm series of Hoorfar--Qi, Bridgeman, and Sanford

Statement-only targets from Chance Sanford, *A Dilogarithm Series and a Generalization of a
Theorem of Bridgeman*, INTEGERS 25 (2025), Article A52 (texts checked against
arXiv:2410.21619v2). Each statement writes the Rogers dilogarithm inline as
`L x = ∑_{n ≥ 1} xⁿ/n² + (log x · log (1 - x))/2`; on `[0, 1]` this is the paper's `L`, including
`L 0 = 0` and `L 1 = π²/6` (Lean's `log 0 = 0`), and every argument below lies in `[0, 1]`.
-/

open Real

namespace MetaMathlibExt

@[expose] public section

/-- **Hoorfar–Qi dilogarithm series.** Write $L(x) = \sum_{m \ge 1} x^m/m^2 +
\frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on $[0, 1]$ (with $\log 0 = 0$). For
positive integers $p, q$ and real numbers $\theta, \beta$ with $0 < \theta < 1$ and
$0 < \beta < 1$,
$$
\sum_{n \ge 0} L\left(\frac{\beta(1 - \theta^p)(1 - \theta^q)\theta^n}
{(1 - \beta\theta^{n+p})(1 - \beta\theta^{n+q})}\right) =
\sum_{n=0}^{q-1} L\left(\frac{\beta(1 - \theta^p)\theta^n}{1 - \beta\theta^{n+p}}\right) +
\sum_{n=0}^{p-1} L\left(\frac{1 - \theta^q}{1 - \beta\theta^{n+q}}\right) - p\,L(1 - \theta^q).
$$

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 1, quoting Hoorfar and Qi (`integers-2025-A52-thm-1`). -/
public theorem_wanted rogersDilog_hoorfarQi_series {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {θ β : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    ∑' n : ℕ, L (β * (1 - θ ^ p) * (1 - θ ^ q) * θ ^ n /
        ((1 - β * θ ^ (n + p)) * (1 - β * θ ^ (n + q)))) =
      ∑ n ∈ Finset.range q, L (β * (1 - θ ^ p) * θ ^ n / (1 - β * θ ^ (n + p))) +
        ∑ n ∈ Finset.range p, L ((1 - θ ^ q) / (1 - β * θ ^ (n + q))) - p * L (1 - θ ^ q)

/-- **Bridgeman's dilogarithm series for a positive Pell solution.** Write
$L(x) = \sum_{m \ge 1} x^m/m^2 + \frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on
$[0, 1]$ (with $\log 0 = 0$). Let $n$ be a natural number that is not a perfect square, let
$a, b$ be positive rationals with $a^2 - n b^2 = 1$, and put $u = a + b\sqrt{n}$. Define rationals
$a_k, b_k$ by $a_0 = 1$, $b_0 = 0$, $a_{k+1} = a a_k + n b b_k$ and $b_{k+1} = b a_k + a b_k$,
so that $u^k = a_k + b_k\sqrt{n}$. Then
$$
L(1/u^2) = \sum_{k \ge 2} L(b^2/b_k^2),
$$
and if $a$ and $b$ are integers, then for every $k \ge 0$ there is an integer $m$ with $b_k = bm$.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 3 (3), quoting Bridgeman (`integers-2025-A52-thm-3`). -/
public theorem_wanted rogersDilog_pell_positive_series {n : ℕ} (hn : ¬ IsSquare n) {a b : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hpell : a ^ 2 - n * b ^ 2 = 1) {A B : ℕ → ℚ}
    (hA₀ : A 0 = 1) (hB₀ : B 0 = 0) (hA : ∀ k, A (k + 1) = a * A k + n * b * B k)
    (hB : ∀ k, B (k + 1) = b * A k + a * B k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    L (1 / ((a : ℝ) + b * √n) ^ 2) = ∑' k : ℕ, L ((b : ℝ) ^ 2 / (B (k + 2) : ℝ) ^ 2) ∧
      ((∃ a' b' : ℤ, a = a' ∧ b = b') → ∀ k, ∃ m : ℤ, B k = b * m)

/-- **Bridgeman's dilogarithm series for a negative Pell solution.** Write
$L(x) = \sum_{m \ge 1} x^m/m^2 + \frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on
$[0, 1]$ (with $\log 0 = 0$). Let $n$ be a natural number that is not a perfect square, let
$a, b$ be positive rationals with $a^2 - n b^2 = -1$, and put $u = a + b\sqrt{n}$. Define rationals
$a_k, b_k$ by $a_0 = 1$, $b_0 = 0$, $a_{k+1} = a a_k + n b b_k$ and $b_{k+1} = b a_k + a b_k$,
so that $u^k = a_k + b_k\sqrt{n}$. Then
$$
L(1/u^2) = \sum_{k \ge 1} L\left(\frac{a^2}{n b_{2k}^2}\right) +
\sum_{k \ge 1} L\left(\frac{a^2}{a_{2k+1}^2}\right),
$$
and if $a$ and $b$ are integers, then for every $k \ge 0$ both $b_{2k}/a$ and $a_{2k+1}/a$ are
integers.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 3 (4), quoting Bridgeman (`integers-2025-A52-thm-3`). -/
public theorem_wanted rogersDilog_pell_negative_series {n : ℕ} (hn : ¬ IsSquare n) {a b : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hpell : a ^ 2 - n * b ^ 2 = -1) {A B : ℕ → ℚ}
    (hA₀ : A 0 = 1) (hB₀ : B 0 = 0) (hA : ∀ k, A (k + 1) = a * A k + n * b * B k)
    (hB : ∀ k, B (k + 1) = b * A k + a * B k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    L (1 / ((a : ℝ) + b * √n) ^ 2) =
        ∑' k : ℕ, L ((a : ℝ) ^ 2 / (n * (B (2 * (k + 1)) : ℝ) ^ 2)) +
          ∑' k : ℕ, L ((a : ℝ) ^ 2 / (A (2 * (k + 1) + 1) : ℝ) ^ 2) ∧
      ((∃ a' b' : ℤ, a = a' ∧ b = b') →
        ∀ k, (∃ m : ℤ, B (2 * k) = a * m) ∧ ∃ m : ℤ, A (2 * k + 1) = a * m)

/-- **Sanford's coupled recurrence.** Let $a, b$ be real numbers in $(0, 1)$ with $a \ne b$, and
for every natural number $m$ put
$$
x_m = \frac{a(a - b)(1 - b)^m}{a(1 - b)^{m+1} - b(1 - a)^{m+1}}, \qquad
y_m = \frac{b(a - b)(1 - a)^m}{a(1 - b)^{m+1} - b(1 - a)^{m+1}}.
$$
Then for every natural number $n$,
$$
x_{n+1} = \frac{x_n(1 - y_n)}{1 - x_n y_n} \quad\text{and}\quad
y_{n+1} = \frac{y_n(1 - x_n)}{1 - x_n y_n}.
$$

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Lemma 1 (`integers-2025-A52-lem-1`). -/
public theorem_wanted sanford_coupled_recurrence {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (hab : a ≠ b) (n : ℕ) :
    let x : ℕ → ℝ := fun m =>
      a * (a - b) * (1 - b) ^ m / (a * (1 - b) ^ (m + 1) - b * (1 - a) ^ (m + 1))
    let y : ℕ → ℝ := fun m =>
      b * (a - b) * (1 - a) ^ m / (a * (1 - b) ^ (m + 1) - b * (1 - a) ^ (m + 1))
    x (n + 1) = x n * (1 - y n) / (1 - x n * y n) ∧ y (n + 1) = y n * (1 - x n) / (1 - x n * y n)

/-- **Sanford's dilogarithm series identity.** Write $L(x) = \sum_{m \ge 1} x^m/m^2 +
\frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on $[0, 1]$ (with $\log 0 = 0$). For
real numbers $a, b \in (0, 1)$ with $a \ne b$,
$$
\sum_{n \ge 0} L\left(\frac{ab(a - b)^2(1 - a)^n(1 - b)^n}
{\left(a(1 - b)^{n+1} - b(1 - a)^{n+1}\right)^2}\right) =
L(a) + L(b) - L\left(\frac{|a - b|}{1 - \min(a, b)}\right).
$$

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 4 (`integers-2025-A52-thm-4`). -/
public theorem_wanted rogersDilog_sanford_principal_series {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (hab : a ≠ b) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    ∑' n : ℕ, L (a * b * (a - b) ^ 2 * (1 - a) ^ n * (1 - b) ^ n /
        (a * (1 - b) ^ (n + 1) - b * (1 - a) ^ (n + 1)) ^ 2) =
      L a + L b - L (|a - b| / (1 - min a b))

/-- **Sanford's symmetric dilogarithm series.** Write $L(x) = \sum_{m \ge 1} x^m/m^2 +
\frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on $[0, 1]$ (with $\log 0 = 0$). For
every real number $a \in (0, 1)$,
$$
\sum_{n \ge 1} L\left(\frac{a^2 \left(\frac{1 - a}{2}\right)^n \left(\frac{1 + a}{2}\right)^n}
{\left(\left(\frac{1 + a}{2}\right)^{n+1} - \left(\frac{1 - a}{2}\right)^{n+1}\right)^2}\right) =
L\left(\frac{1 - a}{1 + a}\right).
$$

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Corollary 1 (`integers-2025-A52-cor-1`). -/
public theorem_wanted rogersDilog_sanford_symmetric_series {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    ∑' n : ℕ, L (a ^ 2 * (1 / 2 - a / 2) ^ (n + 1) * (1 / 2 + a / 2) ^ (n + 1) /
        ((1 / 2 + a / 2) ^ (n + 2) - (1 / 2 - a / 2) ^ (n + 2)) ^ 2) =
      L ((1 - a) / (1 + a))

/-- **Sanford's Lucas-sequence dilogarithm series for $Q > 0$.** Write
$L(x) = \sum_{m \ge 1} x^m/m^2 + \frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on
$[0, 1]$ (with $\log 0 = 0$). Let $(P, Q)$ be Lucas sequence parameters with $P > 0$, $Q > 0$ and
$D = P^2 - 4Q > 0$, let $U = U(P, Q)$ be the Lucas sequence, and put $\alpha = (P + \sqrt{D})/2$.
Then for every integer $k \ge 1$,
$$
\sum_{n \ge 1} L\left(\frac{U_k^2 Q^{kn}}{U_{k(n+1)}^2}\right) =
L\left(\frac{Q^k}{\alpha^{2k}}\right).
$$

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 5 (8) (`integers-2025-A52-thm-5`). -/
public theorem_wanted rogersDilog_lucasU_series (params : LucasSequenceParams)
    (hP : 0 < params.p) (hQ : 0 < params.q) (hD : 0 < params.p ^ 2 - 4 * params.q)
    {k : ℕ} (hk : 0 < k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    let α : ℝ := (params.p + √((params.p ^ 2 - 4 * params.q : ℤ) : ℝ)) / 2
    ∑' n : ℕ, L ((lucasU params k : ℝ) ^ 2 * (params.q : ℝ) ^ (k * (n + 1)) /
        (lucasU params (k * (n + 2)) : ℝ) ^ 2) = L ((params.q : ℝ) ^ k / α ^ (2 * k))

/-- **Sanford's Lucas-sequence dilogarithm series for $Q < 0$.** Write
$L(x) = \sum_{m \ge 1} x^m/m^2 + \frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on
$[0, 1]$ (with $\log 0 = 0$). Let $(P, Q)$ be Lucas sequence parameters with $P > 0$ and $Q < 0$,
let $U = U(P, Q)$ be the Lucas sequence and $V = V(P, Q)$ its companion, and put $D = P^2 - 4Q$
and $\alpha = (P + \sqrt{D})/2$. Then for every odd natural number $k$,
$$
\sum_{n \ge 1} L\left(-\frac{V_k^2 Q^{k(2n-1)}}{D\,U_{2kn}^2}\right) +
\sum_{n \ge 1} L\left(\frac{V_k^2 Q^{2kn}}{V_{k(2n+1)}^2}\right) =
L\left(-\frac{Q^k}{\alpha^{2k}}\right).
$$

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 5 (9) (`integers-2025-A52-thm-5`). -/
public theorem_wanted rogersDilog_lucasUV_series_of_neg (params : LucasSequenceParams)
    (hP : 0 < params.p) (hQ : params.q < 0) {k : ℕ} (hk : Odd k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    let D : ℤ := params.p ^ 2 - 4 * params.q
    let α : ℝ := (params.p + √(D : ℝ)) / 2
    ∑' n : ℕ, L (-(lucasV params k : ℝ) ^ 2 * (params.q : ℝ) ^ (k * (2 * n + 1)) /
        ((D : ℝ) * (lucasU params (2 * k * (n + 1)) : ℝ) ^ 2)) +
      ∑' n : ℕ, L ((lucasV params k : ℝ) ^ 2 * (params.q : ℝ) ^ (2 * k * (n + 1)) /
        (lucasV params (k * (2 * n + 3)) : ℝ) ^ 2) =
      L (-(params.q : ℝ) ^ k / α ^ (2 * k))

end

end MetaMathlibExt
