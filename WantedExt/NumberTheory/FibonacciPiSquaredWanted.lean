/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.NumberTheory.FibonacciPiSquared

/-!
# Fibonacci numbers and `π²`

Statements from Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024),
no. 1 (paper `tonien10292023`), read from the extracted text layer (the primary PDF is not
reachable for agents).

The paper's sequences are pinned by hypotheses rather than new definitions: `p n` is the
polynomial sequence with `p 1 = 1` and
`p (n + 1) = (2X + 2n + 1)(2X + 2n + 2) p n - (X + 1)² p n (X + 1)` for `n ≥ 1` (the value `p 0`
is unused); `a` is the real Fibonacci-type sequence with `a 0 = -8√5 / 250`,
`a 1 = (25 - 4√5) / 250`; `b` has `b 0 = b 1 = 0` and
`b (n + 1) = b n + b (n - 1) + (-1)^(n+1) p n (0) / (2n)!` for `n ≥ 1`. In each display the second
identity is the continuation line `= …` of the aligned display that starts with `π² =`; the
text layer drops the repeated left side.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- **Fibonacci series for $\pi^2$ with polynomial weights.** Let $p_1, p_2, \dots$ be polynomials
with integer coefficients such that $p_1 = 1$ and, for every $n \ge 1$,
$p_{n+1}(x) = (2x + 2n + 1)(2x + 2n + 2)\, p_n(x) - (x + 1)^2 p_n(x + 1)$. Let $(a_n)_{n \ge 0}$
be real numbers with $a_0 = -8\sqrt{5}/250$, $a_1 = (25 - 4\sqrt{5})/250$ and
$a_{n+1} = a_n + a_{n-1}$ for $n \ge 1$, and let $(b_n)_{n \ge 0}$ be real numbers with
$b_0 = b_1 = 0$ and $b_{n+1} = b_n + b_{n-1} + (-1)^{n+1} p_n(0)/(2n)!$ for $n \ge 1$. Write $F_m$
for the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every $n \ge 1$,

$$\pi^2 = \frac{1}{a_{n-1}} \Bigl(b_{n-1} + (-1)^n \sum_{k=0}^{\infty}
\frac{(k!)^2 \, p_n(k) \, F_{2k+2}}{(2k+2n)!}\Bigr)$$

and

$$\pi^2 = \frac{1}{a_n} \Bigl(b_n + (-1)^{n+1} \sum_{k=0}^{\infty}
\frac{(k!)^2 \, p_n(k) \, F_{2k+1}}{(2k+2n)!}\Bigr).$$

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Theorem 2.1 (`fq-2024-tonien10292023-thm-2.1`). -/
public theorem_wanted pi_sq_eq_fibonacci_factorial_series (p : ℕ → ℤ[X]) (hp1 : p 1 = 1)
    (hp : ∀ n, 1 ≤ n → p (n + 1) = (2 * X + C (2 * n + 1 : ℤ)) * (2 * X + C (2 * n + 2 : ℤ)) *
      p n - (X + 1) ^ 2 * (p n).comp (X + 1))
    (a : ℕ → ℝ) (ha0 : a 0 = -(8 * √5) / 250) (ha1 : a 1 = (25 - 4 * √5) / 250)
    (ha : ∀ n, 1 ≤ n → a (n + 1) = a n + a (n - 1))
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hb1 : b 1 = 0)
    (hb : ∀ n, 1 ≤ n → b (n + 1) =
      b n + b (n - 1) + (-1) ^ (n + 1) * (((p n).eval 0 : ℤ) : ℝ) / ((2 * n).factorial : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    Real.pi ^ 2 = (b (n - 1) + (-1) ^ n * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (((p n).eval (k : ℤ) : ℤ) : ℝ) * (Nat.fib (2 * k + 2) : ℝ) /
          ((2 * k + 2 * n).factorial : ℝ)) / a (n - 1) ∧
      Real.pi ^ 2 = (b n + (-1) ^ (n + 1) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (((p n).eval (k : ℤ) : ℤ) : ℝ) * (Nat.fib (2 * k + 1) : ℝ) /
          ((2 * k + 2 * n).factorial : ℝ)) / a n

/-- **Two Fibonacci series for $\pi^2$.** Writing $F_m$ for the Fibonacci numbers ($F_0 = 0$,
$F_1 = 1$),

$$\pi^2 = \frac{250}{8\sqrt{5}} \sum_{k=0}^{\infty} \frac{(k!)^2 \, F_{2k+2}}{(2k+2)!}
\quad \text{and} \quad
\pi^2 = \frac{250}{25 - 4\sqrt{5}} \sum_{k=0}^{\infty} \frac{(k!)^2 \, F_{2k+1}}{(2k+2)!}.$$

These are identities (2.3) and (2.4) of the paper, the case $n = 1$ of its Theorem 2.1.

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Lemma 2.2 (`fq-2024-tonien10292023-lem-2.2`). -/
public theorem_wanted pi_sq_eq_fibonacci_central_series :
    Real.pi ^ 2 = 250 / (8 * √5) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (Nat.fib (2 * k + 2) : ℝ) / ((2 * k + 2).factorial : ℝ) ∧
      Real.pi ^ 2 = 250 / (25 - 4 * √5) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (Nat.fib (2 * k + 1) : ℝ) / ((2 * k + 2).factorial : ℝ)

end

end MetaMathlibExt
