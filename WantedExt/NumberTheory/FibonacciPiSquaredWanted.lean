/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.FibonacciFactorialSeries

/-!
# Fibonacci numbers and `π²`

Statements from Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024),
no. 1 (paper `tonien10292023`), read from the extracted text layer (the primary PDF is not
reachable for agents). The second identity is the continuation line `= …` of the aligned display
that starts with `π² =`; the text layer drops the repeated left side.
-/

namespace MetaMathlibExt

@[expose] public section

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
