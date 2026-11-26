/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.Digits.KaprekarPrimeBase
public import MathlibExt.NumberTheory.Digits.KaprekarTwoMaximalCycles

/-!
# Four-digit Kaprekar dynamics in odd bases (Chen, Ono, Schwartz, Thakur)

Cycle-length and cycle-count statements from E. Chen, K. Ono, R. E. Schwartz and
D. Thakur, *Four-Digit Kaprekar Dynamics in Odd Bases*, Journal of Integer Sequences
29 (2026), Article 26.4.7. The difference-coordinate map, state space and maximal
period criterion are in `MathlibExt/NumberTheory/Digits/KaprekarMaximalPeriod.lean`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of Kaprekar cycles of maximal length.** Let $B > 3$ be odd, let $K_B$ be the
four-digit Kaprekar map and $X_B$ its state space, and put $q = (B - 1)/2$. If some point of
$X_B$ has minimal period $q$ under $K_B$, then exactly $q \lfloor (q - 1)/2 \rfloor$ points of
$X_B$ have minimal period $q$ under $K_B$.

Equivalently, $K_B$ then has exactly $\lfloor (q - 1)/2 \rfloor$ terminal cycles of length $q$
on $X_B$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 5 (`jis-2026-26.4.7-cor-5`). -/
public theorem_wanted kaprekar_card_maximal_cycles (B : ℕ) (hB : Odd B) (hB3 : 3 < B)
    (heq : ∃ d ∈ kaprekarFourDigitStates B,
      Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2) :
    ((kaprekarFourDigitStates B).filter fun d =>
        Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2).card =
      (B - 1) / 2 * (((B - 1) / 2 - 1) / 2)

/-- **Explicit count of Kaprekar cycles of each length.** Let $B > 3$ be odd and $L \ge 1$, let
$K_B$ be the four-digit Kaprekar map and $X_B$ its state space, let $\varphi$ be Euler's totient
function, and let $\lambda(n)$ denote the projective order of $2$ modulo $n$. For $a \ge 1$ put
$$\mu_B(a) = \sum_{n \mid B,\ n > 1,\ \lambda(n) = a}
\left\lfloor \frac{\varphi(n)}{2a} \right\rfloor$$
and
$$N_B(L) = \mu_B(L) \left\lfloor \frac{L - 1}{2} \right\rfloor + \mu_B(2L) +
\binom{\mu_B(L)}{2} L + \sum_{a, b \mid L,\ a < b,\ \operatorname{lcm}(a, b) = L}
\mu_B(a)\, \mu_B(b) \gcd(a, b),$$
where $n$ ranges over positive divisors of $B$ and $a, b$ in the last sum range over positive
divisors of $L$. Then exactly $L \cdot N_B(L)$ points of $X_B$ have minimal period $L$ under
$K_B$.

Here $N_B(L)$ is the number of terminal cycles of length $L$ of $K_B$ on $X_B$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Theorem 24, with `μ_B` from display (14) (`jis-2026-26.4.7-thm-24`). -/
public theorem_wanted kaprekar_card_minimalPeriod_eq (B : ℕ) (hB : Odd B) (hB3 : 3 < B)
    (L : ℕ) (hL : 0 < L) :
    let μ : ℕ → ℕ := fun a =>
      ∑ n ∈ B.divisors with 1 < n ∧ projectiveOrderTwo n = a, n.totient / (2 * a)
    ((kaprekarFourDigitStates B).filter fun d =>
        Function.minimalPeriod (kaprekarFourDigitStep B) d = L).card =
      L * (μ L * ((L - 1) / 2) + μ (2 * L) + (μ L).choose 2 * L +
        ∑ p ∈ (L.divisors ×ˢ L.divisors).filter (fun p => p.1 < p.2 ∧ Nat.lcm p.1 p.2 = L),
          μ p.1 * μ p.2 * Nat.gcd p.1 p.2)

/-- **Odd bases with a unique Kaprekar cycle.** Let $B \ge 3$ be odd, let $K_B$ be the
four-digit Kaprekar map and $X_B$ its state space. There is a point $c \in X_B$, periodic for
$K_B$, whose forward orbit $\{K_B^k(c) : k \ge 0\}$ contains every point of $X_B$ that is
periodic for $K_B$, if and only if $B \in \{3, 5, 7\}$.

That is, $K_B$ has a unique terminal cycle on $X_B$ exactly when $B$ is $3$, $5$ or $7$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 27 (ii) (`jis-2026-26.4.7-cor-27`). -/
public theorem_wanted kaprekar_unique_cycle_iff (B : ℕ) (hB : Odd B) (hB3 : 3 ≤ B) :
    (∃ c ∈ kaprekarFourDigitStates B, c ∈ Function.periodicPts (kaprekarFourDigitStep B) ∧
      ∀ d ∈ kaprekarFourDigitStates B, d ∈ Function.periodicPts (kaprekarFourDigitStep B) →
        ∃ k, (kaprekarFourDigitStep B)^[k] c = d) ↔
      B = 3 ∨ B = 5 ∨ B = 7

end

end MetaMathlibExt
