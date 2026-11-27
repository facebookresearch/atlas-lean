/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.List.GetD
public import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadterLinearDies
public import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadterSevenCycle
public import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadterSixteenCycleTwo
public import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadterTwoCycle

namespace MetaMathlibExt

@[expose] public section

/-- **Period-seven pattern of the padded sequence from $1, \dots, N$.** Let $N \ge 72$ be a
natural number, and let $B$ be the sequence with $B(n) = 0$ for $n \le 0$ and $B(i) = i$ for
$1 \le i \le N$, continued by the recurrence $B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$.
Let $\nu = -1, -2, -2, -2, 2, 1, 0$ according as $N \equiv 0, 1, 2, 3, 4, 5, 6 \pmod 7$. Then
for all natural numbers $k \ge 1$ and $r < 7$ with $N + 67 \le N + 7k + r \le 2N + \nu$, the
term $B(N + 7k + r)$ can be computed, and it equals $7k + 2$, $N + 7k + 2$, $N + 7k + 4$, $7$,
$2N + 2k + 45$, $2N + k - 7$ or $N - 2$ according as $r = 0, 1, 2, 3, 4, 5$ or $6$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 2
(`jis-2024-24.7.4-thm-2`). -/
public theorem_wanted threeTermHofstadter_padded_linear_period_seven {N : ℕ} (hN : 72 ≤ N)
    (k r : ℕ) (hk : 1 ≤ k) (hr : r < 7) (hlo : N + 67 ≤ N + 7 * k + r)
    (hhi : ((N + 7 * k + r : ℕ) : ℤ) ≤ 2 * N + [-1, -2, -2, -2, 2, 1, 0].getD (N % 7) 0) :
    threeTermHofstadterTerm true ((List.range N).map fun i : ℕ => (i : ℤ) + 1) (N + 7 * k + r) =
      some ([7 * k + 2, N + 7 * k + 2, N + 7 * k + 4, 7, 2 * N + 2 * k + 45, 2 * N + k - 7,
        N - 2].getD r 0 : ℤ)

/-- **Length of the padded sequence from $1, \dots, N$.** Let $N$ be a natural number, and let
$t = 196, 2087, 3201, 4315, 200, 32478, 118$ and $e = 27, 254, 524, 560, 20, 4547, 9$
according as $N \equiv 0, 1, 2, 3, 4, 5, 6 \pmod 7$. Let $B$ be the sequence with $B(n) = 0$
for $n \le 0$ and $B(i) = i$ for $1 \le i \le N$, continued by the recurrence
$B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$. If $N \ge t$, then $B$ ends after
exactly $2N + e$ terms: $B(1), \dots, B(2N + e)$ can be computed and $B(2N + e + 1)$ cannot,
because the recurrence refers to an index not yet computed.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 2
(`jis-2024-24.7.4-thm-2`). -/
public theorem_wanted threeTermHofstadter_padded_linear_endsAfter {N : ℕ}
    (hN : [196, 2087, 3201, 4315, 200, 32478, 118].getD (N % 7) 0 ≤ N) :
    ThreeTermHofstadterEndsAfter true ((List.range N).map fun i : ℕ => (i : ℤ) + 1)
      (2 * N + [27, 254, 524, 560, 20, 4547, 9].getD (N % 7) 0)

/-- **Five-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K \ge 3$ be a
natural number, $\mu \ge 1$ an integer, and $a_4, \dots, a_K$ arbitrary integers. Let $B$ be
the sequence given by $B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$, padded with
$B(n) = 0$ for $n \le 0$, with initial conditions
$1, 2, 3, a_4, \dots, a_K, K + \mu, 3, K + 3, K + \mu + 1, 5$ at the indices $1, \dots, K + 5$.
Then for all natural numbers $k$ and $r < 5$ with
$K + 1 \le K + 5k + r \le K + \lfloor (5\mu - 15)/2 \rfloor$, the term $B(K + 5k + r)$ can be
computed, and it equals $5$, $K + 3k + \mu$, $3$, $K + 5k + 3$ or $K + 3k + \mu + 1$ according
as $r = 0, 1, 2, 3$ or $4$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 5,
citing the author's thesis, Proposition 9.10 (`jis-2024-24.7.4-lem-5`). -/
public theorem_wanted threeTermHofstadter_fiveCycle {K : ℕ} (hK : 3 ≤ K) {mu : ℤ} (hmu : 1 ≤ mu)
    (a : List ℤ) (ha : a.length = K - 3) (k r : ℕ) (hr : r < 5) (hlo : K + 1 ≤ K + 5 * k + r)
    (hhi : ((K + 5 * k + r : ℕ) : ℤ) ≤ K + (5 * mu - 15) / 2) :
    threeTermHofstadterTerm true ([1, 2, 3] ++ a ++ [K + mu, 3, K + 3, K + mu + 1, 5])
        (K + 5 * k + r) =
      some ([5, K + 3 * k + mu, 3, K + 5 * k + 3, K + 3 * k + mu + 1].getD r 0 : ℤ)

/-- **First sixteen-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K \ge 1$ be
a natural number and let $\lambda$, $\mu_1$, $\mu_2$, $\gamma$ be integers with $\lambda > 31 + K$
and $\mu_1, \mu_2, \gamma > \lambda$. Let $a_1, \dots, a_K$ be arbitrary integers and let $B$ be
the padded three-term Hofstadter-like sequence with initial conditions
$a_1, \dots, a_K, \lambda, 7, \mu_2, 16, \mu_2, 16, \mu_1, \lambda, 7, \mu_2, 16, 2\mu_2, 16,
\mu_2, 25, \gamma, \lambda, 7$. Then for all natural numbers $k$ and $r \le 15$ with
$K + 1 \le K + 16k + r \le \lambda$, the term $B(K + 16k + r)$ is defined, and these terms are
$B(K + 16k) = \mu_1 2^{k-1} + \gamma - \mu_1$, $B(K + 16k + 1) = \lambda$, $B(K + 16k + 2) = 7$,
$B(K + 16k + 3) = \mu_2 2^k$, $B(K + 16k + 4) = 16$, $B(K + 16k + 5) = \mu_2 2^k$,
$B(K + 16k + 6) = 16$, $B(K + 16k + 7) = \mu_1 2^k$, $B(K + 16k + 8) = \lambda$,
$B(K + 16k + 9) = 7$, $B(K + 16k + 10) = \mu_2 2^k$, $B(K + 16k + 11) = 16$,
$B(K + 16k + 12) = \mu_2 2^{k+1}$, $B(K + 16k + 13) = 16$, $B(K + 16k + 14) = \mu_2 2^k$ and
$B(K + 16k + 15) = 25$.

Corrected: the paper prints $B(K + 16k + 12) = \mu_2 2^k$, which contradicts its own initial
value $B(K + 12) = 2\mu_2$; the exponent $k + 1$ matches the initial conditions and every later
term.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 6,
citing the author's thesis, Proposition 9.13 (`jis-2024-24.7.4-lem-6`). -/
public theorem_wanted threeTermHofstadter_sixteenCycle_one {K : ℕ} (hK : 1 ≤ K)
    {lam mu₁ mu₂ ga : ℤ} (hlam : 31 + (K : ℤ) < lam) (hmu₁ : lam < mu₁) (hmu₂ : lam < mu₂)
    (hga : lam < ga) (a : List ℤ) (ha : a.length = K) (k r : ℕ) (hr : r < 16)
    (hlo : K + 1 ≤ K + 16 * k + r) (hhi : ((K + 16 * k + r : ℕ) : ℤ) ≤ lam) :
    threeTermHofstadterTerm true
        (a ++ [lam, 7, mu₂, 16, mu₂, 16, mu₁, lam, 7, mu₂, 16, 2 * mu₂, 16, mu₂, 25, ga, lam, 7])
        (K + 16 * k + r) =
      some ([mu₁ * 2 ^ (k - 1) + ga - mu₁, lam, 7, mu₂ * 2 ^ k, 16, mu₂ * 2 ^ k, 16,
        mu₁ * 2 ^ k, lam, 7, mu₂ * 2 ^ k, 16, mu₂ * 2 ^ (k + 1), 16, mu₂ * 2 ^ k, 25].getD r 0)

end

end MetaMathlibExt
