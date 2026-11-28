/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Choose.Central
public import MathlibExt.Combinatorics.Enumerative.GeneralizedCentralBinomialArcsin
public import MathlibExt.Combinatorics.Enumerative.GeneralizedCentralBinomialArcsinSeries

/-!
# Power series with reciprocals of central binomial coefficients via `arcsin`

Statements from Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central
Binomial Coefficients*, INTEGERS 26 (2026), Article A2.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- **Zurita's series $\sum_{k > n} 4^k x^k / ((k - n)^2\binom{2k}{k})$.** For $j \ge 1$ write
Zurita's polynomials as $S_j(x) = \sum_{k=0}^{j} s^{(j)}_k x^k$,
$T_{j-2}(x) = \sum_{k=0}^{j-2} t^{(j)}_k x^k$ and $M_{j-1}(x) = \sum_{k=0}^{j-1} m^{(j)}_k x^k$.
Let $n \ge 1$, let $x$ be real with $0 < x < 1$, and put
$$
r_k = \frac{t^{(n)}_{k-1}}{k - n} +
\frac{1}{2(k - n)} \sum_{l=0}^{k-1} s^{(n)}_l\, m^{(n-l)}_{k-l-1} +
\frac{4^k}{(k - n)^2} \Bigl(4^{-k} - \frac{1}{\binom{2k}{k}}\Bigr)
$$
for $1 \le k \le n - 1$ and
$$
q = -\frac{2^{2n+1}}{\binom{2n}{n}} + \sum_{l=0}^{n-2} s^{(n)}_l \Bigl(
\frac{4^{n-l}}{(n - l)\binom{2(n-l)}{n-l}} -
\frac12 \sum_{p=1}^{n-l-1} \frac{4^p\, m^{(n-l)}_{n-l-1-p}}{p(2p + 1)\binom{2p}{p}}\Bigr).
$$
Then
$$
\sum_{k > n} \frac{4^k x^k}{(k - n)^2 \binom{2k}{k}} =
\frac{2^{2n+1} x^n}{\binom{2n}{n}} \arcsin(\sqrt{x})^2 -
\arcsin(\sqrt{x}) \sqrt{x(1 - x)} \sum_{k=0}^{n-1} s^{(n)}_k M_{n-k-1}(x)\, x^k +
\sum_{k=1}^{n-1} r_k x^k + q x^n.
$$

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Corollary 2 (`integers-2026-A2-cor-2`). -/
public theorem_wanted tsum_four_pow_div_sub_sq_mul_centralBinom {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    let r : ℕ → ℝ := fun k =>
      ((zuritaTCoeff n (k - 1) : ℝ) / ((k : ℝ) - n) +
          1 / 2 * ∑ l ∈ range k, (zuritaSCoeff n l * zuritaMCoeff (n - l) (k - l - 1) : ℝ) /
            ((k : ℝ) - n)) +
        (4 : ℝ) ^ k / ((k : ℝ) - n) ^ 2 * (1 / (4 : ℝ) ^ k - 1 / Nat.centralBinom k)
    let q : ℝ := -(2 : ℝ) ^ (2 * n + 1) / Nat.centralBinom n +
      ∑ l ∈ range (n - 1), (zuritaSCoeff n l : ℝ) *
        ((4 : ℝ) ^ (n - l) / (((n - l : ℕ) : ℝ) * Nat.centralBinom (n - l)) -
          1 / 2 * ∑ p ∈ Icc 1 (n - l - 1),
            (4 : ℝ) ^ p * (zuritaMCoeff (n - l) (n - l - 1 - p) : ℝ) /
              ((p : ℝ) * (2 * p + 1) * Nat.centralBinom p))
    ∑' k : ℕ, (4 : ℝ) ^ (k + n + 1) * x ^ (k + n + 1) /
        (((k : ℝ) + 1) ^ 2 * Nat.centralBinom (k + n + 1)) =
      (2 : ℝ) ^ (2 * n + 1) * x ^ n / Nat.centralBinom n * Real.arcsin (Real.sqrt x) ^ 2 -
        Real.arcsin (Real.sqrt x) * Real.sqrt (x * (1 - x)) *
          ∑ k ∈ range n, (zuritaSCoeff n k : ℝ) * zuritaM (n - k) x * x ^ k +
        ∑ k ∈ Icc 1 (n - 1), r k * x ^ k + q * x ^ n

end

end MetaMathlibExt
