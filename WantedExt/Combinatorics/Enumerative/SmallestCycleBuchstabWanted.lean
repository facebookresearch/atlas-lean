/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Data.Fintype.Perm

/-!
# Gravel–Panario, smallest cycles and the (generalized) Buchstab function — wishlist

Statement-only records for Gravel and Panario, INTEGERS 24 (2024), Article A7
(source: arXiv:2212.12847v2 TeX). `X_n` is the length of the smallest cycle of
a uniformly random permutation of `Fin n`, written as
`⨅ x, Function.minimalPeriod σ x` (the cycle through `x` has length
`minimalPeriod σ x`); moments are averages over `Equiv.Perm (Fin n)`.

The Buchstab function `ω` and the generalized Buchstab function `Ω_K` enter as
hypotheses: any `ω : ℝ → ℝ` with `ω x = 1/x` on `[1, 2]` and
`x ω(x) = 1 + ∫_1^{x-1} ω` for `x ≥ 2` (the integrated form of
`(x ω(x))' = ω(x - 1)`), and any `Ω` with `Ω = 1` on `[1, 2)` and
`Ω(x) = 1 + K ∫_2^x Ω(u - 1)/(u - 1) du` for `x ≥ 2`. Both systems determine the
function on `[1, ∞)` interval by interval.
-/

open Real

namespace MetaMathlibExt

@[expose] public section

/-- **Mean length of the smallest cycle of a random permutation.** For $n \ge 1$ let $X_n$ be the
length of the smallest cycle of a uniformly random permutation of $\{1, \dots, n\}$. Then
$\mathbb{E}(X_n) / (e^{-\gamma} \log n) \to 1$ as $n \to \infty$, where $\gamma$ is the
Euler–Mascheroni constant.

The paper states this as $\mathbb{E}(X_n) = e^{-\gamma} \log n \, (1 + O(h(n)/\log n))$ for some
$h(n) = o(\log n)$, which is equivalent.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 1
(`integers-2024-A7-thm-1`). -/
public theorem_wanted smallest_cycle_mean_asymp :
    Filter.Tendsto (fun n : ℕ =>
      ((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ)) /
          (n.factorial : ℝ)) / (Real.exp (-eulerMascheroniConstant) * Real.log n))
      Filter.atTop (nhds 1)

/-- **Higher moments of the smallest cycle length.** Let $\omega$ be a real function with
$\omega(x) = 1/x$ for $1 \le x \le 2$ and $x\,\omega(x) = 1 + \int_1^{x-1} \omega(t)\,dt$ for
$x \ge 2$, and for $n \ge 1$ let $X_n$ be the length of the smallest cycle of a uniformly random
permutation of $\{1, \dots, n\}$. For every integer $\ell \ge 2$ there are real constants
$\varepsilon > 0$ and $C$ such that for every $n \ge 1$

$$\left| \mathbb{E}(X_n^\ell) - \ell\, n^{\ell-1} \int_1^\infty \frac{\omega(x)}{x^\ell}\,dx \right|
\le C\, n^{\ell-1} n^{-\varepsilon}.$$

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 1
(`integers-2024-A7-thm-1`). -/
public theorem_wanted smallest_cycle_moment_asymp (ω : ℝ → ℝ)
    (hω₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
    (hω₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 ≤ n →
      |(∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ) ^ ℓ) /
            (n.factorial : ℝ) -
          ℓ * (n : ℝ) ^ (ℓ - 1) * ∫ x in Set.Ioi (1 : ℝ), ω x / x ^ ℓ|
        ≤ C * (n : ℝ) ^ (ℓ - 1) * (n : ℝ) ^ (-ε)

/-- **Variance of the smallest cycle length.** Let $\omega$ be a real function with
$\omega(x) = 1/x$ for $1 \le x \le 2$ and $x\,\omega(x) = 1 + \int_1^{x-1} \omega(t)\,dt$ for
$x \ge 2$, and for $n \ge 1$ let $X_n$ be the length of the smallest cycle of a uniformly random
permutation of $\{1, \dots, n\}$. There are real constants $\varepsilon > 0$ and $C$ such that for
every $n \ge 1$

$$\left| \operatorname{Var}(X_n) - 2n \int_1^\infty \frac{\omega(x)}{x^2}\,dx \right|
\le C\, n \cdot n^{-\varepsilon}.$$

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 2
(`integers-2024-A7-thm-2`). -/
public theorem_wanted smallest_cycle_variance_asymp (ω : ℝ → ℝ)
    (hω₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
    (hω₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 ≤ n →
      |((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ) ^ 2) /
            (n.factorial : ℝ) -
          ((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ)) /
            (n.factorial : ℝ)) ^ 2) -
          n * (2 * ∫ x in Set.Ioi (1 : ℝ), ω x / x ^ 2)|
        ≤ C * (n : ℝ) * (n : ℝ) ^ (-ε)

/-- **Recursion for the Taylor coefficients of the Buchstab function.** Let $\omega$ be a real
function with $\omega(x) = 1/x$ for $1 \le x \le 2$ and
$x\,\omega(x) = 1 + \int_1^{x-1} \omega(t)\,dt$ for $x \ge 2$, and let $c_{n,i}$ ($n, i \ge 0$)
be real numbers such that for every integer $n \ge 1$ and every real $z$ with $-1 \le z < 1$ the
series $\sum_{i \ge 0} c_{n,i} z^i$ converges absolutely to $\omega(n + (1+z)/2)$. Then
$c_{1,i} = \frac{2}{3} \left(-\frac{1}{3}\right)^i$ for every $i \ge 0$, and for every $n \ge 1$

$$c_{n+1,0} = \frac{1}{2n+3} \sum_{i \ge 0} c_{n,i} \left(2(n+1) + \frac{(-1)^i}{i+1}\right)$$

and, for every $i \ge 1$,

$$c_{n+1,i} = \frac{1}{2n+3} \left(\frac{c_{n,i-1}}{i} - c_{n+1,i-1}\right).$$

The printed statement of Theorem 3 has $c_{n,i}/n$ in place of $c_{n,i-1}/i$; the recursion above
is the identity $(2n+3) c_{n+1,i} + c_{n+1,i-1} = c_{n,i-1}/i$ derived in the paper's proof.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 3
(`integers-2024-A7-thm-3`). -/
public theorem_wanted buchstab_taylor_coeff_recursion (ω : ℝ → ℝ)
    (hω₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
    (hω₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t)
    (c : ℕ → ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Set.Ico (-1 : ℝ) 1,
      HasSum (fun i => c n i * z ^ i) (ω (n + (1 + z) / 2))) :
    (∀ i, c 1 i = 2 / 3 * (-1 / 3 : ℝ) ^ i) ∧
      (∀ n : ℕ, 1 ≤ n → c (n + 1) 0 =
        (∑' i, c n i * (2 * ((n : ℝ) + 1) + (-1 : ℝ) ^ i / ((i : ℝ) + 1))) /
          (2 * (n : ℝ) + 3)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, 1 ≤ i →
        c (n + 1) i = (c n (i - 1) / i - c (n + 1) (i - 1)) / (2 * (n : ℝ) + 3))

/-- **Recursion for the Taylor coefficients of the generalized Buchstab function.** Let $K > 0$,
let $\Omega$ be a real function with $\Omega(x) = 1$ for $1 \le x < 2$ and
$\Omega(x) = 1 + K \int_2^x \frac{\Omega(u-1)}{u-1}\,du$ for $x \ge 2$, and let $c_{n,i}$
($n, i \ge 0$) be real numbers such that for every integer $n \ge 1$ and every real $z$ with
$-1 \le z < 1$ the series $\sum_{i \ge 0} c_{n,i} z^i$ converges absolutely to
$\Omega(n + (1+z)/2)$. Then $c_{1,0} = 1$, $c_{1,i} = 0$ for every $i \ge 1$,

$$c_{2,0} = 1 + K \sum_{i \ge 0} \frac{(-1)^i}{(i+1)\,2^{i+1}},$$

$$c_{2,i} = K \sum_{j \ge 0} \frac{(-1)^{j+i-1} \binom{j+i}{i}}{(j+i)\,2^{j+i}} \quad (i \ge 1),$$

and for every $n \ge 3$, writing
$\alpha_{n,m} = \sum_{j=0}^{m} \frac{(-1)^{m-j}}{(2n-1)^{m-j}}\, c_{n-1,j}$ for $m \ge 0$,

$$c_{n,0} = \sum_{i \ge 0} c_{n-1,i} -
\frac{K}{2n-1} \sum_{i \ge 0} \frac{(-1)^{i+1} \alpha_{n,i}}{i+1}$$

and $c_{n,i} = \dfrac{K\, \alpha_{n,i-1}}{(2n-1)\, i}$ for every $i \ge 1$.

Here $c_{2,0} = 1 + K \log(3/2)$. The printed statement of Theorem 4 has
$c_{2,0} = 1 + K \sum_{i \ge 1} 1/(i\, 2^i)$, which omits the sign $(-1)^{i-1}$.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 4
(`integers-2024-A7-thm-4`). -/
public theorem_wanted generalized_buchstab_taylor_coeff_recursion (K : ℝ) (hK : 0 < K)
    (Ω : ℝ → ℝ) (hΩ₁ : ∀ x ∈ Set.Ico (1 : ℝ) 2, Ω x = 1)
    (hΩ₂ : ∀ x : ℝ, 2 ≤ x → Ω x = 1 + K * ∫ u in (2 : ℝ)..x, Ω (u - 1) / (u - 1))
    (c : ℕ → ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Set.Ico (-1 : ℝ) 1,
      HasSum (fun i => c n i * z ^ i) (Ω (n + (1 + z) / 2))) :
    c 1 0 = 1 ∧ (∀ i : ℕ, 1 ≤ i → c 1 i = 0) ∧
      c 2 0 = 1 + K * ∑' i : ℕ, (-1 : ℝ) ^ i / (((i : ℝ) + 1) * 2 ^ (i + 1)) ∧
      (∀ i : ℕ, 1 ≤ i → c 2 i =
        K * ∑' j : ℕ, (-1 : ℝ) ^ (j + i - 1) * ((j + i).choose i : ℝ) /
          (((j : ℝ) + i) * 2 ^ (j + i))) ∧
      (∀ n : ℕ, 3 ≤ n → c n 0 = ∑' i, c (n - 1) i -
        K / (2 * (n : ℝ) - 1) * ∑' i : ℕ, (-1 : ℝ) ^ (i + 1) *
          (∑ j ∈ Finset.range (i + 1),
            (-1 : ℝ) ^ (i - j) / (2 * (n : ℝ) - 1) ^ (i - j) * c (n - 1) j) / ((i : ℝ) + 1)) ∧
      (∀ n : ℕ, 3 ≤ n → ∀ i : ℕ, 1 ≤ i → c n i =
        K * (∑ j ∈ Finset.range i,
            (-1 : ℝ) ^ (i - 1 - j) / (2 * (n : ℝ) - 1) ^ (i - 1 - j) * c (n - 1) j) /
          ((2 * (n : ℝ) - 1) * i))

end

end MetaMathlibExt
