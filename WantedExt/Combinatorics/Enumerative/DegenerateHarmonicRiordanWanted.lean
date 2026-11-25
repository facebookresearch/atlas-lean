/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.DegenerateHarmonicRiordan

namespace MetaMathlibExt

@[expose] public section

/-- **Alternating and binomial sums of degenerate hyperharmonic numbers.** Let $\lambda > 0$ and
$\alpha > 0$ be real numbers and let $n$ be a natural number. Write $H_{m,\lambda}(\alpha)$ for the
generalized degenerate harmonic numbers, $H^s_{m,\lambda}(\alpha)$ for the generalized degenerate
hyperharmonic numbers of order $s$, and $D_{n,\lambda}$ for the degenerate Daehee numbers. Then
$$
\sum_{k=0}^{n} (-1)^k H^{k+1}_{n-k+1,\lambda}(\alpha) =
\frac{(-1)^n D_{n,\lambda}}{\alpha^{n+1}\, n!},
$$
and for every natural number $r$,
$$
\sum_{k=0}^{n} \binom{k+r}{r} H_{n-k+1,\lambda}(\alpha) = H^{r+2}_{n+1,\lambda}(\alpha).
$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 1
(`integers-2024-A41-thm-1`). -/
public theorem_wanted degenerateHyperharmonic_alternating_and_binomial_sums {lam α : ℝ}
    (hlam : 0 < lam) (hα : 0 < α) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * generalizedDegenerateHyperharmonic lam α (k + 1) (n - k + 1) =
      (-1) ^ n * degenerateDaehee lam n / (α ^ (n + 1) * n.factorial) ∧
    ∀ r : ℕ, ∑ k ∈ Finset.range (n + 1),
        ((k + r).choose r : ℝ) * generalizedDegenerateHarmonic lam α (n - k + 1) =
      generalizedDegenerateHyperharmonic lam α (r + 2) (n + 1)

/-- **Alternating degenerate exponential sum of degenerate harmonic numbers of rank.** Let
$\lambda > 0$ and $\alpha > 0$ be real and let $n$ be a natural number. Write
$(1)_{k,\lambda} = 1 \cdot (1 - \lambda) \cdots (1 - (k-1)\lambda)$ for the generalized falling
factorial (so $(1)_{0,\lambda} = 1$), $H_\lambda(m, r, \alpha)$ for the generalized degenerate
harmonic numbers of rank $r$, and $H_{m,\lambda}(\alpha)$ for the generalized degenerate harmonic
numbers. Then
$$\sum_{k=0}^{n} (-1)^k \frac{(1)_{k,\lambda}}{k!} H_\lambda(n+1, k, \alpha) =
H_{n+1,\lambda}(\alpha) - \frac{H_{n,\lambda}(\alpha)}{\alpha}.$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 3
(`integers-2024-A41-thm-3`). -/
public theorem_wanted degenerateHarmonicRank_exp_weighted_sum {lam α : ℝ}
    (hlam : 0 < lam) (hα : 0 < α) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * generalizedFallingFactorial 1 lam k / k.factorial *
          degenerateHarmonicRank lam α (n + 1) k =
      generalizedDegenerateHarmonic lam α (n + 1) - generalizedDegenerateHarmonic lam α n / α

/-- **A binomial sum equal to a degenerate hyperharmonic number.** Let $\lambda > 0$ and
$\alpha > 0$ be real numbers and let $r \le n$ be natural numbers. Write
$\binom{\lambda}{j} = \lambda(\lambda - 1)\cdots(\lambda - j + 1)/j!$ and $H^s_{m,\lambda}(\alpha)$
for the generalized degenerate hyperharmonic numbers of order $s$. Then
$$
\sum_{k=r}^{n} (-1)^{n-k} \frac{\binom{\lambda}{n-k+1}}{\lambda\, \alpha^{n-k+1}} \binom{k}{r} =
H^{r+1}_{n-r+1,\lambda}(\alpha).
$$

The hypothesis $r \le n$ makes the summation range $r \le k \le n$ nonempty, as in the paper.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 6
(`integers-2024-A41-thm-6`). -/
public theorem_wanted degenerateHyperharmonic_eq_binomial_sum {lam α : ℝ}
    (hlam : 0 < lam) (hα : 0 < α) {n r : ℕ} (hrn : r ≤ n) :
    ∑ k ∈ Finset.Icc r n,
        (-1 : ℝ) ^ (n - k) * Ring.choose lam (n - k + 1) / (lam * α ^ (n - k + 1)) *
          (k.choose r : ℝ) =
      generalizedDegenerateHyperharmonic lam α (r + 1) (n - r + 1)

/-- **Degenerate harmonic numbers of rank and degenerate Stirling numbers of the first kind.** Let
$\lambda > 0$ and $\alpha > 0$ be real and let $n \ge 1$ be a natural number. Write
$(1)_{k,\lambda} = 1 \cdot (1 - \lambda) \cdots (1 - (k-1)\lambda)$ for the generalized falling
factorial, $H_\lambda(m, r, \alpha)$ for the generalized degenerate harmonic numbers of rank $r$,
and $S_{1,\lambda}(k, i)$ for the degenerate Stirling numbers of the first kind. Then
$$\sum_{k=1}^{n} \frac{(1)_{k,\lambda}}{k!} H_\lambda(n, k-1, \alpha) =
\sum_{k=1}^{n} \sum_{i=1}^{k} \frac{(-1)^{k+i} (1)_{i,\lambda} S_{1,\lambda}(k, i)}{\alpha^k k!}.$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 7
(`integers-2024-A41-thm-7`). -/
public theorem_wanted degenerateHarmonicRank_exp_sum_eq_stirlingFirst {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n,
        generalizedFallingFactorial 1 lam k / k.factorial * degenerateHarmonicRank lam α n (k - 1) =
      ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 k,
        (-1 : ℝ) ^ (k + i) * generalizedFallingFactorial 1 lam i * degenerateStirlingFirst lam k i /
          (α ^ k * k.factorial)

/-- **Degenerate Bernoulli and Euler sums of higher-rank degenerate harmonic numbers.** Let
$\lambda > 0$ and $\alpha > 0$ be real and let $n \ge 1$ be an integer. Write $\beta_{k,\lambda}$
and $\varepsilon_{k,\lambda}$ for the degenerate Bernoulli and Euler numbers,
$H_{m,\lambda}(\alpha)$ for the generalized degenerate harmonic numbers, and
$H_\lambda(m, r, \alpha)$ for the generalized degenerate harmonic numbers of rank $r$. Then
$\sum_{k=1}^{n} (-1)^k \beta_{k,\lambda} H_\lambda(n, k - 1, \alpha) / k! =
\alpha H_{n+1,\lambda}(\alpha) - 1$, and if moreover $\alpha \ne 1/2$, then
$\sum_{k=1}^{n} (-1)^{k+1} \varepsilon_{k,\lambda} H_\lambda(n, k - 1, \alpha) / k! =
((2\alpha)^{-n} - 1) / (2\alpha - 1)$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 8
(`integers-2024-A41-thm-8`). -/
public theorem_wanted degenerateHarmonicRank_bernoulli_euler_sums {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ k * degenerateBernoulli lam k * degenerateHarmonicRank lam α n (k - 1) /
          k.factorial =
      α * generalizedDegenerateHarmonic lam α (n + 1) - 1 ∧
    (α ≠ 1 / 2 →
      ∑ k ∈ Finset.Icc 1 n,
          (-1 : ℝ) ^ (k + 1) * degenerateEuler lam k / k.factorial *
            degenerateHarmonicRank lam α n (k - 1) =
        (((2 * α) ^ n)⁻¹ - 1) / (2 * α - 1))

/-- **Degenerate harmonic numbers of rank and degenerate Stirling numbers of the second kind.**
Let $\lambda > 0$ and $\alpha > 0$ be real and let $m$ and $n$ be natural numbers with
$1 \le m \le n$. Write $S_{2,\lambda}(k, m)$ for the degenerate Stirling numbers of the second kind
and $H_\lambda(n, r, \alpha)$ for the generalized degenerate harmonic numbers of rank $r$. Then
$$\sum_{k=m}^{n} \frac{(-1)^k S_{2,\lambda}(k, m) H_\lambda(n, k-1, \alpha)}{k!} =
\frac{(-1)^m}{m! \, \alpha^m}.$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 9
(`integers-2024-A41-thm-9`). -/
public theorem_wanted degenerateHarmonicRank_stirlingSecond_sum {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Finset.Icc m n,
        (-1 : ℝ) ^ k * degenerateStirlingSecond lam k m * degenerateHarmonicRank lam α n (k - 1) /
          k.factorial =
      (-1) ^ m / (m.factorial * α ^ m)

end

end MetaMathlibExt
