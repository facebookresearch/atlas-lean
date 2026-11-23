/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.NumberTheory.OppermannCyclicNumbers

/-!
# Cyclic numbers: counting function, moments and gaps

Statements from John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25
(2025), Article A23.

A positive integer `n` is cyclic when `gcd(n, φ(n)) = 1` (`MetaMathlibExt.IsCyclicNumber`).
The `n`-th cyclic number `c_n` (`c_1 = 1`) is `Nat.nth IsCyclicNumber (n - 1)`; `A(x)` counts
the cyclic numbers `≤ x` and `cc(x)` the composite cyclic numbers `≤ x`.  The `k`-th moment of
`c_1, …, c_n` is `μ'(c,n,k) = n⁻¹ (c_1^k + ⋯ + c_n^k)`, the mean is `m(c,n) = μ'(c,n,1)`, and
the variance is `v(c,n) = (n-1)⁻¹ ∑ (c_i - m(c,n))²`.
-/

open Asymptotics Filter Topology

namespace MetaMathlibExt

@[expose] public section

open Classical in
/-- **Asymptotic count of cyclic and composite cyclic numbers.** For real $x$, let $A(x)$ be the
number of cyclic numbers $m$ with $1 \le m \le x$, and let $cc(x)$ be the number of composite
cyclic numbers $m \le x$, that is, cyclic numbers $m > 1$ that are not prime. Then, as
$x \to \infty$, $A(x) \sim cc(x)$ and $cc(x) \sim x e^{-\gamma} / \log \log \log x$, where
$\gamma$ is the Euler–Mascheroni constant.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Lemma 1 (`integers-2025-A23-lem-1`). -/
public theorem_wanted cyclicCount_isEquivalent_compositeCyclicCount :
    let A : ℝ → ℝ := fun x => (((Finset.Icc 1 ⌊x⌋₊).filter IsCyclicNumber).card : ℝ)
    let cc : ℝ → ℝ := fun x =>
      (((Finset.Icc 1 ⌊x⌋₊).filter fun m => IsCyclicNumber m ∧ 1 < m ∧ ¬m.Prime).card : ℝ)
    IsEquivalent atTop A cc ∧
      IsEquivalent atTop cc (fun x => x * Real.exp (-Real.eulerMascheroniConstant) /
        Real.log (Real.log (Real.log x)))

open Classical in
/-- **The cyclic counting functions vary regularly with index one.** For real $x$, let $A(x)$ be
the number of cyclic numbers $m$ with $1 \le m \le x$, let $\pi(x)$ be the number of primes
$p \le x$, and let $cc(x)$ be the number of composite cyclic numbers $m \le x$, that is, cyclic
numbers $m > 1$ that are not prime. Then for every real $\lambda > 0$, each of
$A(\lambda x) / A(x)$, $\pi(\lambda x) / \pi(x)$ and $cc(\lambda x) / cc(x)$ tends to $\lambda$
as $x \to \infty$.

Every prime is cyclic, so $\pi(x)$ is also the number of prime cyclic numbers $\le x$.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 1 (`integers-2025-A23-thm-1`). -/
public theorem_wanted cyclicCountingFunctions_regularlyVarying_index_one :
    let A : ℝ → ℝ := fun x => (((Finset.Icc 1 ⌊x⌋₊).filter IsCyclicNumber).card : ℝ)
    let piFun : ℝ → ℝ := fun x => (Nat.primeCounting ⌊x⌋₊ : ℝ)
    let cc : ℝ → ℝ := fun x =>
      (((Finset.Icc 1 ⌊x⌋₊).filter fun m => IsCyclicNumber m ∧ 1 < m ∧ ¬m.Prime).card : ℝ)
    ∀ lam : ℝ, 0 < lam →
      Tendsto (fun x => A (lam * x) / A x) atTop (𝓝 lam) ∧
      Tendsto (fun x => piFun (lam * x) / piFun x) atTop (𝓝 lam) ∧
      Tendsto (fun x => cc (lam * x) / cc x) atTop (𝓝 lam)

/-- **Taylor's law for cyclic numbers.** Let $c_1 < c_2 < \cdots$ be the cyclic numbers in
increasing order, so $c_1 = 1$. For $n \ge 1$ let $m(c,n) = \frac{1}{n} \sum_{i=1}^{n} c_i$ be
the mean of $c_1, \dots, c_n$, and for $n \ge 2$ let
$v(c,n) = \frac{1}{n-1} \sum_{i=1}^{n} (c_i - m(c,n))^2$ be their variance. Then for every real
$b$, as $n \to \infty$, $v(c,n) / m(c,n)^b$ tends to $\infty$ if $b < 2$, to $1/3$ if $b = 2$,
and to $0$ if $b > 2$.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 1 (`integers-2025-A23-thm-1`). -/
public theorem_wanted cyclicNumbers_variance_div_mean_rpow_tendsto :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let mean : ℕ → ℝ := fun n => (∑ i ∈ Finset.Icc 1 n, c i) / n
    let var : ℕ → ℝ := fun n => (∑ i ∈ Finset.Icc 1 n, (c i - mean n) ^ 2) / (n - 1)
    ∀ b : ℝ,
      (b < 2 → Tendsto (fun n => var n / mean n ^ b) atTop atTop) ∧
      (b = 2 → Tendsto (fun n => var n / mean n ^ b) atTop (𝓝 (1 / 3))) ∧
      (2 < b → Tendsto (fun n => var n / mean n ^ b) atTop (𝓝 0))

/-- **Mean and variance of the cyclic numbers.** Let $c_1 < c_2 < \cdots$ be the cyclic numbers
in increasing order, so $c_1 = 1$. For $n \ge 1$ let $m(c,n) = \frac{1}{n} \sum_{i=1}^{n} c_i$ be
the mean of $c_1, \dots, c_n$, and for $n \ge 2$ let
$v(c,n) = \frac{1}{n-1} \sum_{i=1}^{n} (c_i - m(c,n))^2$ be their variance. Then, as
$n \to \infty$, $m(c,n) \sim c_n / 2$ and $v(c,n) \sim c_n^2 / 12$.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 1 (`integers-2025-A23-thm-1`). -/
public theorem_wanted cyclicNumbers_mean_variance_isEquivalent :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let mean : ℕ → ℝ := fun n => (∑ i ∈ Finset.Icc 1 n, c i) / n
    let var : ℕ → ℝ := fun n => (∑ i ∈ Finset.Icc 1 n, (c i - mean n) ^ 2) / (n - 1)
    IsEquivalent atTop mean (fun n => c n / 2) ∧
      IsEquivalent atTop var (fun n => c n ^ 2 / 12)

/-- **Relation between the moments of the cyclic numbers.** Let $c_1 < c_2 < \cdots$ be the
cyclic numbers in increasing order, so $c_1 = 1$, and for $n \ge 1$ and a natural number $k$ let
$\mu'(c,n,k) = \frac{1}{n} \sum_{i=1}^{n} c_i^k$ be the $k$-th moment of $c_1, \dots, c_n$. Then
for all natural numbers $j \ge 1$ and $k$, as $n \to \infty$,
$$
\mu'(c,n,k) \sim \frac{(j+1)^{k/j}}{k+1} \, \mu'(c,n,j)^{k/j}.
$$

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 1 (`integers-2025-A23-thm-1`). -/
public theorem_wanted cyclicNumbers_moment_isEquivalent_moment_rpow (j k : ℕ) (hj : 1 ≤ j) :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let μ : ℕ → ℕ → ℝ := fun n k => (∑ i ∈ Finset.Icc 1 n, c i ^ k) / n
    IsEquivalent atTop (fun n => μ n k)
      (fun n => ((j : ℝ) + 1) ^ ((k : ℝ) / j) / (k + 1) * μ n j ^ ((k : ℝ) / j))

/-- **Generalized Taylor's law for cyclic numbers.** Let $c_1 < c_2 < \cdots$ be the cyclic
numbers in increasing order, so $c_1 = 1$. For $n \ge 1$ and a natural number $k$ let
$\mu'(c,n,k) = \frac{1}{n} \sum_{i=1}^{n} c_i^k$ be the $k$-th moment of $c_1, \dots, c_n$, and
let $m(c,n) = \mu'(c,n,1)$ be their mean. Then for every natural number $k$, as $n \to \infty$,
$$
\mu'(c,n,k) \sim \frac{2^k}{1+k} \, m(c,n)^k.
$$

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 1 (`integers-2025-A23-thm-1`). -/
public theorem_wanted cyclicNumbers_moment_isEquivalent_mean_pow (k : ℕ) :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let mean : ℕ → ℝ := fun n => (∑ i ∈ Finset.Icc 1 n, c i) / n
    IsEquivalent atTop (fun n : ℕ => (∑ i ∈ Finset.Icc 1 n, c i ^ k) / n)
      (fun n => (2 : ℝ) ^ k / (1 + k) * mean n ^ k)

/-- **Gaps between cyclic numbers under the Riemann hypothesis.** Assume the Riemann hypothesis.
Let $c_1 < c_2 < \cdots$ be the cyclic numbers in increasing order and $p_1 < p_2 < \cdots$ the
primes in increasing order. Then the gaps $d_n = c_{n+1} - c_n$ between consecutive cyclic
numbers satisfy $d_n = o(\sqrt{p_n} \log p_n)$ as $n \to \infty$.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 2 (`integers-2025-A23-thm-2`). -/
public theorem_wanted cyclicNumber_gap_isLittleO_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let p : ℕ → ℝ := fun n => (Nat.nth Nat.Prime (n - 1) : ℝ)
    (fun n => c (n + 1) - c n) =o[atTop] (fun n => Real.sqrt (p n) * Real.log (p n))

end

end MetaMathlibExt
