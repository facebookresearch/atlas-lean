/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Completely additive height functions

Statements from Hartosh Singh Bal, *Completely Additive Height Functions: Profile
Laws, Matula Bounds, and Inverse Growth*, INTEGERS 26 (2026), Article A116.
The statement `isGreatest_primeIndexHeight_level` is proved in
`MathlibExt.NumberTheory.CompletelyAdditiveHeightIsGreatestPrimeIndexHeightLevel`.

A height function is a completely additive `H : ℕ → ℕ` (on positive integers) with `H(p) ≥ 1`
for every prime `p` and only finitely many primes at each height `n ≥ 1`. Primes are indexed
from one: `p₁ = 2, p₂ = 3, …`, so `pᵢ = Nat.nth Nat.Prime (i - 1)`, and the index of a prime `p`
is `Nat.count Nat.Prime p + 1`. Iteratively defined height functions (Matula's
`H(pᵢ) = H(i) + 1`) are stated for every completely additive `H` satisfying the defining
equations, which determine `H` uniquely by strong induction.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import MathlibExt.NumberTheory.CompletelyAdditiveHeight
public import MathlibExt.NumberTheory.CompletelyAdditiveHeightIsGreatestPrimeIndexHeightLevel
public import MathlibExt.NumberTheory.CompletelyAdditiveHeightExistsHeightFunctionWithProfile

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- **Largest number at a given Matula height.** Write $p_i$ for the $i$-th prime, indexed from
one ($p_1 = 2$), and let $H$ be a function from the natural numbers to themselves that is
completely additive on the positive integers and satisfies $H(p_i) = H(i) + 1$ for every $i \ge 1$
(Matula's height function). Then for every $n \ge 4$ the largest positive integer $m$ with
$H(m) = n$ is the Gutman–Ivić maximal Matula number $P(n)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 5
(`integers-2026-A116-prop-5`). -/
public theorem_wanted matula_isGreatest_level {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    (hM : ∀ i, 1 ≤ i → H (nthPrimeOne i) = H i + 1) {n : ℕ} (hn : 4 ≤ n) :
    IsGreatest {m : ℕ | 0 < m ∧ H m = n} (matulaMax n)

/-- **Smallest number at a given Matula height.** Write $p_i$ for the $i$-th prime, indexed from
one ($p_1 = 2$), and let $H$ be a function from the natural numbers to themselves that is
completely additive on the positive integers and satisfies $H(p_i) = H(i) + 1$ for every $i \ge 1$
(Matula's height function). Then for every $n > 1$ the smallest positive integer $m$ with
$H(m) = n$ is $3 \cdot 5^{(n-2)/3}$ if $n \equiv 2 \pmod 3$, $5^{n/3}$ if $n \equiv 0 \pmod 3$, and
$9 \cdot 5^{(n-4)/3}$ if $n \equiv 1 \pmod 3$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 6
(`integers-2026-A116-prop-6`). -/
public theorem_wanted matula_isLeast_level {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    (hM : ∀ i, 1 ≤ i → H (nthPrimeOne i) = H i + 1) {n : ℕ} (hn : 1 < n) :
    IsLeast {m : ℕ | 0 < m ∧ H m = n}
      (if n % 3 = 2 then 3 * 5 ^ ((n - 2) / 3)
        else if n % 3 = 0 then 5 ^ (n / 3) else 9 * 5 ^ ((n - 4) / 3))

/-- **Rosser–Schoenfeld bounds for the $k$-th prime.** Write $p_k$ for the $k$-th prime, indexed
from one ($p_1 = 2$). There is a natural number $k_0$ such that every $k \ge k_0$ satisfies
$k (\log k + \log \log k - 1) \le p_k \le k (\log k + \log \log k)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 1 (`integers-2026-A116-lem-1`),
quoting Rosser and Schoenfeld. -/
public theorem_wanted nthPrimeOne_rosser_schoenfeld :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (k : ℝ) * (Real.log k + Real.log (Real.log k) - 1) ≤ nthPrimeOne k ∧
        (nthPrimeOne k : ℝ) ≤ k * (Real.log k + Real.log (Real.log k))

/-- **Prime reduction for summatory heights.** Let $H : \mathbb{N} \to \mathbb{N}$ be completely
additive on the positive integers, and for real $x$ let $F(x) = \sum_{1 \le m \le x} H(m)$. Then
there is a real constant $C$ such that for every real $x \ge 2$,
$$\Bigl| F(x) - x \sum_{p \le x} \frac{H(p)}{p - 1} \Bigr| \le C \log x \sum_{p \le x} H(p),$$
where both sums run over the primes $p \le x$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 7
(`integers-2026-A116-prop-7`), "In particular" display. -/
public theorem_wanted sum_height_asymptotic {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (H m : ℝ)) -
          x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (H p : ℝ) / ((p : ℝ) - 1)| ≤
        C * Real.log x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (H p : ℝ)

/-- **Iteratively defined height functions.** Write $p_i$ for the $i$-th prime, so $p_1 = 2$. Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) = 1$; suppose that for all integers $i, r \ge 1$, if
$p_r$ divides $f(i)$ then $r < i$ (this forces $f(i) \ge 1$ for $i \ge 1$); and suppose that for
every $t \ge 1$ only finitely many $i \ge 1$ have $f(i) = t$. Let $j \ge 1$. Then there is a
function $H : \mathbb{N} \to \mathbb{N}$ that is completely additive on the positive integers and
satisfies $H(p_i) = H(f(i)) + j$ for every $i \ge 1$, and every such $H$ is a height function.

The case $i = 1$ gives $H(2) = j$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 2 (`integers-2026-A116-thm-2`). -/
public theorem_wanted isHeightFunction_of_iterative (f : ℕ → ℕ) (hf1 : f 1 = 1)
    (hdiv : ∀ i r, 1 ≤ i → 1 ≤ r → nthPrimeOne r ∣ f i → r < i)
    (hfin : ∀ t, 1 ≤ t → {i : ℕ | 1 ≤ i ∧ f i = t}.Finite) {j : ℕ} (hj : 1 ≤ j) :
    (∃ H : ℕ → ℕ, IsCompletelyAdditiveNat H ∧ ∀ i, 1 ≤ i → H (nthPrimeOne i) = H (f i) + j) ∧
      ∀ H : ℕ → ℕ, IsCompletelyAdditiveNat H → (∀ i, 1 ≤ i → H (nthPrimeOne i) = H (f i) + j) →
        IsHeightFunction H

/-- **Meinardus' theorem.** Let $b_0, b_1, b_2, \dots$ be nonnegative reals with $b_k \ne 0$ for
some $k \ge 1$, and let $a_n$ be the coefficients of the weighted partition product
$\prod_{k \ge 1} (1 - q^k)^{-b_k}$. Suppose that the weights satisfy Meinardus' hypotheses
(M1)–(M3) with exponent $\alpha > 0$, residue $A > 0$ and continuation $G$, and put
$\kappa = (\operatorname{Re} G(0) - 1 - \alpha/2)/(\alpha + 1)$ and
$C_2 = (1 + 1/\alpha)\,(A\,\Gamma(\alpha + 1)\,\zeta(\alpha + 1))^{1/(\alpha + 1)}$. Then there is
$C_1 > 0$ with $a_n \sim C_1 n^{\kappa} \exp(C_2 n^{\alpha/(\alpha + 1)})$ as $n \to \infty$, and
$\log a_n \sim C_2 n^{\alpha/(\alpha + 1)}$ as $n \to \infty$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 3 (`integers-2026-A116-thm-3`),
quoting Meinardus. -/
public theorem_wanted meinardus_asymptotic {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hb0 : ∃ k, 1 ≤ k ∧ b k ≠ 0) {α A : ℝ} (hα : 0 < α) (hA : 0 < A) {G : ℂ → ℂ}
    (hM : MeinardusHypotheses b α A G) :
    let κ := ((G 0).re - 1 - α / 2) / (α + 1)
    let C₂ := (1 + 1 / α) *
      (A * Real.Gamma (α + 1) * (riemannZeta (α + 1)).re) ^ (1 / (α + 1))
    (∃ C₁ : ℝ, 0 < C₁ ∧ Asymptotics.IsEquivalent atTop (fun n : ℕ => weightedPartitionCoeff b n)
      (fun n : ℕ => C₁ * (n : ℝ) ^ κ * Real.exp (C₂ * (n : ℝ) ^ (α / (α + 1))))) ∧
      Asymptotics.IsEquivalent atTop (fun n : ℕ => Real.log (weightedPartitionCoeff b n))
        (fun n : ℕ => C₂ * (n : ℝ) ^ (α / (α + 1)))

/-- **A simple pole of a Dirichlet series from the growth of its partial sums.** Let
$(\pi_k)_{k \ge 0}$ be nonnegative real numbers and let $C$, $\alpha$, $\eta$ be positive reals.
Suppose there is a constant $K$ with
$\bigl|\sum_{k=1}^{\lfloor x \rfloor} \pi_k - (C/\alpha) x^{\alpha}\bigr| \le K x^{\alpha - \eta}$
for every real $x \ge 1$. Then the Dirichlet series $B(s) = \sum_{k \ge 1} \pi_k k^{-s}$ converges
absolutely for $\operatorname{Re} s > \alpha$, and there is a function $R$, holomorphic on the
half-plane $\operatorname{Re} s > \alpha - \eta$, with $B(s) = C/(s - \alpha) + R(s)$ for
$\operatorname{Re} s > \alpha$. Moreover, for every $\delta$ with $0 < \delta < \eta$ there is a
constant $K'$ with $|C/(s - \alpha) + R(s)| \le K'(1 + |\operatorname{Im} s|)$ for all complex $s$
with $\operatorname{Re} s \ge \alpha - \eta + \delta$ and $|\operatorname{Im} s| \ge 1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 3 (`integers-2026-A116-lem-3`). -/
public theorem_wanted lseries_profile_simple_pole {π : ℕ → ℝ} (hπ : ∀ k, 0 ≤ π k) {C α η : ℝ}
    (hC : 0 < C) (hα : 0 < α) (hη : 0 < η)
    (hcum : ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x →
      |∑ k ∈ Finset.Icc 1 ⌊x⌋₊, π k - C / α * x ^ α| ≤ K * x ^ (α - η)) :
    (∀ s : ℂ, α < s.re → LSeriesSummable (fun k => (π k : ℂ)) s) ∧
      ∃ R : ℂ → ℂ, DifferentiableOn ℂ R {s | α - η < s.re} ∧
        (∀ s : ℂ, α < s.re → LSeries (fun k => (π k : ℂ)) s = C / (s - α) + R s) ∧
        ∀ δ : ℝ, 0 < δ → δ < η → ∃ K : ℝ, ∀ s : ℂ, α - η + δ ≤ s.re → 1 ≤ |s.im| →
          ‖C / (s - α) + R s‖ ≤ K * (1 + |s.im|)

/-- **Meinardus asymptotics for the levels of a height function.** Let $H$ be a height function,
for $k \ge 0$ let $\pi_k$ be the number of primes $p$ with $H(p) = k$, and for $n \ge 0$ let $N_n$
be the number of integers $m \ge 1$ with $H(m) = n$. Let $\alpha > 0$ and $C > 0$ be real numbers
and suppose that the weights $(\pi_k)$ satisfy Meinardus' hypotheses with exponent $\alpha$,
residue $C$ and some continuation $G$. Put
$C_2 = (1 + 1/\alpha)\bigl(C\,\Gamma(\alpha + 1)\,\zeta(\alpha + 1)\bigr)^{1/(\alpha+1)}$. Then
there are real numbers $C_1 > 0$ and $\kappa$ with
$N_n \sim C_1 n^{\kappa} \exp\bigl(C_2 n^{\alpha/(\alpha+1)}\bigr)$ as $n \to \infty$, and
$\log N_n \sim C_2 n^{\alpha/(\alpha+1)}$ as $n \to \infty$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 4 (`integers-2026-A116-thm-4`). -/
public theorem_wanted heightLevel_card_meinardus {H : ℕ → ℕ} (hH : IsHeightFunction H)
    {α C : ℝ} (hα : 0 < α) (hC : 0 < C) {G : ℂ → ℂ}
    (hM : MeinardusHypotheses (fun k => ({p : ℕ | p.Prime ∧ H p = k}.ncard : ℝ)) α C G) :
    let C₂ := (1 + 1 / α) *
      (C * Real.Gamma (α + 1) * (riemannZeta (α + 1)).re) ^ (1 / (α + 1))
    (∃ C₁ κ : ℝ, 0 < C₁ ∧ Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (Nat.card {m : ℕ // 0 < m ∧ H m = n} : ℝ))
      (fun n : ℕ => C₁ * (n : ℝ) ^ κ * Real.exp (C₂ * (n : ℝ) ^ (α / (α + 1))))) ∧
      Asymptotics.IsEquivalent atTop
        (fun n : ℕ => Real.log (Nat.card {m : ℕ // 0 < m ∧ H m = n} : ℝ))
        (fun n : ℕ => C₂ * (n : ℝ) ^ (α / (α + 1)))

/-- **Identifying the profile from the growth of the levels.** Let $H$ be a height function, for
$k \ge 0$ let $\pi_k$ be the number of primes $p$ with $H(p) = k$, and for $n \ge 0$ let $N_n$ be
the number of integers $m \ge 1$ with $H(m) = n$. Let $r > 0$ and $A > 0$ be real numbers and
suppose that the weights $(\pi_k)$ satisfy Meinardus' hypotheses with exponent $r$, residue $A$
and some continuation $G$. Suppose further that $N_n \sim C_1 n^{\kappa} \exp(C_2 n^{\beta})$ as
$n \to \infty$ for real numbers $C_1 > 0$, $C_2 > 0$, $\kappa$ and $\beta$ with $0 < \beta < 1$.
Then $\beta = r/(r + 1)$, $r = \beta/(1 - \beta)$,
$C_2 = (1 + 1/r)\bigl(A\,\Gamma(r + 1)\,\zeta(r + 1)\bigr)^{1/(r+1)}$, and
$\sum_{k=1}^{\lfloor x \rfloor} \pi_k \sim (A/r)\, x^r$ as the real number $x$ tends to $\infty$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 1 (`integers-2026-A116-cor-1`). -/
public theorem_wanted heightProfile_identification {H : ℕ → ℕ} (hH : IsHeightFunction H)
    {r A : ℝ} (hr : 0 < r) (hA : 0 < A) {G : ℂ → ℂ}
    (hM : MeinardusHypotheses (fun k => ({p : ℕ | p.Prime ∧ H p = k}.ncard : ℝ)) r A G)
    {C₁ C₂ κ β : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hN : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (Nat.card {m : ℕ // 0 < m ∧ H m = n} : ℝ))
      (fun n : ℕ => C₁ * (n : ℝ) ^ κ * Real.exp (C₂ * (n : ℝ) ^ β))) :
    β = r / (r + 1) ∧ r = β / (1 - β) ∧
      C₂ = (1 + 1 / r) * (A * Real.Gamma (r + 1) * (riemannZeta (r + 1)).re) ^ (1 / (r + 1)) ∧
      Asymptotics.IsEquivalent atTop
        (fun x : ℝ => (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, {p : ℕ | p.Prime ∧ H p = k}.ncard : ℝ))
        (fun x : ℝ => A / r * x ^ r)

/-- **Inverting a polynomial profile.** Let $\pi : \mathbb{N} \to \mathbb{N}$ be a sequence with
cumulative profile $\Pi_k = \sum_{j=1}^{k} \pi_j$, let $k(i)$ be its block index (the least $k$
with $i \le \Pi_k$, and $0$ if there is none), let $H_{\mathrm{seq}}$ be its canonical sequential
realization, and write $p_i$ for the $i$-th prime, indexed from one. Let $C > 0$ and $\alpha > 0$
be real numbers with $\Pi_k \sim C k^\alpha$ as $k \to \infty$. Then $k(i) \sim (i/C)^{1/\alpha}$
as $i \to \infty$, and $H_{\mathrm{seq}}(p_i) = k(i)$ for every $i \ge 1$.

The paper also assumes that $\Pi_k$ is eventually strictly increasing; that hypothesis is dropped
here, since $\Pi$ is nondecreasing, which suffices.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 4 (`integers-2026-A116-lem-4`). -/
public theorem_wanted seqHeightIndex_isEquivalent {π : ℕ → ℕ} {C α : ℝ} (hC : 0 < C)
    (hα : 0 < α)
    (hcum : Asymptotics.IsEquivalent atTop (fun k : ℕ => (profilePartialSum π k : ℝ))
      (fun k : ℕ => C * (k : ℝ) ^ α)) :
    Asymptotics.IsEquivalent atTop (fun i : ℕ => (seqHeightIndex π i : ℝ))
        (fun i : ℕ => ((i : ℝ) / C) ^ (1 / α)) ∧
      ∀ i, 1 ≤ i → canonicalSeqHeight π (nthPrimeOne i) = seqHeightIndex π i

/-- **A logarithmic-integral sum.** For every real $\beta > 0$,
$$\sum_{i=2}^{m} \frac{i^{\beta - 1}}{\log i} \sim \frac{m^\beta}{\beta \log m}$$
as $m \to \infty$ through the natural numbers.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 5 (`integers-2026-A116-lem-5`). -/
public theorem_wanted sum_rpow_div_log_isEquivalent {β : ℝ} (hβ : 0 < β) :
    Asymptotics.IsEquivalent atTop
      (fun m : ℕ => ∑ i ∈ Finset.Icc 2 m, (i : ℝ) ^ (β - 1) / Real.log i)
      (fun m : ℕ => (m : ℝ) ^ β / (β * Real.log m))

/-- **Prime-harmonic growth of the canonical sequential realization.** Let $(\pi_k)_{k \ge 1}$ be
a sequence of nonnegative integers with partial sums $\Pi_k = \sum_{1 \le j \le k} \pi_j$, let
$H_{\mathrm{seq}}$ be its canonical sequential realization, and suppose that $C > 0$ and
$\alpha > 0$ are real numbers with $\Pi_k \sim C k^\alpha$ as $k \to \infty$. Write
$S(x) = \sum_{p \le x} H_{\mathrm{seq}}(p)/p$, the sum over primes $p \le x$, and let $m(x)$ be
the number of primes $p \le x$. Then, as $x \to \infty$ over the reals,
$S(x) \sim \frac{\alpha}{C^{1/\alpha}} \cdot \frac{m(x)^{1/\alpha}}{\log m(x)}$ and
$S(x) = \Theta\bigl(x^{1/\alpha} / (\log x)^{1+1/\alpha}\bigr)$, where $f = \Theta(g)$ means
$f = O(g)$ and $g = O(f)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 5 (`integers-2026-A116-thm-5`). -/
public theorem_wanted canonicalSeq_primeHarmonicSum {π : ℕ → ℕ} {C α : ℝ} (hC : 0 < C)
    (hα : 0 < α)
    (hcum : Asymptotics.IsEquivalent atTop (fun k : ℕ => (profilePartialSum π k : ℝ))
      (fun k : ℕ => C * (k : ℝ) ^ α)) :
    Asymptotics.IsEquivalent atTop
        (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight π p : ℝ) / p)
        (fun x : ℝ => α / C ^ (1 / α) *
          ((Nat.primeCounting ⌊x⌋₊ : ℝ) ^ (1 / α) / Real.log (Nat.primeCounting ⌊x⌋₊))) ∧
      (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight π p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x ^ (1 / α) / Real.log x ^ (1 + 1 / α))

/-- **Average order of the canonical sequential realization.** Let $(\pi_k)_{k \ge 1}$ be a
sequence of nonnegative integers with partial sums $\Pi_k = \sum_{1 \le j \le k} \pi_j$, let
$H_{\mathrm{seq}}$ be its canonical sequential realization, and suppose that $C > 0$ and
$\alpha > 0$ are real numbers with $\Pi_k \sim C k^\alpha$ as $k \to \infty$. Then, as
$x \to \infty$ over the reals, each of the three functions
$x \sum_{p \le x} H_{\mathrm{seq}}(p)/p$, $\sum_{p \le x} H_{\mathrm{seq}}(p) \log x / \log p$
(both sums over primes $p \le x$) and $\sum_{1 \le n \le x} H_{\mathrm{seq}}(n)$ is
$\Theta\bigl(x^{1+1/\alpha} / (\log x)^{1+1/\alpha}\bigr)$, where $f = \Theta(g)$ means
$f = O(g)$ and $g = O(f)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 2 (`integers-2026-A116-cor-2`),
statement read from the journal PDF (the corpus record carries the prose of Section 7.6 that
follows it). -/
public theorem_wanted canonicalSeq_averageOrder {π : ℕ → ℕ} {C α : ℝ} (hC : 0 < C)
    (hα : 0 < α)
    (hcum : Asymptotics.IsEquivalent atTop (fun k : ℕ => (profilePartialSum π k : ℝ))
      (fun k : ℕ => C * (k : ℝ) ^ α)) :
    (fun x : ℝ => x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        (canonicalSeqHeight π p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x ^ (1 + 1 / α) / Real.log x ^ (1 + 1 / α)) ∧
      (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        (canonicalSeqHeight π p : ℝ) * (Real.log x / Real.log p)) =Θ[atTop]
        (fun x : ℝ => x ^ (1 + 1 / α) / Real.log x ^ (1 + 1 / α)) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight π n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x ^ (1 + 1 / α) / Real.log x ^ (1 + 1 / α))

/-- **Growth for the plane partition profile.** Let $H_{\mathrm{seq}}$ be the canonical
sequential realization of the profile $\pi_k = k$ for $k \ge 1$, let
$S(x) = \sum_{p \le x} H_{\mathrm{seq}}(p)/p$ (the sum over primes $p \le x$) and
$F(x) = \sum_{1 \le n \le x} H_{\mathrm{seq}}(n)$, and let $m(x)$ be the number of primes
$p \le x$. Then, as $x \to \infty$ over the reals,
$S(x) \sim 2\sqrt{2}\, \sqrt{m(x)} / \log m(x)$,
$S(x) = \Theta\bigl(x^{1/2} / (\log x)^{3/2}\bigr)$, $F(x) = \Theta\bigl(x\, S(x)\bigr)$ and
$F(x) = \Theta\bigl(x^{3/2} / (\log x)^{3/2}\bigr)$, where $f = \Theta(g)$ means $f = O(g)$ and
$g = O(f)$.

Here the partial sums are $k(k+1)/2 \sim k^2/2$, so this is the case $\alpha = 2$, $C = 1/2$ of
the general growth laws.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 4 (`integers-2026-A116-cor-4`). -/
public theorem_wanted canonicalSeq_planePartitionProfile_growth :
    Asymptotics.IsEquivalent atTop
        (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight (fun k => k) p : ℝ) / p)
        (fun x : ℝ => 2 * Real.sqrt 2 *
          (Real.sqrt (Nat.primeCounting ⌊x⌋₊) / Real.log (Nat.primeCounting ⌊x⌋₊))) ∧
      (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight (fun k => k) p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x ^ (1 / 2 : ℝ) / Real.log x ^ (3 / 2 : ℝ)) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight (fun k => k) n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight (fun k => k) p : ℝ) / p) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight (fun k => k) n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x ^ (3 / 2 : ℝ) / Real.log x ^ (3 / 2 : ℝ))

end

end MetaMathlibExt
