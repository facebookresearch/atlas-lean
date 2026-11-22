/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import WantedExt.NumberTheory.GeneralizedHarmonicGammaWanted

/-!
# Sums over primes II (statements)

Statement-only targets from Rusen Li, *Sums over Primes II*: the asymptotic of hyperharmonic
numbers, Jakimczuk's summation lemma, the asymptotics of the `n`-th (squarefree) number with
exactly `k` prime factors, two power-log summation asymptotics, the explicit formulas and
asymptotics of the generalized (alternating) hyperharmonic numbers `H_n^{(p,r)}` and
`H_n^{(p,r,i)}` (`i = 1, 2, 3`), and the asymptotics of sums over primes and over squarefree
numbers with `k` prime factors weighted by powers of these numbers.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset

@[expose] public section

/-- **Hyperharmonic numbers.** The hyperharmonic numbers $h_n^{(r)} \in \mathbb{Q}$ of order $r$
and index $n$, for natural numbers $r$ and $n$, are defined by recursion on $r$:
$h_n^{(0)} = 1/n$ for $n \ge 1$, $h_0^{(0)} = 0$, and
$$h_n^{(r+1)} = \sum_{k=1}^{n} h_k^{(r)}.$$
Thus $h_0^{(r)} = 0$ for every order $r$, and $h_n^{(1)} = 1 + 1/2 + \dots + 1/n$ is the $n$-th
harmonic number $H_n$. This is the definition of Conway and Guy.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public def hyperharmonic : ℕ → ℕ → ℚ
  | 0, n => 1 / n
  | r + 1, n => ∑ k ∈ Icc 1 n, hyperharmonic r k

/-- **Recursion for the hyperharmonic numbers.** For all natural numbers $r$ and $n$, the
hyperharmonic numbers $h_m^{(s)}$ (of order $s$ and index $m$) satisfy
$$h_n^{(r+1)} = \sum_{k=1}^{n} h_k^{(r)}.$$

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public theorem hyperharmonic_succ (r n : ℕ) :
    hyperharmonic (r + 1) n = ∑ k ∈ Icc 1 n, hyperharmonic r k := rfl

/-- **Hyperharmonic numbers of order one are the harmonic numbers.** For every natural number $n$,
the hyperharmonic number $h_n^{(1)}$ of order $1$ and index $n$ equals the $n$-th harmonic number
$H_n = \sum_{k=1}^{n} 1/k$ (in particular $h_0^{(1)} = H_0 = 0$).

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public theorem hyperharmonic_one (n : ℕ) : hyperharmonic 1 n = harmonic n := by
  induction n with
  | zero => simp [hyperharmonic]
  | succ n ih =>
    rw [harmonic_succ, ← ih, hyperharmonic, hyperharmonic, Finset.sum_Icc_succ_top (by omega)]
    simp [hyperharmonic]

/-- **The hyperharmonic number $h_2^{(2)}$.** The hyperharmonic number of order $2$ and index $2$
is $h_2^{(2)} = 5/2$.

Indeed $h_2^{(2)} = h_1^{(1)} + h_2^{(1)} = H_1 + H_2 = 1 + 3/2$, where $H_n$ is the $n$-th
harmonic number.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public theorem hyperharmonic_two_two : hyperharmonic 2 2 = 5 / 2 := by
  simp [hyperharmonic, Finset.sum_Icc_succ_top]
  norm_num

/-- **Asymptotic of the hyperharmonic numbers (Mező).** For every natural number $r \ge 1$, the
hyperharmonic numbers $h_n^{(r)}$ of order $r$ are asymptotically equivalent, as $n \to \infty$,
to $n^{r-1} \log n / (r-1)!$, where $\log$ is the natural logarithm:
$$h_n^{(r)} \sim \frac{n^{r-1} \log n}{(r-1)!} \qquad (n \to \infty).$$

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (`jis-2024-24.4.1-lem-1`). -/
public theorem_wanted hyperharmonic_isEquivalent (r : ℕ) (hr : 1 ≤ r) :
    (fun n : ℕ => (hyperharmonic r n : ℝ)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (r - 1) * Real.log n / (r - 1).factorial

/-- **Jakimczuk's lemma on sums of asymptotically equivalent terms.** Let $(a_i)_{i \ge 0}$ and
$(b_i)_{i \ge 0}$ be real sequences with $a_i > 0$ and $b_i > 0$ for every $i \ge 1$. If
$a_i \sim b_i$ as $i \to \infty$ and $\sum_{i=1}^{n} b_i \to +\infty$ as $n \to \infty$, then
$$\sum_{i=1}^{n} a_i \sim \sum_{i=1}^{n} b_i \qquad (n \to \infty).$$

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 7 (`jis-2024-24.4.1-lem-7`). -/
public theorem_wanted sum_isEquivalent_of_isEquivalent (a b : ℕ → ℝ)
    (ha : ∀ i, 1 ≤ i → 0 < a i) (hb : ∀ i, 1 ≤ i → 0 < b i) (hab : a ~[atTop] b)
    (hdiv : Tendsto (fun n => ∑ i ∈ Icc 1 n, b i) atTop atTop) :
    (fun n => ∑ i ∈ Icc 1 n, a i) ~[atTop] fun n => ∑ i ∈ Icc 1 n, b i

/-- **Asymptotics of the $n$-th number with $k$ prime factors.** Let $k \ge 1$. For $n \ge 1$ let
$p_{n,k}$ be the $n$-th squarefree natural number with exactly $k$ distinct prime factors, and let
$q_{n,k}$ be the $n$-th natural number with exactly $k$ prime factors counted with multiplicity
(that is, $\Omega(q_{n,k}) = k$). Then, as $n \to \infty$,
$p_{n,k} \sim q_{n,k} \sim (k-1)!\, n \log n / (\log \log n)^{k-1}$ and
$p_{n,k} (\log \log p_{n,k})^{k-1} \sim q_{n,k} (\log \log q_{n,k})^{k-1} \sim (k-1)!\, n \log n$.
Moreover the $n$-th prime $p_n$ satisfies $p_n \sim n \log n$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 8 (`jis-2024-24.4.1-lem-8`). -/
public theorem_wanted nth_kPrimeFactors_isEquivalent (k : ℕ) (hk : 1 ≤ k) :
    let p : ℕ → ℝ := fun n =>
      (Nat.nth (fun m => Squarefree m ∧ m.primeFactors.card = k) (n - 1) : ℝ)
    let q : ℕ → ℝ := fun n =>
      (Nat.nth (fun m => ArithmeticFunction.cardFactors m = k) (n - 1) : ℝ)
    (p ~[atTop] q) ∧
      (q ~[atTop] fun n : ℕ =>
        (k - 1).factorial * n * Real.log n / Real.log (Real.log n) ^ (k - 1)) ∧
      ((fun n => p n * Real.log (Real.log (p n)) ^ (k - 1)) ~[atTop]
        fun n => q n * Real.log (Real.log (q n)) ^ (k - 1)) ∧
      ((fun n => q n * Real.log (Real.log (q n)) ^ (k - 1)) ~[atTop]
        fun n : ℕ => (k - 1).factorial * n * Real.log n) ∧
      ((fun n : ℕ => (Nat.nth Nat.Prime (n - 1) : ℝ)) ~[atTop]
        fun n : ℕ => n * Real.log n)

/-- **Asymptotics of power-logarithm sums.** For all $m, n, k \in \mathbb{N}$, as the natural
number $x$ tends to infinity,
$$\sum_{\ell=1}^{x} \ell^m (\log \ell)^n \sim \frac{x^{m+1} (\log x)^n}{m+1}$$
and
$$\sum_{\ell=1}^{x} \frac{\ell^m (\log \ell)^n}{(\log \log \ell)^k} \sim
\frac{x^{m+1} (\log x)^n}{(m+1)(\log \log x)^k}.$$

In the second sum the term $\ell = 1$, where $\log \log 1 = \log 0$ is undefined, is evaluated with
the conventions $\log 0 = 0$ and $t/0 = 0$; a single term does not affect the asymptotic.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 9 (`jis-2024-24.4.1-lem-9`). -/
public theorem_wanted sum_pow_mul_log_pow_isEquivalent (m n k : ℕ) :
    ((fun x : ℕ => ∑ l ∈ Icc 1 x, (l : ℝ) ^ m * Real.log l ^ n) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (m + 1) * Real.log x ^ n / (m + 1)) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (l : ℝ) ^ m * Real.log l ^ n / Real.log (Real.log l) ^ k) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (m + 1) * Real.log x ^ n /
        ((m + 1) * Real.log (Real.log x) ^ k))


/-- **Alternating generalized harmonic numbers.** For a real number $s$ and a natural number $n$,
the alternating generalized harmonic number is
$\overline{H}_n^{(s)} = \sum_{j=1}^{n} (-1)^{j-1} / j^s$, which is $0$ for $n = 0$.

For $s = -p$ with $p$ a natural number this is $\sum_{j=1}^{n} (-1)^{j-1} j^p$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definition of `H̄_n^{(p)}` and `H̄_n^{(-p)}`). -/
public noncomputable def alternatingGeneralizedHarmonic (s : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ (j - 1) * ((j : ℝ) ^ s)⁻¹

/-- **Alternating generalized harmonic numbers of index zero.** For every real number $s$, the
alternating generalized harmonic number $\overline{H}_0^{(s)}$ is $0$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definition of `H̄_n^{(p)}`). -/
@[simp]
public theorem alternatingGeneralizedHarmonic_zero (s : ℝ) :
    alternatingGeneralizedHarmonic s 0 = 0 := by
  simp [alternatingGeneralizedHarmonic]

/-- **Signed iterated partial sums.** Let $(b_n)_{n \ge 0}$ be a real sequence and fix a choice of
signs, either alternating, $\varepsilon_k = (-1)^{k-1}$, or constant, $\varepsilon_k = 1$. The
signed iterated partial sums $S^{(r)}_n$ of $b$, for orders $r \in \mathbb{N}$ and
$n \in \mathbb{N}$, are defined by $S^{(0)}_n = 0$, $S^{(1)}_n = b_n$ and, for $r \ge 1$,
$$S^{(r+1)}_n = \sum_{k=1}^{n} \varepsilon_k \, S^{(r)}_k.$$
The value $0$ at order $0$ is a convention and is not used.

With $b_n = H_n^{(p)} = \sum_{j=1}^{n} j^{-p}$, constant signs give the generalized hyperharmonic
numbers $H_n^{(p,r)}$ and alternating signs give the type I alternating ones $H_n^{(p,r,1)}$; with
$b_n = \bar H_n^{(p)} = \sum_{j=1}^{n} (-1)^{j-1} j^{-p}$, constant signs give type II,
$H_n^{(p,r,2)}$, and alternating signs give type III, $H_n^{(p,r,3)}$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definitions of `H_n^{(p,r)}` and `H_n^{(p,r,i)}`, `i = 1, 2, 3`). -/
public noncomputable def signedIteratedPartialSum (alt : Bool) (b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | 1, n => b n
  | r + 2, n => ∑ k ∈ Icc 1 n, (if alt then (-1 : ℝ) ^ (k - 1) else 1) *
      signedIteratedPartialSum alt b (r + 1) k

/-- **Order one of the signed iterated partial sums.** For every real sequence
$(b_n)_{n \ge 0}$, either choice of signs and every $n \in \mathbb{N}$, the signed iterated partial
sum of $b$ of order $1$ at $n$ equals $b_n$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (`H_n^{(p,1)} = H_n^{(p)}`, `H_n^{(p,1,1)} = H_n^{(p)}`,
`H_n^{(p,1,2)} = H_n^{(p,1,3)} = H̄_n^{(p)}`). -/
public theorem signedIteratedPartialSum_one (alt : Bool) (b : ℕ → ℝ) (n : ℕ) :
    signedIteratedPartialSum alt b 1 n = b n := rfl

/-- **Recursion for the signed iterated partial sums.** Let $(b_n)_{n \ge 0}$ be a real sequence,
fix a choice of signs, either $\varepsilon_k = (-1)^{k-1}$ for all $k$ or $\varepsilon_k = 1$ for
all $k$, and let $S^{(r)}_n$ denote the signed iterated partial sum of $b$ of order $r$ at $n$ for
this choice. Then for every $r \ge 1$ and every $n \in \mathbb{N}$,
$$S^{(r+1)}_n = \sum_{k=1}^{n} \varepsilon_k \, S^{(r)}_k.$$

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definitions of `H_n^{(p,r)}` and `H_n^{(p,r,i)}`). -/
public theorem signedIteratedPartialSum_succ (alt : Bool) (b : ℕ → ℝ) (r n : ℕ) :
    signedIteratedPartialSum alt b (r + 2) n = ∑ k ∈ Icc 1 n,
      (if alt then (-1 : ℝ) ^ (k - 1) else 1) * signedIteratedPartialSum alt b (r + 1) k := rfl

/-- **Alternating zeta values.** For a natural number $p$, the alternating zeta value
$\bar\zeta(p)$ is defined by $\bar\zeta(1) = \log 2$, by $\bar\zeta(p) = (1 - 2^{1-p})\,\zeta(p)$
for $p \ge 2$, where $\zeta(p) = \sum_{n \ge 1} 1/n^p$, and by $\bar\zeta(0) = 0$.

For every $p \ge 1$ this is the alternating series $\bar\zeta(p) = \sum_{n \ge 1} (-1)^{n-1}/n^p$;
the value at $p = 0$ is not used.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 10 (definition of `ζ̄(s)`). -/
public noncomputable def alternatingZeta (p : ℕ) : ℝ :=
  if p = 1 then Real.log 2 else (1 - 2 ^ (1 - (p : ℝ))) * ∑' n : ℕ, 1 / (n : ℝ) ^ p

/-- **Alternating zeta value at one.** The alternating zeta value at $1$ is $\bar\zeta(1) = \log 2$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 10 (definition of `ζ̄(s)`). -/
@[simp]
public theorem alternatingZeta_one : alternatingZeta 1 = Real.log 2 := by
  simp [alternatingZeta]

/-- **Li's coefficients $a(r, m, j)$.** The rational numbers $a(r, m, j)$, for natural numbers
$r$, $m$, $j$, are defined by recursion on $r$. For all $m$ and $j$, $a(0, m, j) = 0$; moreover
$a(1, 0, 0) = 1$ and $a(1, m, j) = 0$ for $(m, j) \ne (0, 0)$. For $r \ge 1$ the values of
order $r + 1$ are as follows. First,
$$a(r+1, r, 0) = -\sum_{m=0}^{r-1} \frac{a(r, m, r-m-1)}{r-m}.$$
For $0 \le m \le r - 1$ and $1 \le \ell \le r - m$,
$$a(r+1,m,\ell) = \sum_{j=\ell-1}^{r-1-m} \frac{a(r,m,j)}{j+1} \binom{j+1}{j-\ell+1} B_{j-\ell+1}.$$
For $0 \le m \le r - 1$,
$$a(r+1, m, 0) = -\sum_{y=0}^{m} \sum_{j=\max(0, m-y-1)}^{r-1-y} a(r, y, j)\, D(m, j, y),$$
where
$$D(m, j, y) = \frac{1}{j+1} \sum_{\ell=\max(0, m-y-1)}^{j} \binom{j+1}{j-\ell} B_{j-\ell}
\binom{\ell+1}{m-y} (-1)^{1+\ell-m+y}.$$
All other values $a(r+1, m, \ell)$ are $0$. Here $B_n$ are the Bernoulli numbers with
$B_1 = 1/2$, that is, the numbers determined by $\sum_{j=0}^{k} \binom{k+1}{j} B_j = k + 1$ for
all $k \ge 0$.

Li writes $D(r, m, j, y)$; the value does not depend on $r$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3 (quoting Li, *Euler sums of generalized hyperharmonic numbers*). -/
public def liCoeffA : ℕ → ℕ → ℕ → ℚ
  | 0, _, _ => 0
  | 1, m, j => if m = 0 ∧ j = 0 then 1 else 0
  | r + 2, m, l =>
    if m = r + 1 ∧ l = 0 then
      -∑ m' ∈ range (r + 1), liCoeffA (r + 1) m' (r - m') / ((r + 1 - m' : ℕ) : ℚ)
    else if m ≤ r ∧ 1 ≤ l ∧ l ≤ r + 1 - m then
      ∑ j ∈ Icc (l - 1) (r - m), liCoeffA (r + 1) m j / ((j + 1 : ℕ) : ℚ) *
        ((j + 1).choose (j + 1 - l) : ℚ) * bernoulli' (j + 1 - l)
    else if m ≤ r ∧ l = 0 then
      -∑ y ∈ range (m + 1), ∑ j ∈ Icc (m - y - 1) (r - y), liCoeffA (r + 1) y j *
        ∑ i ∈ Icc (m - y - 1) j, 1 / ((j + 1 : ℕ) : ℚ) * ((j + 1).choose (j - i) : ℚ) *
          bernoulli' (j - i) * ((i + 1).choose (m - y) : ℚ) * (-1) ^ (1 + i + y - m)
    else 0

/-- **The coefficient $a(1, 0, 0)$.** The coefficient $a(1, 0, 0)$ of Li's Lemma 3 equals $1$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3. -/
public theorem liCoeffA_one_zero_zero : liCoeffA 1 0 0 = 1 := by
  simp [liCoeffA]

/-- **The coefficient $a(2, 1, 0)$.** The coefficient $a(2, 1, 0)$ of Li's Lemma 3 equals $-1$.

By the recursion, $a(2, 1, 0) = -a(1, 0, 0) = -1$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3. -/
public theorem liCoeffA_two_one_zero : liCoeffA 2 1 0 = -1 := by
  simp [liCoeffA]

/-- **Li's coefficients $c(m, j)$.** For natural numbers $m$ and $j$, the rational number
$c(m, j)$ is $\frac{1}{m+1} \binom{m+1}{m+1-j} B_{m+1-j}$ when $j \le m + 1$ and $0$ otherwise,
where $B_i$ denotes the Bernoulli numbers with the convention $B_1 = +\frac{1}{2}$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public def liCoeffC (m j : ℕ) : ℚ :=
  if j ≤ m + 1 then
    1 / ((m + 1 : ℕ) : ℚ) * ((m + 1).choose (m + 1 - j) : ℚ) * bernoulli' (m + 1 - j)
  else 0

/-- **Li's coefficient $c(0, 0)$.** Li's coefficient $c(0, 0)$ equals $\frac{1}{2}$ (this is the
Bernoulli number $B_1$ in the convention $B_1 = +\frac{1}{2}$).

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public theorem liCoeffC_zero_zero : liCoeffC 0 0 = 1 / 2 := by
  simp [liCoeffC]

/-- **Li's coefficients $d(m, j)$.** For natural numbers $m$ and $j$, the rational number
$d(m, j)$ is $\frac{1}{m+1} \sum_{k} \binom{m+1}{m-k} B_{m-k} \binom{1+k}{j} (-1)^{1+k-j}$, the sum
running over the natural numbers $k$ with $\max(j - 1, 0) \le k \le m$ (so $d(m, j) = 0$ when
$j > m + 1$), where $B_i$ denotes the Bernoulli numbers with the convention $B_1 = +\frac{1}{2}$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public def liCoeffD (m j : ℕ) : ℚ :=
  1 / ((m + 1 : ℕ) : ℚ) * ∑ k ∈ Icc (j - 1) m,
    ((m + 1).choose (m - k) : ℚ) * bernoulli' (m - k) * ((1 + k).choose j : ℚ) * (-1) ^ (1 + k - j)

/-- **Li's coefficient $d(0, 1)$.** Li's coefficient $d(0, 1)$ equals $1$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public theorem liCoeffD_zero_one : liCoeffD 0 1 = 1 := by
  simp [liCoeffD]

/-- **Li's coefficients $c_1(m, j)$.** For natural numbers $m$ and $j$, the rational number
$c_1(m, j)$ is
$\frac{1}{2(m+1)} \sum_{k=0}^{m-j} \binom{m+1}{k} B_k 2^k \binom{m+1-k}{j} (-1)^{m-k-j}$ when
$j \le m$ and $0$ otherwise, where $B_i$ denotes the Bernoulli numbers with the convention
$B_1 = +\frac{1}{2}$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public def liCoeffC1 (m j : ℕ) : ℚ :=
  if j ≤ m then 1 / (2 * ((m + 1 : ℕ) : ℚ)) * ∑ k ∈ range (m - j + 1),
    ((m + 1).choose k : ℚ) * bernoulli' k * 2 ^ k * ((m + 1 - k).choose j : ℚ) * (-1) ^ (m - k - j)
  else 0

/-- **Li's coefficient $c_1(0, 0)$.** Li's coefficient $c_1(0, 0)$ equals $\frac{1}{2}$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public theorem liCoeffC1_zero_zero : liCoeffC1 0 0 = 1 / 2 := by
  simp [liCoeffC1]

/-- **Li's coefficients $d_1(m, j)$.** For natural numbers $m$ and $j$,
$d_1(m, j) = \sum_{k=j}^{m} \binom{k}{j} (-1)^{k-j} c_1(m, k)$, where $c_1$ denotes Li's
coefficients $c_1(m, k)$; in particular $d_1(m, j) = 0$ when $j > m$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public def liCoeffD1 (m j : ℕ) : ℚ :=
  ∑ k ∈ Icc j m, (k.choose j : ℚ) * (-1) ^ (k - j) * liCoeffC1 m k

/-- **Li's coefficient $d_1(0, 0)$.** Li's coefficient $d_1(0, 0)$ equals $\frac{1}{2}$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public theorem liCoeffD1_zero_zero : liCoeffD1 0 0 = 1 / 2 := by
  simp [liCoeffD1, liCoeffC1]

/-- **Li's coefficients $b_1(r, m, j, k)$.** These rational numbers, indexed by natural numbers
$r, m, j, k$, are defined by recursion on $r$ from Li's coefficients $c$, $d$, $c_1$ and $d_1$.
All values $b_1(0, m, j, k)$ are $0$, $b_1(1, 0, 0, 2) = 1$, and all other values
$b_1(1, m, j, k)$ are $0$. For $s \ge 1$ let $G = \lfloor (s-1)/2 \rfloor$ and
$b(m, j, k) = b_1(s, m, j, k)$; then $b_1(s+1, m, j, k)$ is $0$ except in the following cases.

If $s$ is odd: for $k = 0$ the value is $\sum_{l=m}^{G} b(l, j, 2)\, c_1(l, m)$ when
$1 \le m \le G$ and $j \le G - m$, and $\sum_{l=0}^{G-j} b(l, j, 2)\, c_1(l, 0)$ when $m = 0$ and
$j \le G$. For $k = 1$ the value is $\sum_{l=m-1}^{G-1} b(l, j, 3)\, c(l, m)$ when
$1 \le m \le G$ and $j \le G - m$, and $S_1 + S_2 + b(0, j, 3) - S_3$ when $m = 0$ and $j \le G$,
where $S_1$ is the sum of $b(m', j_1, 2)\, d_1(m', j - j_1)$ over the pairs of natural numbers
$(m', j_1)$ with $m' \le G$, $j_1 \le G - m'$, $j_1 < j$ and $j - j_1 \le m'$,
$S_2 = \sum_{m'=0}^{G-j} b(m', j, 2)\, d_1(m', 0)$, and $S_3$ is the sum of
$b(m', j_1, 3)\, d(m', j - j_1)$ over the pairs with $m' < G$, $j_1 < G - m'$, $j_1 < j$ and
$j - j_1 \le m' + 1$.

If $s$ is even: for $k = 2$ the value is $\sum_{l=m-1}^{G} b(l, j, 0)\, c(l, m)$ when
$1 \le m \le G + 1$ and $j \le G + 1 - m$, and $-T_1 + T_2 + b(0, j, 0) + T_3$ when $m = 0$ and
$j \le G + 1$, where $T_1$ is the sum of $b(m', j_1, 0)\, d(m', j - j_1)$ over the pairs of
natural numbers $(m', j_1)$ with $m' \le G$, $j_1 \le G - m'$, $j_1 < j$ and $j - j_1 \le m' + 1$,
$T_2$ is the sum of $b(m', j, 1)\, d_1(m', 0)$ over $0 \le m' \le \max(G - j, 0)$, and $T_3$ is
the sum of $b(m', j_1, 1)\, d_1(m', j - j_1)$ over the pairs with $m' \le G$, $j_1 \le G - m'$,
$j_1 < j$ and $j - j_1 \le m'$. For $k = 3$ the value is $\sum_{l=m}^{G} b(l, j, 1)\, c_1(l, m)$
when $1 \le m \le G$ and $j \le G - m$, and $\sum_{l=0}^{G-j} b(l, j, 1)\, c_1(l, 0)$ when
$m = 0$ and $j \le G$.

In particular $b_1(r, m, j, 0) = b_1(r, m, j, 1) = 0$ for odd $r$,
$b_1(r, m, j, 2) = b_1(r, m, j, 3) = 0$ for even $r$, and $b_1(r, m, j, 3) = 0$ for odd $r$ when
$m + j = \lfloor (r-1)/2 \rfloor$. In Lemma 6 the second argument of $b_1$ is the exponent of $n$
and the third is the shift of $p$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 5 (with `c, d, c₁, d₁` from Definition 4). -/
public def liCoeffB1 : ℕ → ℕ → ℕ → ℕ → ℚ
  | 0, _, _, _ => 0
  | 1, m, j, k => if m = 0 ∧ j = 0 ∧ k = 2 then 1 else 0
  | r + 2, m, j, k =>
    let G := r / 2
    let P := liCoeffB1 (r + 1)
    if r % 2 = 0 then
      -- the paper's `r = r + 1` is odd: new values of types 0 and 1
      if k = 0 then
        if 1 ≤ m ∧ m ≤ G ∧ j ≤ G - m then ∑ l ∈ Icc m G, P l j 2 * liCoeffC1 l m
        else if m = 0 ∧ j ≤ G then ∑ l ∈ range (G - j + 1), P l j 2 * liCoeffC1 l 0
        else 0
      else if k = 1 then
        if 1 ≤ m ∧ m ≤ G ∧ j ≤ G - m then ∑ l ∈ Icc (m - 1) (G - 1), P l j 3 * liCoeffC l m
        else if m = 0 ∧ j ≤ G then
          (∑ m' ∈ range (G + 1), ∑ j₁ ∈ range (G - m' + 1),
              if j₁ < j ∧ j - j₁ ≤ m' then P m' j₁ 2 * liCoeffD1 m' (j - j₁) else 0) +
            (∑ m' ∈ range (G - j + 1), P m' j 2 * liCoeffD1 m' 0) + P 0 j 3 -
            ∑ m' ∈ range G, ∑ j₁ ∈ range (G - m'),
              if j₁ < j ∧ j - j₁ ≤ m' + 1 then P m' j₁ 3 * liCoeffD m' (j - j₁) else 0
        else 0
      else 0
    else
      -- the paper's `r = r + 1` is even: new values of types 2 and 3
      if k = 2 then
        if 1 ≤ m ∧ m ≤ G + 1 ∧ j ≤ G + 1 - m then ∑ l ∈ Icc (m - 1) G, P l j 0 * liCoeffC l m
        else if m = 0 ∧ j ≤ G + 1 then
          -(∑ m' ∈ range (G + 1), ∑ j₁ ∈ range (G - m' + 1),
              if j₁ < j ∧ j - j₁ ≤ m' + 1 then P m' j₁ 0 * liCoeffD m' (j - j₁) else 0) +
            (∑ m' ∈ range (G - j + 1), P m' j 1 * liCoeffD1 m' 0) + P 0 j 0 +
            ∑ m' ∈ range (G + 1), ∑ j₁ ∈ range (G - m' + 1),
              if j₁ < j ∧ j - j₁ ≤ m' then P m' j₁ 1 * liCoeffD1 m' (j - j₁) else 0
        else 0
      else if k = 3 then
        if 1 ≤ m ∧ m ≤ G ∧ j ≤ G - m then ∑ l ∈ Icc m G, P l j 1 * liCoeffC1 l m
        else if m = 0 ∧ j ≤ G then ∑ l ∈ range (G - j + 1), P l j 1 * liCoeffC1 l 0
        else 0
      else 0

/-- **The coefficient $b_1(1, 0, 0, 2)$.** The coefficient $b_1(1, 0, 0, 2)$ of Li's
Definition 5 equals $1$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 5. -/
public theorem liCoeffB1_one_zero_zero_two : liCoeffB1 1 0 0 2 = 1 := by
  simp [liCoeffB1]

/-- **The coefficient $b_1(1, 0, 0, 3)$.** The coefficient $b_1(1, 0, 0, 3)$ of Li's
Definition 5 equals $0$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 5. -/
public theorem liCoeffB1_one_zero_zero_three : liCoeffB1 1 0 0 3 = 0 := by
  simp [liCoeffB1]


/-- **Asymptotic of generalized hyperharmonic numbers.** For a natural number $p$ let
$H_n^{(p)} = \sum_{i=1}^{n} 1/i^p$ be the generalized harmonic numbers, and let the generalized
hyperharmonic numbers be $H_n^{(p,1)} = H_n^{(p)}$ and $H_n^{(p,r+1)} = \sum_{k=1}^{n} H_k^{(p,r)}$.
Then for all natural numbers $p \ge 2$ and $r \ge 1$, $H_n^{(p,r)} \sim n^{r-1} \zeta(p) / (r-1)!$
as $n \to \infty$, where $\zeta(p) = \sum_{i \ge 1} 1/i^p$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 2 (`jis-2024-24.4.1-lem-2`). -/
public theorem_wanted generalizedHyperharmonic_isEquivalent {p r : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ r) :
    (fun n : ℕ => signedIteratedPartialSum false (generalizedHarmonic p) r n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (r - 1) * (∑' i : ℕ, 1 / (i : ℝ) ^ p) / (r - 1).factorial

/-- **Explicit formula for type II alternating hyperharmonic numbers.** For real $s$ write
$\overline{H}_n^{(s)} = \sum_{i=1}^{n} (-1)^{i-1}/i^s$ for the alternating generalized harmonic
numbers. For a natural number $p$, the type II generalized alternating hyperharmonic numbers are
$H_n^{(p,1,2)} = \overline{H}_n^{(p)}$ and $H_n^{(p,r+1,2)} = \sum_{k=1}^{n} H_k^{(p,r,2)}$. Let
$a(r, m, j)$ be Li's rational coefficients. Then for all natural numbers $r, n, p \ge 1$,
$$
H_n^{(p,r,2)} = \sum_{m=0}^{r-1} \sum_{j=0}^{r-1-m} a(r, m, j)\, n^j\, \overline{H}_n^{(p-m)},
$$
where the index $p - m$ is a real number and may be negative.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3 (`jis-2024-24.4.1-lem-3`). -/
public theorem_wanted alternatingHyperharmonic_typeII_eq_sum {r n p : ℕ} (hr : 1 ≤ r)
    (hn : 1 ≤ n) (hp : 1 ≤ p) :
    signedIteratedPartialSum false (alternatingGeneralizedHarmonic p) r n =
      ∑ m ∈ range r, ∑ j ∈ range (r - m),
        (liCoeffA r m j : ℝ) * (n : ℝ) ^ j * alternatingGeneralizedHarmonic ((p : ℝ) - m) n

/-- **Explicit formulas for type I and type III alternating hyperharmonic numbers.** For real $s$
write $H_n^{(s)} = \sum_{i=1}^{n} 1/i^s$ and $\overline{H}_n^{(s)} = \sum_{i=1}^{n} (-1)^{i-1}/i^s$
for the generalized and the alternating generalized harmonic numbers. For a natural number $p$,
the type I and type III generalized alternating hyperharmonic numbers are
$H_n^{(p,1,1)} = H_n^{(p)}$, $H_n^{(p,1,3)} = \overline{H}_n^{(p)}$ and, for $i = 1, 3$,
$H_n^{(p,r+1,i)} = \sum_{k=1}^{n} (-1)^{k-1} H_k^{(p,r,i)}$. Let $b_1(r, j, m, k)$ for
$k = 0, 1, 2, 3$ be Li's rational coefficients. Then for all natural numbers $r, n, p \ge 1$,
with $g = \lfloor (r-1)/2 \rfloor$ and $\varepsilon_n = (-1)^{n-1}$,
$$
H_n^{(p,r,1)} = \sum_{m=0}^{g} \sum_{j=0}^{g-m} \bigl(b_1(r,j,m,0)\,\varepsilon_n H_n^{(p-m)} +
b_1(r,j,m,1)\,\overline{H}_n^{(p-m)} + b_1(r,j,m,2)\,H_n^{(p-m)} +
b_1(r,j,m,3)\,\varepsilon_n \overline{H}_n^{(p-m)}\bigr)\, n^j
$$
and
$$
H_n^{(p,r,3)} = \sum_{m=0}^{g} \sum_{j=0}^{g-m} \bigl(b_1(r,j,m,0)\,\varepsilon_n
\overline{H}_n^{(p-m)} + b_1(r,j,m,1)\,H_n^{(p-m)} + b_1(r,j,m,2)\,\overline{H}_n^{(p-m)} +
b_1(r,j,m,3)\,\varepsilon_n H_n^{(p-m)}\bigr)\, n^j,
$$
where the index $p - m$ is a real number and may be negative.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 6 (`jis-2024-24.4.1-lem-6`). -/
public theorem_wanted alternatingHyperharmonic_typeI_typeIII_eq_sum {r n p : ℕ} (hr : 1 ≤ r)
    (hn : 1 ≤ n) (hp : 1 ≤ p) :
    let H := fun m : ℕ => generalizedHarmonic ((p : ℝ) - m) n
    let Hb := fun m : ℕ => alternatingGeneralizedHarmonic ((p : ℝ) - m) n
    let s : ℝ := (-1) ^ (n - 1)
    signedIteratedPartialSum true (generalizedHarmonic p) r n =
        ∑ m ∈ range ((r - 1) / 2 + 1), ∑ j ∈ range ((r - 1) / 2 - m + 1),
          ((liCoeffB1 r j m 0 : ℝ) * s * H m + (liCoeffB1 r j m 1 : ℝ) * Hb m +
            (liCoeffB1 r j m 2 : ℝ) * H m + (liCoeffB1 r j m 3 : ℝ) * s * Hb m) * (n : ℝ) ^ j ∧
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic p) r n =
        ∑ m ∈ range ((r - 1) / 2 + 1), ∑ j ∈ range ((r - 1) / 2 - m + 1),
          ((liCoeffB1 r j m 0 : ℝ) * s * Hb m + (liCoeffB1 r j m 1 : ℝ) * H m +
            (liCoeffB1 r j m 2 : ℝ) * Hb m + (liCoeffB1 r j m 3 : ℝ) * s * H m) * (n : ℝ) ^ j

/-- **Asymptotics of type I alternating hyperharmonic numbers.** For real $s$ let
$H_n^{(s)} = \sum_{i=1}^{n} 1/i^s$ be the generalized harmonic numbers, and let the type I
generalized alternating hyperharmonic numbers be $H_n^{(s,1,1)} = H_n^{(s)}$ and
$H_n^{(s,r+1,1)} = \sum_{k=1}^{n} (-1)^{k-1} H_k^{(s,r,1)}$. Let $y \ge 1$ and $p \ge 2$ be natural
numbers, let $\zeta(p) = \sum_{i \ge 1} 1/i^p$ and let $\bar\zeta(p)$ be the alternating zeta
value at $p$. Then, as $n \to \infty$,
$H_n^{(1,2y+1,1)} \sim n^y \log n / (2^y\, y!)$,
$H_n^{(p,2y+1,1)} \sim n^y \zeta(p) / (2^y\, y!)$,
$H_n^{(1,2y,1)} \sim (-1)^{n-1} n^{y-1} \log n / (2^y (y-1)!)$,
$H_{2n}^{(p,2y,1)} \sim -n^{y-1} (\zeta(p) - \bar\zeta(p)) / (2\,(y-1)!)$ and
$H_{2n-1}^{(p,2y,1)} \sim n^{y-1} (\zeta(p) + \bar\zeta(p)) / (2\,(y-1)!)$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 10 (`jis-2024-24.4.1-lem-10`). -/
public theorem_wanted alternatingHyperharmonic_typeI_isEquivalent {y p : ℕ} (hy : 1 ≤ y)
    (hp : 2 ≤ p) :
    let HI := fun (s : ℝ) (r n : ℕ) => signedIteratedPartialSum true (generalizedHarmonic s) r n
    let ζp : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ p
    ((fun n : ℕ => HI 1 (2 * y + 1) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ y * Real.log n / ((2 ^ y * y.factorial : ℕ) : ℝ)) ∧
    ((fun n : ℕ => HI p (2 * y + 1) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ y * ζp / ((2 ^ y * y.factorial : ℕ) : ℝ)) ∧
    ((fun n : ℕ => HI 1 (2 * y) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * (-1) ^ (n - 1) * Real.log n /
        ((2 ^ y * (y - 1).factorial : ℕ) : ℝ)) ∧
    ((fun n : ℕ => HI p (2 * y) (2 * n)) ~[atTop]
      fun n : ℕ => -((n : ℝ) ^ (y - 1) * (ζp - alternatingZeta p) /
        ((2 * (y - 1).factorial : ℕ) : ℝ))) ∧
    ((fun n : ℕ => HI p (2 * y) (2 * n - 1)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * (ζp + alternatingZeta p) /
        ((2 * (y - 1).factorial : ℕ) : ℝ))

/-- **Asymptotic of type II alternating hyperharmonic numbers.** For a natural number $p$ let
$\overline{H}_n^{(p)} = \sum_{i=1}^{n} (-1)^{i-1}/i^p$ be the alternating generalized harmonic
numbers, and let the type II generalized alternating hyperharmonic numbers be
$H_n^{(p,1,2)} = \overline{H}_n^{(p)}$ and $H_n^{(p,r+1,2)} = \sum_{k=1}^{n} H_k^{(p,r,2)}$. Let
$\bar\zeta(p)$ be the alternating zeta value at $p$, so that $\bar\zeta(1) = \log 2$. Then for all
natural numbers $r, p \ge 1$, $H_n^{(p,r,2)} \sim n^{r-1} \bar\zeta(p) / (r-1)!$ as $n \to \infty$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 13 (`jis-2024-24.4.1-lem-13`). -/
public theorem_wanted alternatingHyperharmonic_typeII_isEquivalent {r p : ℕ} (hr : 1 ≤ r)
    (hp : 1 ≤ p) :
    (fun n : ℕ => signedIteratedPartialSum false (alternatingGeneralizedHarmonic p) r n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (r - 1) * alternatingZeta p / (r - 1).factorial

/-- **Asymptotics of type III alternating hyperharmonic numbers.** For real $s$ let
$\overline{H}_n^{(s)} = \sum_{i=1}^{n} (-1)^{i-1}/i^s$ be the alternating generalized harmonic
numbers, and let the type III generalized alternating hyperharmonic numbers be
$H_n^{(s,1,3)} = \overline{H}_n^{(s)}$ and
$H_n^{(s,r+1,3)} = \sum_{k=1}^{n} (-1)^{k-1} H_k^{(s,r,3)}$. Let $y \ge 1$ and $p \ge 1$ be natural
numbers and let $\bar\zeta(p)$ be the alternating zeta value at $p$. Then, as $n \to \infty$,
$H_n^{(p,2y+1,3)} \sim n^y \bar\zeta(p) / (2^y\, y!)$ and
$H_n^{(1,2y,3)} \sim n^{y-1} \log n / (2^y (y-1)!)$. If moreover $p \ge 2$, then, with
$\zeta(p) = \sum_{i \ge 1} 1/i^p$, as $n \to \infty$,
$H_{2n}^{(p,2y,3)} \sim n^{y-1} (\zeta(p) - \bar\zeta(p)) / (2\,(y-1)!)$ and
$H_{2n-1}^{(p,2y,3)} \sim n^{y-1} (\zeta(p) + \bar\zeta(p)) / (2\,(y-1)!)$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 16 (`jis-2024-24.4.1-lem-16`). -/
public theorem_wanted alternatingHyperharmonic_typeIII_isEquivalent {y p : ℕ} (hy : 1 ≤ y)
    (hp : 1 ≤ p) :
    let HIII := fun (s : ℝ) (r n : ℕ) =>
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) r n
    let ζp : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ p
    ((fun n : ℕ => HIII p (2 * y + 1) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ y * alternatingZeta p / ((2 ^ y * y.factorial : ℕ) : ℝ)) ∧
    ((fun n : ℕ => HIII 1 (2 * y) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * Real.log n / ((2 ^ y * (y - 1).factorial : ℕ) : ℝ)) ∧
    (2 ≤ p → (fun n : ℕ => HIII p (2 * y) (2 * n)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * (ζp - alternatingZeta p) /
        ((2 * (y - 1).factorial : ℕ) : ℝ)) ∧
    (2 ≤ p → (fun n : ℕ => HIII p (2 * y) (2 * n - 1)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * (ζp + alternatingZeta p) /
        ((2 * (y - 1).factorial : ℕ) : ℝ))

/-- **Mixed hyperharmonic product sums over squarefree numbers with $k$ prime factors.** Let
$q_1 \ge 2$ and $q_2, \alpha, \beta, m, k, s, n, r_1, r_2 \ge 1$ be natural numbers. Let
$p_{\ell,k}$ be the $\ell$th ($\ell \ge 1$) squarefree number with exactly $k$ prime factors.
Write $H_\ell^{(q)} = \sum_{j=1}^{\ell} j^{-q}$ and
$\bar H_\ell^{(q)} = \sum_{j=1}^{\ell} (-1)^{j-1} j^{-q}$; let $H_\ell^{(q,1)} = H_\ell^{(q)}$ and
$H_\ell^{(q,r+1)} = \sum_{j=1}^{\ell} H_j^{(q,r)}$, and define $H_\ell^{(q,r,2)}$ by the same
recursion from $H_\ell^{(q,1,2)} = \bar H_\ell^{(q)}$. Let $h_\ell^{(t)}$ be the hyperharmonic
numbers, $h_\ell^{(0)} = 1/\ell$ and $h_\ell^{(t+1)} = \sum_{j=1}^{\ell} h_j^{(t)}$. Let
$\zeta(q) = \sum_{i \ge 1} i^{-q}$ for $q \ge 2$, and let $\bar\zeta(q_2)$ be $\log 2$ if
$q_2 = 1$ and $(1 - 2^{1-q_2}) \zeta(q_2)$ otherwise. Put
$f(\ell) = p_{\ell,k}^{\alpha} (H_\ell^{(q_1,r_1)})^m (h_\ell^{(s)})^n
(H_\ell^{(q_2,r_2,2)})^\beta$,
$E = m(r_1 - 1) + n(s - 1) + \beta(r_2 - 1)$, $A = \alpha + E + 1$,
$D = ((r_1 - 1)!)^m ((s - 1)!)^n ((r_2 - 1)!)^\beta$ and $Z = \zeta(q_1)^m \bar\zeta(q_2)^\beta$.
Then, as the natural number $x$ tends to infinity,
$$\sum_{\ell=1}^{x} f(\ell) \sim
\frac{((k-1)!)^\alpha Z x^A (\log x)^{\alpha+n}}{A D (\log\log x)^{\alpha(k-1)}}$$
and
$$\sum_{1 \le \ell \le x,\ p_{\ell,k} \le x} f(\ell) \sim
\frac{Z x^A (\log\log x)^{(E+1)(k-1)}}{A D ((k-1)!)^{E+1}
(\log x)^{m(r_1-1)+n(s-2)+\beta(r_2-1)+1}}.$$

The exponent of $\log x$ in the second formula is an integer, which is negative for some
parameters with $s = 1$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 15 (`jis-2024-24.4.1-thm-15`). -/
public theorem_wanted sum_squarefreeKPrime_pow_mul_hyperharmonic_products_isEquivalent
    {q₁ q₂ α β m k s n r₁ r₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 1 ≤ q₂) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hs : 1 ≤ s) (hn : 1 ≤ n) (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) :
    let pk : ℕ → ℕ := fun l =>
      Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1)
    let f : ℕ → ℝ := fun l =>
      (pk l : ℝ) ^ α * (signedIteratedPartialSum false (generalizedHarmonic q₁) r₁ l) ^ m *
        (hyperharmonic s l : ℝ) ^ n *
        (signedIteratedPartialSum false (alternatingGeneralizedHarmonic q₂) r₂ l) ^ β
    let E : ℕ := m * (r₁ - 1) + n * (s - 1) + β * (r₂ - 1)
    let Z : ℝ := (∑' i : ℕ, 1 / (i : ℝ) ^ q₁) ^ m * alternatingZeta q₂ ^ β
    let D : ℝ := ((r₁ - 1).factorial : ℝ) ^ m * ((s - 1).factorial : ℝ) ^ n *
      ((r₂ - 1).factorial : ℝ) ^ β
    ((fun x : ℕ => ∑ l ∈ Icc 1 x, f l) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * Z * Real.log x ^ (α + n) *
        (x : ℝ) ^ (α + E + 1) /
          (D * ((α + E + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x), f l) ~[atTop]
      fun x : ℕ => Z * (x : ℝ) ^ (α + E + 1) * Real.log (Real.log x) ^ ((E + 1) * (k - 1)) /
        (((α + E + 1 : ℕ) : ℝ) * D * ((k - 1).factorial : ℝ) ^ (E + 1) *
          Real.log x ^ ((m : ℤ) * ((r₁ : ℤ) - 1) + (n : ℤ) * ((s : ℤ) - 2) +
            (β : ℤ) * ((r₂ : ℤ) - 1) + 1)))

/-- **Prime-weighted power sums of type I alternating hyperharmonic numbers.** Let
$\alpha, m, y \ge 1$ and $q \ge 2$ be integers. Let $p_\ell$ be the $\ell$-th prime ($p_1 = 2$),
let $H_n^{(s,r,1)}$ be the signed iterated partial sum of order $r$, with alternating signs, of the
generalized harmonic numbers $H_n^{(s)} = \sum_{j=1}^{n} j^{-s}$, let
$\zeta(q) = \sum_{n \ge 1} n^{-q}$, and let $\bar\zeta$ be the alternating zeta function. For a
real sequence $f$ write
$$S_x(f) = \sum_{\ell=1}^{x} p_\ell^\alpha f(\ell)^m, \qquad
T_x(f) = \sum_{\substack{1 \le \ell \le x \\ p_\ell \le x}} p_\ell^\alpha f(\ell)^m,$$
put $E = my + 1$, $F = m(y-1) + 1$, $A = \alpha + E$ and $B = \alpha + F$, and let
$f_1(\ell) = H_\ell^{(1,2y+1,1)}$, $f_2(\ell) = H_\ell^{(q,2y+1,1)}$,
$f_3(\ell) = (-1)^{\ell-1} H_\ell^{(1,2y,1)}$, $f_4(\ell) = H_{2\ell-1}^{(1,2y,1)}$,
$f_5(\ell) = -H_{2\ell}^{(1,2y,1)}$, $f_6(\ell) = H_{2\ell-1}^{(q,2y,1)}$ and
$f_7(\ell) = -H_{2\ell}^{(q,2y,1)}$. Then, as the natural number $x$ tends to infinity,
$$S_x(f_1) \sim \frac{x^A (\log x)^{\alpha+m}}{(2^y y!)^m A}, \qquad
T_x(f_1) \sim \frac{x^A}{(2^y y!)^m A (\log x)^{m(y-1)+1}},$$
$$S_x(f_2) \sim \frac{\zeta(q)^m x^A (\log x)^\alpha}{(2^y y!)^m A}, \qquad
T_x(f_2) \sim \frac{\zeta(q)^m x^A}{(2^y y!)^m A (\log x)^E},$$
$$S_x(f_3) \sim \frac{x^B (\log x)^{\alpha+m}}{(2^y (y-1)!)^m B}, \qquad
T_x(f_3) \sim \frac{x^B}{(2^y (y-1)!)^m B (\log x)^{m(y-2)+1}},$$
for $i = 4, 5$
$$S_x(f_i) \sim \frac{x^B (\log x)^{\alpha+m}}{(2 (y-1)!)^m B}, \qquad
T_x(f_i) \sim \frac{x^B}{(2 (y-1)!)^m B (\log x)^{m(y-2)+1}},$$
and
$$S_x(f_6) \sim \frac{(\zeta(q) + \bar\zeta(q))^m x^B (\log x)^\alpha}{(2 (y-1)!)^m B}, \qquad
T_x(f_6) \sim \frac{(\zeta(q) + \bar\zeta(q))^m x^B}{(2 (y-1)!)^m B (\log x)^F},$$
$$S_x(f_7) \sim \frac{(\zeta(q) - \bar\zeta(q))^m x^B (\log x)^\alpha}{(2 (y-1)!)^m B}, \qquad
T_x(f_7) \sim \frac{(\zeta(q) - \bar\zeta(q))^m x^B}{(2 (y-1)!)^m B (\log x)^F}.$$

The exponent $m(y-2)+1$ of $\log x$ may be negative; the power is then an integer power.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 11 (`jis-2024-24.4.1-thm-11`). -/
public theorem_wanted sum_primes_pow_mul_alternatingHyperharmonic_typeI_isEquivalent
    {α m q y : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hy : 1 ≤ y) (hq : 2 ≤ q) :
    let pr : ℕ → ℕ := fun l => Nat.nth Nat.Prime (l - 1)
    let ζq : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ q
    let HI := fun (s : ℝ) (r n : ℕ) => signedIteratedPartialSum true (generalizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HI 1 (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α + m) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HI 1 (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * y + 1) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HI q (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ζq ^ m * (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HI q (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ζq ^ m * (x : ℝ) ^ (α + m * y + 1) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * y + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * ((-1 : ℝ) ^ (l - 1) * HI 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α + m) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * ((-1 : ℝ) ^ (l - 1) * HI 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HI 1 (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α + m) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (-HI 1 (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α + m) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HI 1 (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (-HI 1 (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HI q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HI q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (-HI q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (-HI q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (y - 1) + 1)))

/-- **Type I alternating hyperharmonic power sums weighted by squarefree $k$-prime numbers.** Let
$\alpha, m, k, y \ge 1$ and $q \ge 2$ be integers. Let $p_{\ell,k}$ be the $\ell$-th squarefree
number with exactly $k$ prime factors, let $H_n^{(s,r,1)}$ be the signed iterated partial sum of
order $r$, with alternating signs, of the generalized harmonic numbers
$H_n^{(s)} = \sum_{j=1}^{n} j^{-s}$, let $\zeta(q) = \sum_{n \ge 1} n^{-q}$, and let $\bar\zeta$ be
the alternating zeta function. For a real sequence $f$ write
$$S_x(f) = \sum_{\ell=1}^{x} p_{\ell,k}^\alpha f(\ell)^m, \qquad
T_x(f) = \sum_{\substack{1 \le \ell \le x \\ p_{\ell,k} \le x}} p_{\ell,k}^\alpha f(\ell)^m,$$
put $K = (k-1)!$, $E = my + 1$, $F = m(y-1) + 1$, $A = \alpha + E$ and $B = \alpha + F$, and let
$f_1(\ell) = H_\ell^{(1,2y+1,1)}$, $f_2(\ell) = H_\ell^{(q,2y+1,1)}$,
$f_3(\ell) = (-1)^{\ell-1} H_\ell^{(1,2y,1)}$, $f_4(\ell) = H_{2\ell-1}^{(1,2y,1)}$,
$f_5(\ell) = -H_{2\ell}^{(1,2y,1)}$, $f_6(\ell) = H_{2\ell-1}^{(q,2y,1)}$ and
$f_7(\ell) = -H_{2\ell}^{(q,2y,1)}$. Then, as the natural number $x$ tends to infinity,
$$S_x(f_1) \sim \frac{K^\alpha x^A (\log x)^{\alpha+m}}{(2^y y!)^m A (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_1) \sim
\frac{x^A (\log \log x)^{E(k-1)}}{(2^y y!)^m K^E A (\log x)^{m(y-1)+1}},$$
$$S_x(f_2) \sim
\frac{K^\alpha \zeta(q)^m x^A (\log x)^\alpha}{(2^y y!)^m A (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_2) \sim
\frac{\zeta(q)^m x^A (\log \log x)^{E(k-1)}}{(2^y y!)^m K^E A (\log x)^E},$$
$$S_x(f_3) \sim
\frac{K^\alpha x^B (\log x)^{\alpha+m}}{(2^y (y-1)!)^m B (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_3) \sim
\frac{x^B (\log \log x)^{F(k-1)}}{(2^y (y-1)!)^m K^F B (\log x)^{m(y-2)+1}},$$
for $i = 4, 5$
$$S_x(f_i) \sim
\frac{K^\alpha x^B (\log x)^{\alpha+m}}{(2 (y-1)!)^m B (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_i) \sim
\frac{x^B (\log \log x)^{F(k-1)}}{(2 (y-1)!)^m K^F B (\log x)^{m(y-2)+1}},$$
and
$$S_x(f_6) \sim \frac{K^\alpha (\zeta(q) + \bar\zeta(q))^m x^B (\log x)^\alpha}
{(2 (y-1)!)^m B (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_6) \sim \frac{(\zeta(q) + \bar\zeta(q))^m x^B (\log \log x)^{F(k-1)}}
{(2 (y-1)!)^m K^F B (\log x)^F},$$
$$S_x(f_7) \sim \frac{K^\alpha (\zeta(q) - \bar\zeta(q))^m x^B (\log x)^\alpha}
{(2 (y-1)!)^m B (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_7) \sim \frac{(\zeta(q) - \bar\zeta(q))^m x^B (\log \log x)^{F(k-1)}}
{(2 (y-1)!)^m K^F B (\log x)^F}.$$

The exponent $m(y-2)+1$ of $\log x$ may be negative; the power is then an integer power.

The paper prints the second sum of its seventh item,
$\sum p_{\ell,k}^\alpha (-H_{2\ell}^{(1,2y,1)})^m$, over $p_{\ell,k} \le x$ but gives it the
asymptotic of a sum over $\ell \le x$, and the version over $p_{\ell,k} \le x$ is its eighth item;
it is read here as $S_x(f_5)$, a sum over $\ell \le x$, as in Theorem 11.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 12 (`jis-2024-24.4.1-thm-12`). -/
public theorem_wanted sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeI_isEquivalent
    {α m k q y : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hk : 1 ≤ k) (hy : 1 ≤ y) (hq : 2 ≤ q) :
    let pk : ℕ → ℕ := fun l =>
      Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1)
    let ζq : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ q
    let HI := fun (s : ℝ) (r n : ℕ) => signedIteratedPartialSum true (generalizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HI 1 (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α + m) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HI 1 (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * y + 1) * Real.log (Real.log x) ^ ((m * y + 1) * (k - 1)) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * y + 1) *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HI q (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * ζq ^ m *
        (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HI q (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ζq ^ m * (x : ℝ) ^ (α + m * y + 1) *
        Real.log (Real.log x) ^ ((m * y + 1) * (k - 1)) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * y + 1) *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log x ^ (m * y + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * ((-1 : ℝ) ^ (l - 1) * HI 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α + m) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * ((-1 : ℝ) ^ (l - 1) * HI 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
            ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HI 1 (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α + m) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (-HI 1 (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α + m) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HI 1 (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (-HI 1 (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HI q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (ζq + alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HI q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (-HI q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (ζq - alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (-HI q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1)))

/-- **Prime- and squarefree-weighted power sums of type II alternating hyperharmonic numbers.**
Let $\alpha, m, q, k, r \ge 1$ be integers. Let $p_\ell$ be the $\ell$-th prime ($p_1 = 2$) and
$p_{\ell,k}$ the $\ell$-th squarefree number with exactly $k$ prime factors. Let
$H_n^{(q,r,2)}$ be the signed iterated partial sum of order $r$, with constant signs, of the
alternating generalized harmonic numbers $\bar H_n^{(q)} = \sum_{j=1}^{n} (-1)^{j-1} j^{-q}$, and
let $\bar\zeta$ be the alternating zeta function ($\bar\zeta(1) = \log 2$). Put
$E = m(r-1) + 1$ and $A = \alpha + E$. Then, as the natural number $x$ tends to infinity,
$$\sum_{\ell=1}^{x} p_\ell^\alpha \bigl(H_\ell^{(q,r,2)}\bigr)^m \sim
\frac{\bar\zeta(q)^m x^A (\log x)^\alpha}{((r-1)!)^m A},$$
$$\sum_{\substack{1 \le \ell \le x \\ p_\ell \le x}} p_\ell^\alpha \bigl(H_\ell^{(q,r,2)}\bigr)^m
\sim \frac{\bar\zeta(q)^m x^A}{((r-1)!)^m A (\log x)^E},$$
$$\sum_{\ell=1}^{x} p_{\ell,k}^\alpha \bigl(H_\ell^{(q,r,2)}\bigr)^m \sim
\frac{((k-1)!)^\alpha \bar\zeta(q)^m x^A (\log x)^\alpha}
{((r-1)!)^m A (\log \log x)^{\alpha(k-1)}},$$
$$\sum_{\substack{1 \le \ell \le x \\ p_{\ell,k} \le x}} p_{\ell,k}^\alpha
\bigl(H_\ell^{(q,r,2)}\bigr)^m \sim
\frac{\bar\zeta(q)^m x^A (\log \log x)^{E(k-1)}}{((r-1)!)^m ((k-1)!)^E A (\log x)^E}.$$

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 14 (`jis-2024-24.4.1-thm-14`). -/
public theorem_wanted sum_pow_mul_alternatingHyperharmonic_typeII_isEquivalent
    {α m q k r : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hq : 1 ≤ q) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    let pr : ℕ → ℕ := fun l => Nat.nth Nat.Prime (l - 1)
    let pk : ℕ → ℕ := fun l =>
      Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1)
    let HII := fun (s : ℝ) (r n : ℕ) =>
      signedIteratedPartialSum false (alternatingGeneralizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HII q (r) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta q ^ m * (x : ℝ) ^ (α + m * (r - 1) + 1) * Real.log x ^ (α) /
        (((r - 1).factorial : ℝ) ^ m * ((α + m * (r - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HII q (r) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta q ^ m * (x : ℝ) ^ (α + m * (r - 1) + 1) /
        (((r - 1).factorial : ℝ) ^ m * ((α + m * (r - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (r - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HII q (r) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * alternatingZeta q ^ m *
        (x : ℝ) ^ (α + m * (r - 1) + 1) * Real.log x ^ (α) /
        (((r - 1).factorial : ℝ) ^ m * ((α + m * (r - 1) + 1 : ℕ) : ℝ) *
          Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HII q (r) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta q ^ m *
        (x : ℝ) ^ (α + m * (r - 1) + 1) * Real.log (Real.log x) ^ ((m * (r - 1) + 1) * (k - 1)) /
        (((r - 1).factorial : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (r - 1) + 1) *
          ((α + m * (r - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (r - 1) + 1)))

/-- **Prime-weighted power sums of type III alternating hyperharmonic numbers.** Let
$\alpha, m, p, y \ge 1$ and $q \ge 2$ be integers. Let $p_\ell$ be the $\ell$-th prime
($p_1 = 2$), let $H_n^{(s,r,3)}$ be the signed iterated partial sum of order $r$, with alternating
signs, of the alternating generalized harmonic numbers
$\bar H_n^{(s)} = \sum_{j=1}^{n} (-1)^{j-1} j^{-s}$, let $\zeta(q) = \sum_{n \ge 1} n^{-q}$, and
let $\bar\zeta$ be the alternating zeta function ($\bar\zeta(1) = \log 2$). For a real sequence
$f$ write
$$S_x(f) = \sum_{\ell=1}^{x} p_\ell^\alpha f(\ell)^m, \qquad
T_x(f) = \sum_{\substack{1 \le \ell \le x \\ p_\ell \le x}} p_\ell^\alpha f(\ell)^m,$$
put $E = my + 1$, $F = m(y-1) + 1$, $A = \alpha + E$ and $B = \alpha + F$, and let
$f_1(\ell) = H_\ell^{(p,2y+1,3)}$, $f_2(\ell) = H_\ell^{(1,2y,3)}$,
$f_3(\ell) = H_{2\ell-1}^{(q,2y,3)}$ and $f_4(\ell) = H_{2\ell}^{(q,2y,3)}$. Then, as the natural
number $x$ tends to infinity,
$$S_x(f_1) \sim \frac{\bar\zeta(p)^m x^A (\log x)^\alpha}{(2^y y!)^m A}, \qquad
T_x(f_1) \sim \frac{\bar\zeta(p)^m x^A}{(2^y y!)^m A (\log x)^E},$$
$$S_x(f_2) \sim \frac{x^B (\log x)^{\alpha+m}}{(2^y (y-1)!)^m B}, \qquad
T_x(f_2) \sim \frac{x^B}{(2^y (y-1)!)^m B (\log x)^{m(y-2)+1}},$$
$$S_x(f_3) \sim \frac{(\zeta(q) + \bar\zeta(q))^m x^B (\log x)^\alpha}{(2 (y-1)!)^m B}, \qquad
T_x(f_3) \sim \frac{(\zeta(q) + \bar\zeta(q))^m x^B}{(2 (y-1)!)^m B (\log x)^F},$$
$$S_x(f_4) \sim \frac{(\zeta(q) - \bar\zeta(q))^m x^B (\log x)^\alpha}{(2 (y-1)!)^m B}, \qquad
T_x(f_4) \sim \frac{(\zeta(q) - \bar\zeta(q))^m x^B}{(2 (y-1)!)^m B (\log x)^F}.$$

The exponent $m(y-2)+1$ of $\log x$ may be negative; the power is then an integer power.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 17 (`jis-2024-24.4.1-thm-17`). -/
public theorem_wanted sum_primes_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent
    {α m p q y : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hp : 1 ≤ p) (hy : 1 ≤ y) (hq : 2 ≤ q) :
    let pr : ℕ → ℕ := fun l => Nat.nth Nat.Prime (l - 1)
    let ζq : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ q
    let HIII := fun (s : ℝ) (r n : ℕ) =>
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HIII p (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta p ^ m * (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HIII p (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta p ^ m * (x : ℝ) ^ (α + m * y + 1) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * y + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HIII 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α + m) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HIII 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HIII q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HIII q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HIII q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HIII q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (y - 1) + 1)))

/-- **Type III alternating hyperharmonic power sums weighted by squarefree $k$-prime numbers.**
Let $\alpha, m, k, p, y \ge 1$ and $q \ge 2$ be integers. Let $p_{\ell,k}$ be the $\ell$-th
squarefree number with exactly $k$ prime factors, let $H_n^{(s,r,3)}$ be the signed iterated
partial sum of order $r$, with alternating signs, of the alternating generalized harmonic numbers
$\bar H_n^{(s)} = \sum_{j=1}^{n} (-1)^{j-1} j^{-s}$, let $\zeta(q) = \sum_{n \ge 1} n^{-q}$, and
let $\bar\zeta$ be the alternating zeta function ($\bar\zeta(1) = \log 2$). For a real sequence
$f$ write
$$S_x(f) = \sum_{\ell=1}^{x} p_{\ell,k}^\alpha f(\ell)^m, \qquad
T_x(f) = \sum_{\substack{1 \le \ell \le x \\ p_{\ell,k} \le x}} p_{\ell,k}^\alpha f(\ell)^m,$$
put $K = (k-1)!$, $E = my + 1$, $F = m(y-1) + 1$, $A = \alpha + E$ and $B = \alpha + F$, and let
$f_1(\ell) = H_\ell^{(p,2y+1,3)}$, $f_2(\ell) = H_\ell^{(1,2y,3)}$,
$f_3(\ell) = H_{2\ell-1}^{(q,2y,3)}$ and $f_4(\ell) = H_{2\ell}^{(q,2y,3)}$. Then, as the natural
number $x$ tends to infinity,
$$S_x(f_1) \sim
\frac{K^\alpha \bar\zeta(p)^m x^A (\log x)^\alpha}{(2^y y!)^m A (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_1) \sim
\frac{\bar\zeta(p)^m x^A (\log \log x)^{E(k-1)}}{(2^y y!)^m K^E A (\log x)^E},$$
$$S_x(f_2) \sim
\frac{K^\alpha x^B (\log x)^{\alpha+m}}{(2^y (y-1)!)^m B (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_2) \sim
\frac{x^B (\log \log x)^{F(k-1)}}{(2^y (y-1)!)^m K^F B (\log x)^{m(y-2)+1}},$$
$$S_x(f_3) \sim \frac{K^\alpha (\zeta(q) + \bar\zeta(q))^m x^B (\log x)^\alpha}
{(2 (y-1)!)^m B (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_3) \sim \frac{(\zeta(q) + \bar\zeta(q))^m x^B (\log \log x)^{F(k-1)}}
{(2 (y-1)!)^m K^F B (\log x)^F},$$
$$S_x(f_4) \sim \frac{K^\alpha (\zeta(q) - \bar\zeta(q))^m x^B (\log x)^\alpha}
{(2 (y-1)!)^m B (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_4) \sim \frac{(\zeta(q) - \bar\zeta(q))^m x^B (\log \log x)^{F(k-1)}}
{(2 (y-1)!)^m K^F B (\log x)^F}.$$

The exponent $m(y-2)+1$ of $\log x$ may be negative; the power is then an integer power.

The paper prints the first two items with the type I numbers $H_\ell^{(p,2y+1,1)}$, but their
asymptotics carry $\bar\zeta(p)$, the section treats type III, and the proof sums
$H_\ell^{(p,2y+1,3)}$; they are read here with type III.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 18 (`jis-2024-24.4.1-thm-18`). -/
public theorem_wanted sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent
    {α m k p q y : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hk : 1 ≤ k) (hp : 1 ≤ p) (hy : 1 ≤ y) (hq : 2 ≤ q) :
    let pk : ℕ → ℕ := fun l =>
      Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1)
    let ζq : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ q
    let HIII := fun (s : ℝ) (r n : ℕ) =>
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII p (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * alternatingZeta p ^ m *
        (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII p (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta p ^ m * (x : ℝ) ^ (α + m * y + 1) *
        Real.log (Real.log x) ^ ((m * y + 1) * (k - 1)) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * y + 1) *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log x ^ (m * y + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α + m) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
            ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (ζq + alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (ζq - alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1)))


end

end MetaMathlibExt
