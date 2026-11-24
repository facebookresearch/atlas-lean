/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Nat.Choose.Central

/-!
# Power series with reciprocals of central binomial coefficients via `arcsin`

Statements from Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central
Binomial Coefficients*, INTEGERS 26 (2026), Article A2.

The paper's rational polynomials `S_n`, `T_{n-2}`, `M_{n-1}`, `N_{n-2}` and constants `c_n`, `d_n`
(Definitions 1-4) are defined here through their coefficient recursions. The antiderivative
lemmas are stated as derivative identities and the corollaries (the case `m = 1` of the main
theorems) as identities of real functions, both on `0 < x < 1`, where every square root, power
and `arcsin` is the real one.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- **Coefficients of Zurita's polynomial $S_n$.** For a natural number $n$, the rational numbers
$s_0, s_1, s_2, \dots$ are defined by $s_0 = 1/(1/2 - n)$ and
$s_k = \frac{k - 1 - n}{k - n + 1/2}\, s_{k-1}$ for every $k \ge 1$. Their first $n + 1$ terms are
the coefficients of $S_n(x) = \sum_{k=0}^{n} s_k x^k$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 1. -/
def zuritaSCoeff (n : ℕ) : ℕ → ℚ
  | 0 => 1 / (1 / 2 - n)
  | k + 1 => ((k : ℚ) - n) / ((k : ℚ) + 1 - n + 1 / 2) * zuritaSCoeff n k

/-- **Zurita's constant $c_n$.** For a natural number $n$, let $s_n$ be the coefficient of $x^n$
in Zurita's polynomial $S_n(x) = \sum_{k=0}^n s_k x^k$. Then $c_n$ is the rational number
$s_n/2 - 1$. For $n = 1$ this gives $c_1 = 1$, the paper's convention.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
def zuritaC (n : ℕ) : ℚ :=
  zuritaSCoeff n n / 2 - 1

/-- **Reversed coefficients of Zurita's polynomial $T_{n-2}$.** Fix a natural number $n$, let
$s_0, s_1, \dots$ be the coefficients of $S_n$ and let $c_n = s_n/2 - 1$. The rational numbers
$u_0, u_1, \dots$ are defined by $u_0 = -s_{n-1}/2 - c_n$ and
$u_{i+1} = \frac{(k + 1 - n)\, u_i + s_k/2}{k - n}$ with $k = n - 2 - i$, where the index
subtractions $n - 1$ and $n - 2 - i$ are truncated at $0$. For $n \ge 2$ they list the
coefficients of $T_{n-2}$ backwards, $t_{n-2-i} = u_i$ for $0 \le i \le n - 2$; thus
$t_{n-2} = -s_{n-1}/2 - c_n$ and $t_{k-1} = ((k + 1 - n) t_k + s_k/2)/(k - n)$ for
$k = n - 2, \dots, 1$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
def zuritaTCoeffRev (n : ℕ) : ℕ → ℚ
  | 0 => -zuritaSCoeff n (n - 1) / 2 - zuritaC n
  | i + 1 => ((((n - 2 - i : ℕ) : ℚ) + 1 - n) * zuritaTCoeffRev n i +
      zuritaSCoeff n (n - 2 - i) / 2) / (((n - 2 - i : ℕ) : ℚ) - n)

/-- **Coefficients of Zurita's polynomial $T_{n-2}$.** For natural numbers $n$ and $k$,
$t_k = u_{n-2-k}$, where $n - 2 - k$ is truncated at $0$ and $u_0, u_1, \dots$ are the reversed
coefficients of $T_{n-2}$: with $s_j$ the coefficients of $S_n$ and $c_n = s_n/2 - 1$,
$u_0 = -s_{n-1}/2 - c_n$ and $u_{i+1} = ((m + 1 - n) u_i + s_m/2)/(m - n)$ for
$m = n - 2 - i$, the indices $n - 1$ and $n - 2 - i$ being truncated at $0$. For $k \le n - 2$
these are the coefficients of $T_{n-2}(x) = \sum_{k=0}^{n-2} t_k x^k$; for $k > n - 2$,
$t_k = u_0$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
def zuritaTCoeff (n k : ℕ) : ℚ :=
  zuritaTCoeffRev n (n - 2 - k)

/-- **Zurita's coefficients $m_k$.** For a natural number $n$, the rational numbers
$m_0, m_1, \dots$ are defined by $m_0 = 2/(2n - 1)$ and
$m_k = \frac{2(k - n)}{2k - 2n + 1}\, m_{k-1}$ for $k \ge 1$. Zurita's polynomial $M_{n-1}$ is
$M_{n-1}(x) = \sum_{k=0}^{n-1} m_k x^k$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 3. -/
def zuritaMCoeff (n : ℕ) : ℕ → ℚ
  | 0 => 2 / (2 * n - 1)
  | k + 1 => 2 * ((k : ℚ) + 1 - n) / (2 * ((k : ℚ) + 1) - 2 * n + 1) * zuritaMCoeff n k

/-- **Zurita's constant $d_n$.** For a natural number $n$, let $m_0, m_1, \dots$ be Zurita's
coefficients, given by $m_0 = 2/(2n - 1)$ and $m_k = \frac{2(k - n)}{2k - 2n + 1}\, m_{k-1}$ for
$k \ge 1$, so that $M_{n-1}(x) = \sum_{k=0}^{n-1} m_k x^k$ for $n \ge 1$. Then $d_n$ is the
rational number $m_{n-1}/2$ for $n \ge 1$, and $d_0 = m_0/2 = -1$. For $n = 1$ this gives
$d_1 = 1$, the paper's convention.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 4. -/
def zuritaD (n : ℕ) : ℚ :=
  zuritaMCoeff n (n - 1) / 2

/-- **Coefficients of Zurita's polynomial $N_{n-2}$.** For natural numbers $n$ and $k$, let $m_k$
be Zurita's coefficient, given by $m_0 = 2/(2n - 1)$ and
$m_k = \frac{2(k - n)}{2k - 2n + 1}\, m_{k-1}$ for $k \ge 1$. This is the rational number
$m_k / (2(k - n + 1))$, taken to be $0$ when $k = n - 1$. For $k \le n - 2$ it is the
coefficient of $x^k$ in $N_{n-2}(x) = \frac12 \sum_{i=0}^{n-2} \frac{m_i x^i}{i - n + 1}$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 4. -/
def zuritaNCoeff (n k : ℕ) : ℚ :=
  zuritaMCoeff n k / 2 / ((k : ℚ) - n + 1)

/-- **Values from Zurita's Tables 1-4.** For $n = 2$ the coefficients $s_0, s_1, s_2$ of $S_2$ are
$-2/3$, $-8/3$ and $16/3$, and the constants $c_2$ and $c_4$ equal $5/3$ and $93/35$. For $n = 3$
the coefficients $t_0, t_1$ of $T_1$ are $-1/10$ and $-3/5$, the coefficients $m_0, m_1, m_2$ of
$M_2$ are $2/5$, $8/15$ and $16/15$, the constant $d_3$ equals $8/15$, and the coefficients of
$x^0$ and $x^1$ in $N_1$ are $-3/30$ and $-8/30$.

In polynomial form: $S_2(x) = -2/3 - (8/3)x + (16/3)x^2$, $T_1(x) = -1/10 - (3/5)x$,
$M_2(x) = 2/5 + (8/15)x + (16/15)x^2$ and $N_1(x) = -(8x + 3)/30$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Tables 1-4. -/
theorem zurita_table_values :
    (List.range 3).map (zuritaSCoeff 2) = [-2 / 3, -8 / 3, 16 / 3] ∧ zuritaC 2 = 5 / 3 ∧
      zuritaC 4 = 93 / 35 ∧ (List.range 2).map (zuritaTCoeff 3) = [-1 / 10, -3 / 5] ∧
      (List.range 3).map (zuritaMCoeff 3) = [2 / 5, 8 / 15, 16 / 15] ∧ zuritaD 3 = 8 / 15 ∧
      (List.range 2).map (zuritaNCoeff 3) = [-3 / 30, -8 / 30] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, zuritaC, zuritaD, zuritaTCoeff, zuritaNCoeff]
  norm_num [zuritaSCoeff, zuritaTCoeffRev, zuritaMCoeff, zuritaC]

/-- **Zurita's polynomial $S_n$.** For a natural number $n$ and a real number $x$,
$S_n(x) = \sum_{k=0}^{n} s_k x^k$, where $s_0 = 1/(1/2 - n)$ and
$s_k = \frac{k - 1 - n}{k - n + 1/2}\, s_{k-1}$ for $k \ge 1$ are the coefficients of $S_n$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 1. -/
noncomputable def zuritaS (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (zuritaSCoeff n k : ℝ) * x ^ k

/-- **Zurita's polynomial $T_{n-2}$.** For a natural number $n$ and a real number $x$,
$T_{n-2}(x) = \sum_{k=0}^{n-2} t_k x^k$, where $t_0, t_1, \dots$ are the coefficients of
Zurita's polynomial $T_{n-2}$; for $n \le 1$ the sum is empty and $T_{n-2}(x) = 0$. For
$n \ge 2$ these coefficients are given by $t_{n-2} = -s_{n-1}/2 - c_n$ and
$t_{k-1} = ((k + 1 - n) t_k + s_k/2)/(k - n)$ for $k = n - 2, \dots, 1$, where
$s_0 = 1/(1/2 - n)$ and $s_k = \frac{k - 1 - n}{k - n + 1/2}\, s_{k-1}$ for $k \ge 1$ are the
coefficients of Zurita's polynomial $S_n$, and $c_n = s_n/2 - 1$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
noncomputable def zuritaT (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n - 1), (zuritaTCoeff n k : ℝ) * x ^ k

/-- **Zurita's polynomial $M_{n-1}$.** For a natural number $n$, let $m_0, m_1, \dots$ be Zurita's
coefficients, given by $m_0 = 2/(2n - 1)$ and $m_k = \frac{2(k - n)}{2k - 2n + 1}\, m_{k-1}$ for
$k \ge 1$. Then $M_{n-1}$ is the real polynomial function
$M_{n-1}(x) = \sum_{k=0}^{n-1} m_k x^k$ (so $M_{-1} = 0$).

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 3. -/
noncomputable def zuritaM (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, (zuritaMCoeff n k : ℝ) * x ^ k

/-- **Zurita's polynomial $N_{n-2}$.** For a natural number $n$, let $m_0, m_1, \dots$ be Zurita's
coefficients, given by $m_0 = 2/(2n - 1)$ and $m_k = \frac{2(k - n)}{2k - 2n + 1}\, m_{k-1}$ for
$k \ge 1$. Then $N_{n-2}$ is the real polynomial function
$N_{n-2}(x) = \frac12 \sum_{k=0}^{n-2} \frac{m_k x^k}{k - n + 1}$, which is $0$ for $n \le 1$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 4. -/
noncomputable def zuritaN (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n - 1), (zuritaNCoeff n k : ℝ) * x ^ k

/-- **Zurita's antiderivative of $x^{-n-1/2}\arcsin(\sqrt{x})/(1-x)^{3/2}$.** Let $n \ge 1$, let
$c_n$ be Zurita's constant and let $S_n$ and $T_{n-2}$ be Zurita's polynomials (with
$T_{-1} = 0$). For every real $x$ with $0 < x < 1$, the function
$$
F(y) = \log|y - 1| + c_n \log y + \frac{T_{n-2}(y)}{y^{n-1}} +
\frac{\arcsin(\sqrt{y})\, S_n(y)}{y^{n-1/2} \sqrt{1 - y}}
$$
has derivative $x^{-n-1/2} \arcsin(\sqrt{x}) / (1 - x)^{3/2}$ at $x$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Lemma 1 (`integers-2026-A2-lem-1`). -/
public theorem_wanted hasDerivAt_zurita_antiderivative_one {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => Real.log (y - 1) + (zuritaC n : ℝ) * Real.log y +
        zuritaT n y / y ^ (n - 1) +
        Real.arcsin (Real.sqrt y) * zuritaS n y / (y ^ ((n : ℝ) - 1 / 2) * Real.sqrt (1 - y)))
      (x ^ (-(n : ℝ) - 1 / 2) * Real.arcsin (Real.sqrt x) / (1 - x) ^ ((3 : ℝ) / 2)) x

/-- **Zurita's antiderivative of $x^{-n-1/2}\arcsin(\sqrt{x})/\sqrt{1-x}$.** Let $n \ge 1$, let
$d_n$ be Zurita's constant and let $M_{n-1}$ and $N_{n-2}$ be Zurita's polynomials (with
$N_{-1} = 0$). For every real $x$ with $0 < x < 1$, the function
$$
G(y) = d_n \log y - \frac{\arcsin(\sqrt{y}) \sqrt{y(1 - y)}\, M_{n-1}(y)}{y^n} +
\frac{N_{n-2}(y)}{y^{n-1}}
$$
has derivative $x^{-n-1/2} \arcsin(\sqrt{x}) / \sqrt{1 - x}$ at $x$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Lemma 2 (`integers-2026-A2-lem-2`). -/
public theorem_wanted hasDerivAt_zurita_antiderivative_two {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => (zuritaD n : ℝ) * Real.log y -
        Real.arcsin (Real.sqrt y) * Real.sqrt (y * (1 - y)) * zuritaM n y / y ^ n +
        zuritaN n y / y ^ (n - 1))
      (x ^ (-(n : ℝ) - 1 / 2) * Real.arcsin (Real.sqrt x) / Real.sqrt (1 - x)) x

/-- **Zurita's series $\sum_{k > n} 4^k x^k / ((k - n)\binom{2k}{k})$.** Let $n \ge 1$, let
$S_n(x) = \sum_{k=0}^n s_k x^k$ and $T_{n-2}$ be Zurita's polynomials (with $T_{-1} = 0$), and
let $x$ be real with $0 < x < 1$. Then
$$
\sum_{k > n} \frac{4^k x^k}{(k - n)\binom{2k}{k}} = x\, T_{n-2}(x) +
\sqrt{\frac{x}{1 - x}}\, \arcsin(\sqrt{x})\, S_n(x) +
\sum_{k=0}^{n-1} \Bigl(1 - \frac{4^k}{\binom{2k}{k}}\Bigr) \frac{x^k}{k - n} -
\Bigl(\frac12 \sum_{k=1}^{n} \frac{4^k s_{n-k}}{k \binom{2k}{k}}\Bigr) x^n.
$$

The source prints the range $|x| < 4$. The statement here is restricted to $0 < x < 1$, inside
the range $|x| < 1$ that the source's Theorem 1 gives in this case; since
$\binom{2k}{k} \le 4^k$, the series diverges for $x \ge 1$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Corollary 1 (`integers-2026-A2-cor-1`). -/
public theorem_wanted tsum_four_pow_div_sub_mul_centralBinom {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ∑' k : ℕ, (4 : ℝ) ^ (k + n + 1) * x ^ (k + n + 1) /
        (((k : ℝ) + 1) * Nat.centralBinom (k + n + 1)) =
      x * zuritaT n x + Real.sqrt (x / (1 - x)) * Real.arcsin (Real.sqrt x) * zuritaS n x +
        ∑ k ∈ range n, (1 - (4 : ℝ) ^ k / Nat.centralBinom k) * x ^ k / ((k : ℝ) - n) -
        (1 / 2 * ∑ k ∈ Icc 1 n, (4 : ℝ) ^ k * (zuritaSCoeff n (n - k) : ℝ) /
          ((k : ℝ) * Nat.centralBinom k)) * x ^ n

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
          1 / 2 * ∑ p ∈ Icc 1 (n - l - 1), (4 : ℝ) ^ p * (zuritaMCoeff (n - l) (n - l - 1 - p) : ℝ) /
            ((p : ℝ) * (2 * p + 1) * Nat.centralBinom p))
    ∑' k : ℕ, (4 : ℝ) ^ (k + n + 1) * x ^ (k + n + 1) /
        (((k : ℝ) + 1) ^ 2 * Nat.centralBinom (k + n + 1)) =
      (2 : ℝ) ^ (2 * n + 1) * x ^ n / Nat.centralBinom n * Real.arcsin (Real.sqrt x) ^ 2 -
        Real.arcsin (Real.sqrt x) * Real.sqrt (x * (1 - x)) *
          ∑ k ∈ range n, (zuritaSCoeff n k : ℝ) * zuritaM (n - k) x * x ^ k +
        ∑ k ∈ Icc 1 (n - 1), r k * x ^ k + q * x ^ n

end

end MetaMathlibExt
