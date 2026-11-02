/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Arndt compositions: a generating functions approach

Statements from Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35 (arXiv:2311.15388).

An Arndt composition is a composition `(σ₁, …, σ_ℓ)` with `σ_{2i-1} > σ_{2i}` for every `i`
with `2i ≤ ℓ`; `a(n, m) = arndtCompositionCount (fun _ => True) n m` counts those of `n` with `m`
parts (`WantedExt/Combinatorics/Enumerative/ArndtCompositionsWanted.lean`). Bivariate generating
functions live in `ℤ[y][[x]]`, `x` marking the weight and `y` the second statistic, and rational
generating functions are stated multiplicatively (generating function times denominator equals
numerator).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.RingTheory.Binomial
public import WantedExt.Combinatorics.Enumerative.ArndtCompositionsWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Bivariate generating function of a two-index count.** For a function $a$ assigning a natural
number $a(n, m)$ to every pair of natural numbers $n, m$, its bivariate generating function is the
power series $\sum_{n \ge 0} \bigl(\sum_{m = 0}^{n} a(n, m)\, y^m\bigr) x^n$ in
$\mathbb{Z}[y][[x]]$, where $x$ marks the first index (the weight) and $y$ the second. Only the
terms with $m \le n$ enter; for counts with $a(n, m) = 0$ whenever $m > n$ it equals
$\sum_{n, m} a(n, m)\, x^n y^m$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2 (the series `A(x, y)`, `Ap(x, y)`,
`Bp(x, y)`, `B(x, y)`, `A_k(x, y)` and `A^{(k)}(x, y)`). -/
noncomputable def bivariateCountGF (a : ℕ → ℕ → ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    ∑ m ∈ Finset.range (n + 1), (a n m : Polynomial ℤ) * Polynomial.X ^ m

/-- **Coefficients of a bivariate generating function.** For every function $a$ assigning a natural
number $a(n, m)$ to each pair of natural numbers and every $n \ge 0$, the coefficient of $x^n$ in
the bivariate generating function of $a$ is the polynomial
$\sum_{m = 0}^{n} a(n, m)\, y^m \in \mathbb{Z}[y]$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2. -/
theorem coeff_bivariateCountGF (a : ℕ → ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (bivariateCountGF a) =
      ∑ m ∈ Finset.range (n + 1), (a n m : Polynomial ℤ) * Polynomial.X ^ m := by
  simp [bivariateCountGF]

/-- **The Arndt generating function as a bivariate count series.** For a set $S$ of natural
numbers, let $a_S(n, m)$ be the number of Arndt compositions of $n$ with $m$ parts, all parts in
$S$. Then the Arndt generating function $A_S(x, y)$ equals the bivariate generating function
$\sum_{n \ge 0} \sum_{m=0}^{n} a_S(n, m) x^n y^m$ in $\mathbb{Z}[y][[x]]$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2 (definition of `A(x, y)`). -/
theorem arndtGF_eq_bivariateCountGF (S : ℕ → Prop) [DecidablePred S] :
    arndtGF S = bivariateCountGF (arndtCompositionCount S) :=
  rfl

/-- **Anti-palindromic compositions.** For natural numbers $n$ and $m$, the number of
anti-palindromic compositions of $n$ with $m$ parts: sequences $(c_1, \dots, c_m)$ of positive
integers with $c_1 + \dots + c_m = n$ and $c_i \ne c_{m+1-i}$ for every $i$ with
$2i \ne m + 1$. That is, each part differs from the part in the mirror position, except the
middle part when $m$ is odd.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2.1 (definition of anti-palindromic
compositions, after Andrews, Just, and Simay). -/
def antiPalindromicCompositionCount (n m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    (∀ i, 0 < c i) ∧ ∀ i j : Fin m, (i : ℕ) + j + 1 = m → i ≠ j → c i ≠ c j).card

/-- **Reduced anti-palindromic compositions.** For natural numbers $n$ and $m$, this is the number
of compositions $(\sigma_1, \ldots, \sigma_m)$ of $n$ into $m$ positive parts such that
$\sigma_i > \sigma_{m+1-i}$ for every $i$ with $2i < m + 1$.

A composition $(\sigma_1, \ldots, \sigma_m)$ is anti-palindromic when
$\sigma_i \ne \sigma_{m+1-i}$ for every $i$ with $2i \ne m + 1$. Two anti-palindromic compositions
are equivalent when one arises from the other by swapping the entries $\sigma_i$ and
$\sigma_{m+1-i}$ of some of the pairs; each class contains exactly one composition of the form
above, so this is also the number of classes, the reduced anti-palindromic compositions of $n$
with $m$ parts.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2.1 (reduced anti-palindromic compositions and
the choice of representative after Theorem 7). -/
def reducedAntiPalindromicCompositionCount (n m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    (∀ i, 0 < c i) ∧ ∀ i j : Fin m, (i : ℕ) + j + 1 = m → i < j → c j < c i).card

/-- **Anti-palindromic compositions of 6 with three parts.** There are exactly eight
anti-palindromic compositions of $6$ with three parts.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2.1 (each class has `2^{⌊ℓ/2⌋}` members). -/
theorem antiPalindromicCompositionCount_six_three : antiPalindromicCompositionCount 6 3 = 8 := by
  decide

/-- **Reduced anti-palindromic compositions of 6 with three parts.** There are exactly four reduced
anti-palindromic compositions of $6$ with three parts.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2.1 (each class has `2^{⌊ℓ/2⌋}` members). -/
theorem reducedAntiPalindromicCompositionCount_six_three :
    reducedAntiPalindromicCompositionCount 6 3 = 4 := by
  decide

/-- **Anti-palindromic compositions of 6 with four parts.** There are exactly four
anti-palindromic compositions of $6$ with four parts, and exactly one reduced anti-palindromic
composition of $6$ with four parts.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2.1 (each class has `2^{⌊ℓ/2⌋}` members). -/
theorem antiPalindromicCompositionCount_six_four :
    antiPalindromicCompositionCount 6 4 = 4 ∧ reducedAntiPalindromicCompositionCount 6 4 = 1 := by
  decide

/-- **Arndt compositions by last part.** An Arndt composition of $n$ is a composition
$(\sigma_1, \ldots, \sigma_\ell)$ of $n$ into positive parts such that $\sigma_{2i-1} > \sigma_{2i}$
for every $i$ with $2i \le \ell$. For natural numbers $n$ and $j$, $b(n, j)$ is the number of
Arndt compositions of $n$, with any number of parts, whose last part is $j$. The empty
composition of $0$ counts as having last part $0$, so $b(0, 0) = 1$ and $b(0, j) = 0$ for
$j \ge 1$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 3 (definition of `b(n, m)` and Table 2). -/
def arndtLastPartCount (n j : ℕ) : ℕ :=
  if n = 0 then (if j = 0 then 1 else 0) else
    ∑ m ∈ Finset.range n,
      ((Finset.Nat.antidiagonalTuple (m + 1) n).filter fun c =>
        (∀ i, 0 < c i) ∧
          (∀ i i' : Fin (m + 1), (i : ℕ) % 2 = 0 → (i' : ℕ) = i + 1 → c i' < c i) ∧
            c (Fin.last m) = j).card

/-- **Arndt compositions of 6 by last part.** Let $b(n, j)$ be the number of Arndt compositions
of $n$ with last part $j$. Then $b(6, 1) = 4$, $b(6, 2) = 2$, $b(6, 3) = 1$ and $b(6, 6) = 1$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 3, Table 2. -/
theorem arndtLastPartCount_six :
    arndtLastPartCount 6 1 = 4 ∧ arndtLastPartCount 6 2 = 2 ∧ arndtLastPartCount 6 3 = 1 ∧
      arndtLastPartCount 6 6 = 1 := by
  decide +kernel

/-- **Number of $k$-Arndt compositions.** For an integer $k$ and $n, m \ge 0$, $a_k(n, m)$ is the
number of $k$-Arndt compositions of $n$ with $m$ parts: sequences $(c_0, \ldots, c_{m-1})$ of
positive integers with $c_0 + \cdots + c_{m-1} = n$ such that $c_{2i} > c_{2i+1} + k$ for every
$i \ge 0$ with $2i + 1 < m$. For $k = 0$ these are the Arndt compositions.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 4 (definition of `k`-Arndt compositions,
after Hopkins and Tangboonduangjit; Theorem 11 treats `k ≥ 0` and `k < 0`). -/
def kArndtCompositionCount (k : ℤ) (n m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    (∀ i, 0 < c i) ∧
      ∀ i j : Fin m, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → (c j : ℤ) + k < c i).card

/-- **Sample values of the $k$-Arndt composition counts.** Writing $a_k(n, m)$ for the number of
$k$-Arndt compositions of $n$ with $m$ parts, $a_3(7, 2) = 1$, $a_3(7, 3) = 1$ and
$a_{-3}(4, 2) = 3$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 4 (series expansions after Theorem 11). -/
theorem kArndtCompositionCount_examples :
    kArndtCompositionCount 3 7 2 = 1 ∧ kArndtCompositionCount 3 7 3 = 1 ∧
      kArndtCompositionCount (-3) 4 2 = 3 := by
  decide

/-- **Number of $k$-block Arndt compositions.** For $k \ge 1$ and $n, m \ge 0$, $a^{(k)}(n, m)$ is
the number of $k$-block Arndt compositions of $n$ with $m$ parts: sequences
$(c_0, \ldots, c_{m-1})$ of positive integers with $c_0 + \cdots + c_{m-1} = n$ that strictly
decrease inside each block of $k$ consecutive positions $ki, ki + 1, \ldots, ki + k - 1$ (the last
block may be shorter), that is, $c_i > c_{i+1}$ for every $i$ with $i + 1 < m$ and
$i \not\equiv k - 1 \pmod{k}$. For $k = 2$ these are the Arndt compositions.

The definition is meant for $k \ge 1$; its value at $k = 0$ has no combinatorial meaning.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 5 (definition of `k`-block Arndt
compositions). -/
def blockArndtCompositionCount (k n m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    (∀ i, 0 < c i) ∧
      ∀ i j : Fin m, (i : ℕ) % k ≠ k - 1 → (j : ℕ) = i + 1 → c j < c i).card

/-- **Four-part 3-block Arndt compositions of 10.** There are exactly $7$ three-block Arndt
compositions of $10$ with $4$ parts, that is, $a^{(3)}(10, 4) = 7$.

They are $(6,2,1,1)$, $(5,3,1,1)$, $(5,2,1,2)$, $(4,3,2,1)$, $(4,3,1,2)$, $(4,2,1,3)$ and
$(3,2,1,4)$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 5 (list of the compositions counted by
`a^{(3)}(10) = 18`). -/
theorem blockArndtCompositionCount_three_ten_four : blockArndtCompositionCount 3 10 4 = 7 := by
  decide

/-- **Alternating sum and recurrence for Arndt compositions.** Let $a(n, m)$ be the number of
Arndt compositions of $n$ with $m$ parts, and write $K = n - m - \lfloor m/2 \rfloor$. For all
$n, m \ge 0$: if $m + \lfloor m/2 \rfloor \le n$, then
$$a(n, m) = \sum_{\ell=0}^{K} \binom{m+\ell-1}{\ell} \binom{n-m-\ell-1}{K-\ell} (-1)^{K-\ell},$$
and otherwise $a(n, m) = 0$. Moreover, for all $n \ge 3$ and $m \ge 2$,
$a(n, m) = a(n-1, m) + a(n-2, m) - a(n-3, m) + a(n-3, m-2)$. The binomial coefficients are the
generalized ones, $\binom{r}{k} = r(r-1)\cdots(r-k+1)/k!$ for an integer $r$, so the upper
index $-1$ is allowed and $\binom{-1}{k} = (-1)^k$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 2 (`integers-2024-A35-thm-2`). -/
public theorem_wanted arndtCompositionCount_eq_alternating_sum_and_recurrence :
    (∀ n m : ℕ, (arndtCompositionCount (fun _ => True) n m : ℤ) =
      if m + m / 2 ≤ n then
        ∑ ℓ ∈ Finset.range (n - m - m / 2 + 1),
          Ring.choose ((m : ℤ) + ℓ - 1) ℓ * Ring.choose ((n : ℤ) - m - ℓ - 1) (n - m - m / 2 - ℓ) *
            (-1) ^ (n - m - m / 2 - ℓ)
      else 0) ∧
    ∀ n m : ℕ, 3 ≤ n → 2 ≤ m →
      (arndtCompositionCount (fun _ => True) n m : ℤ) =
        arndtCompositionCount (fun _ => True) (n - 1) m +
          arndtCompositionCount (fun _ => True) (n - 2) m -
            arndtCompositionCount (fun _ => True) (n - 3) m +
              arndtCompositionCount (fun _ => True) (n - 3) (m - 2)

/-- **Positive sum for Arndt compositions.** Let $a(n, m)$ be the number of Arndt compositions of
$n$ with $m$ parts, and write $h = \lfloor m/2 \rfloor$. For all $n \ge 0$ and $m \ge 1$: if
$m + h \le n$, then
$$a(n, m) = \sum_{\ell=0}^{\lfloor (n-m-h)/2 \rfloor} \binom{h+\ell-1}{\ell}
\binom{n-2h-2\ell-1}{\lfloor (m-1)/2 \rfloor},$$
and otherwise $a(n, m) = 0$. Here $\binom{-1}{0} = 1$ (this term occurs for $m = 1$).

The paper states it for all $n, m \ge 0$; at $n = m = 0$ it fails ($a(0, 0) = 1$, while the only
term has lower index $\lfloor -1/2 \rfloor = -1$ and vanishes), so the case $m = 0$ is omitted.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 3 (`integers-2024-A35-thm-3`). -/
public theorem_wanted arndtCompositionCount_eq_positive_sum (n m : ℕ) (hm : 0 < m) :
    (arndtCompositionCount (fun _ => True) n m : ℤ) =
      if m + m / 2 ≤ n then
        ∑ ℓ ∈ Finset.range ((n - m - m / 2) / 2 + 1),
          Ring.choose (((m / 2 : ℕ) : ℤ) + ℓ - 1) ℓ *
            Ring.choose ((n : ℤ) - 2 * (m / 2 : ℕ) - 2 * ℓ - 1) ((m - 1) / 2)
      else 0

/-- **Holonomic recurrence for Arndt compositions.** Let $a(n, m)$ be the number of Arndt
compositions of $n$ with $m$ parts. For all $n, m \ge 0$,
$$(m - n - 2 + \lfloor m/2 \rfloor)\, a(n+2, m) + (m - \lfloor m/2 \rfloor)\, a(n+1, m) +
n\, a(n, m) = 0.$$

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 4 (`integers-2024-A35-thm-4`). -/
public theorem_wanted arndtCompositionCount_holonomic_recurrence (n m : ℕ) :
    ((m : ℤ) - n - 2 + (m / 2 : ℕ)) * arndtCompositionCount (fun _ => True) (n + 2) m +
        ((m : ℤ) - (m / 2 : ℕ)) * arndtCompositionCount (fun _ => True) (n + 1) m +
          (n : ℤ) * arndtCompositionCount (fun _ => True) n m = 0

/-- **Asymptotics of Arndt compositions with a fixed number of parts.** Let $a(n, m)$ be the
number of Arndt compositions of $n$ with $m$ parts. For every fixed integer $m \ge 1$,
$$a(n, m) \sim \frac{n^{m-1}}{2^{\lfloor m/2 \rfloor} (m-1)!} \quad (n \to \infty).$$

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 1 (`integers-2024-A35-cor-1`). -/
public theorem_wanted arndtCompositionCount_isEquivalent (m : ℕ) (hm : 0 < m) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (arndtCompositionCount (fun _ => True) n m : ℝ))
      (fun n : ℕ => (n : ℝ) ^ (m - 1) / (2 ^ (m / 2) * (Nat.factorial (m - 1) : ℝ)))

/-- **Arndt compositions are counted by Fibonacci numbers.** Let $a(n, m)$ be the number of Arndt
compositions of $n$ with $m$ parts, let $a(n) = \sum_{m=0}^{n} a(n, m)$ be the number of all
Arndt compositions of $n$, and let $F_n$ be the $n$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$).
Then, in $\mathbb{Z}[[x]]$,
$$\Big(\sum_{n \ge 0} a(n) x^n\Big)(1 - x - x^2) = 1 - x^2,$$
and $a(n) = F_n$ for every $n \ge 1$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 2 (`integers-2024-A35-cor-2`). -/
public theorem_wanted arndtComposition_total_eq_fib :
    (PowerSeries.mk fun n =>
        ((∑ m ∈ Finset.range (n + 1), arndtCompositionCount (fun _ => True) n m : ℕ) : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2) = 1 - PowerSeries.X ^ 2 ∧
      ∀ n : ℕ, 1 ≤ n →
        ∑ m ∈ Finset.range (n + 1), arndtCompositionCount (fun _ => True) n m = Nat.fib n

/-- **Expected number of parts of an Arndt composition.** Let $a(n, m)$ be the number of Arndt
compositions of $n$ with $m$ parts, and $F_n$ the $n$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$).
Then
$$\frac{1}{F_n} \sum_{m=0}^{n} m\, a(n, m) \sim \left(\frac{3}{\sqrt 5} - 1\right) n
\quad (n \to \infty).$$

Since there are $F_n$ Arndt compositions of $n$ for $n \ge 1$, the left side is the expected
number of parts of a uniformly random Arndt composition of $n$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 5 (`integers-2024-A35-thm-5`). -/
public theorem_wanted arndtComposition_expected_parts_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ =>
        (∑ m ∈ Finset.range (n + 1), (m * arndtCompositionCount (fun _ => True) n m : ℝ)) /
          (Nat.fib n : ℝ))
      (fun n : ℕ => (3 / Real.sqrt 5 - 1) * n)

/-- **Generating function of anti-palindromic compositions.** Let $ap(n, m)$ be the number of
anti-palindromic compositions of $n$ with $m$ parts, and let
$Ap(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} ap(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$. Then
$Ap(x, y)\,(1 - x - x^2 + x^3 - 2x^3y^2) = 1 - x - x^2 + x^3 + xy - x^3y$, that is,
$Ap(x, y) = (1 - x - x^2 + x^3 + xy - x^3y)/(1 - x - x^2 + x^3 - 2x^3y^2)$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 6 (`integers-2024-A35-thm-6`). -/
public theorem_wanted bivariateCountGF_antiPalindromic :
    bivariateCountGF antiPalindromicCompositionCount *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 -
          PowerSeries.C (2 * Polynomial.X ^ 2) * PowerSeries.X ^ 3) =
      1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
        PowerSeries.C Polynomial.X * PowerSeries.X -
          PowerSeries.C Polynomial.X * PowerSeries.X ^ 3

/-- **Generating function of reduced anti-palindromic compositions.** Let $b(n, m)$ be the number
of reduced anti-palindromic compositions of $n$ with $m$ parts, and let
$B_p(x, y) = \sum_{n \ge 0} \sum_{m = 0}^{n} b(n, m)\, x^n y^m$ in $\mathbb{Z}[y][[x]]$, where
$x$ marks the weight and $y$ the number of parts. Then
$$B_p(x, y)\,(1 - x - x^2 + x^3 - x^3 y^2) = 1 - x - x^2 + x^3 + xy - x^3 y,$$
that is, $B_p(x, y) = (1 - x - x^2 + x^3 + xy - x^3 y)/(1 - x - x^2 + x^3 - x^3 y^2)$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 3 (`integers-2024-A35-cor-3`). -/
public theorem_wanted bivariateCountGF_reducedAntiPalindromic :
    bivariateCountGF reducedAntiPalindromicCompositionCount *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 -
          PowerSeries.C (Polynomial.X ^ 2) * PowerSeries.X ^ 3) =
      1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
        PowerSeries.C Polynomial.X * PowerSeries.X -
          PowerSeries.C Polynomial.X * PowerSeries.X ^ 3

/-- **Arndt compositions and reduced anti-palindromic compositions are equinumerous.** For all
natural numbers $n$ and $m$, the number of reduced anti-palindromic compositions of $n$ with $m$
parts equals the number of Arndt compositions of $n$ with $m$ parts, all positive integers being
allowed as parts.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 7 (`integers-2024-A35-thm-7`). -/
public theorem_wanted reducedAntiPalindromicCompositionCount_eq_arndtCompositionCount (n m : ℕ) :
    reducedAntiPalindromicCompositionCount n m = arndtCompositionCount (fun _ => True) n m

/-- **Generating function of Arndt compositions by last part.** Let $b(n, m)$ be the number of
Arndt compositions of $n$ with last part $m$, where the empty composition of $0$ counts as
having last part $0$ (so $b(0, 0) = 1$), and let
$B(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} b(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$. Then
$B(x, y)\,(1 - x - x^2)(1 - xy)(1 - x^2y) =
1 - x - x^2 - x^2y + 2x^3y + 2x^4y - x^5y - x^4y^2$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 8 (`integers-2024-A35-thm-8`). -/
public theorem_wanted bivariateCountGF_arndtLastPart :
    bivariateCountGF arndtLastPartCount *
        ((1 - PowerSeries.X - PowerSeries.X ^ 2) *
          (1 - PowerSeries.C Polynomial.X * PowerSeries.X) *
            (1 - PowerSeries.C Polynomial.X * PowerSeries.X ^ 2)) =
      1 - PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.C Polynomial.X * PowerSeries.X ^ 2 +
        PowerSeries.C (2 * Polynomial.X) * PowerSeries.X ^ 3 +
          PowerSeries.C (2 * Polynomial.X) * PowerSeries.X ^ 4 -
            PowerSeries.C Polynomial.X * PowerSeries.X ^ 5 -
              PowerSeries.C (Polynomial.X ^ 2) * PowerSeries.X ^ 4

/-- **Closed formula for Arndt compositions by last part.** Let $F_r$ be the $r$-th Fibonacci
number ($F_0 = 0$, $F_1 = 1$) and $b(n, m)$ the number of Arndt compositions of $n$ with last
part $m$. Define $t_1, t_2 : \mathbb{N} \to \mathbb{N}$ by $t_1(0) = 1$, $t_1(1) = 0$,
$t_1(r) = F_{r-2}$ and $t_2(0) = 0$, $t_2(1) = 1$, $t_2(r) = F_{r-1}$ for $r \ge 2$. Then for all
integers $n \ge 1$ and $m \ge 1$: $b(n, m) = 0$ if $n < m$, $b(n, m) = t_1(n - m)$ if
$m \le n < 2m$, and $b(n, m) = t_1(n - m) + t_2(n - 2m)$ if $n \ge 2m$.

The paper leaves the range of $m$ implicit; at $m = 0$ the printed formula fails ($b(1, 0) = 0$,
while the formula gives $t_1(1) + t_2(1) = 1$), so $m \ge 1$ is assumed.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 9 (`integers-2024-A35-thm-9`). -/
public theorem_wanted arndtLastPartCount_eq (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    let t₁ : ℕ → ℕ := fun r => if r = 0 then 1 else if r = 1 then 0 else Nat.fib (r - 2)
    let t₂ : ℕ → ℕ := fun r => if r = 0 then 0 else if r = 1 then 1 else Nat.fib (r - 1)
    arndtLastPartCount n m =
      if n < m then 0 else if n < 2 * m then t₁ (n - m) else t₁ (n - m) + t₂ (n - 2 * m)

/-- **Asymptotics of Arndt compositions with a fixed last part.** Let $b(n, m)$ be the number of
Arndt compositions of $n$ with last part $m$, and let $\varphi$ be the golden ratio. For every
fixed integer $m \ge 1$,
$b(n, m) \sim \frac{\varphi^{n-m-2}}{\sqrt{5}} \left(1 + \frac{1}{\varphi^{m-1}}\right)$ as
$n \to \infty$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 10 (`integers-2024-A35-thm-10`). -/
public theorem_wanted arndtLastPartCount_isEquivalent (m : ℕ) (hm : 0 < m) :
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (arndtLastPartCount n m : ℝ))
      (fun n : ℕ => Real.goldenRatio ^ ((n : ℤ) - m - 2) / Real.sqrt 5 *
        (1 + 1 / Real.goldenRatio ^ ((m : ℤ) - 1)))

/-- **Arndt compositions with last part at most or at least $k$.** Let $F_n$ be the $n$-th
Fibonacci number ($F_0 = 0$, $F_1 = 1$) and $b(n, j)$ the number of Arndt compositions of $n$
with last part $j$. For all integers $k \ge 1$ and $n \ge 2k + 2$, the number of Arndt
compositions of $n$ with last part at most $k$ is
$\sum_{j=1}^{k} b(n, j) = F_n - F_{n-k-1} - F_{n-2k-2}$, and the number with last part at least
$k$ is $\sum_{j=k}^{n} b(n, j) = F_{n-k} + F_{n-2k}$.

The paper prints the second count as $F_{n-k} - F_{n-2k}$, which is false: for $k = 1$ and
$n = 4$ all $F_4 = 3$ Arndt compositions of $4$ have last part at least $1$, while
$F_3 - F_2 = 1$. The sign $+$ is the one the paper's own consequence uses ($F_{n-2} + F_{n-4}$
compositions with last part greater than $1$), and it is what subtracting the number with last
part at most $k - 1$ from $F_n$ gives.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 4 (`integers-2024-A35-cor-4`). -/
public theorem_wanted arndtLastPart_atMost_atLeast (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k + 2 ≤ n) :
    ((∑ j ∈ Finset.Icc 1 k, arndtLastPartCount n j : ℕ) : ℤ) =
        Nat.fib n - Nat.fib (n - k - 1) - Nat.fib (n - 2 * k - 2) ∧
      ∑ j ∈ Finset.Icc k n, arndtLastPartCount n j = Nat.fib (n - k) + Nat.fib (n - 2 * k)

/-- **Generating function of $k$-Arndt compositions for $k \ge 0$.** Let $k \ge 0$ be an
integer, let $a_k(n, m)$ be the number of $k$-Arndt compositions of $n$ with $m$ parts, and let
$A_k(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} a_k(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$. Then
$A_k(x, y)\,(1 - x - x^2 + x^3 - x^{3+k}y^2) = (1 - x^2)(1 - x(1 - y))$, that is,
$A_k(x, y) = (1 - x^2)(1 - x(1 - y))/(1 - x - x^2 + x^3 - x^{3+k}y^2)$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 11, case `k ≥ 0`
(`integers-2024-A35-thm-11`). -/
public theorem_wanted bivariateCountGF_kArndt_nonneg (k : ℕ) :
    bivariateCountGF (kArndtCompositionCount k) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 -
          PowerSeries.C (Polynomial.X ^ 2) * PowerSeries.X ^ (3 + k)) =
      (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X + PowerSeries.C Polynomial.X * PowerSeries.X)

/-- **Generating function of $k$-Arndt compositions for negative $k$.** Let $k' \ge 1$ and
$k = -k'$, let $a_k(n, m)$ be the number of $k$-Arndt compositions of $n$ with $m$ parts, and
let $A_k(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} a_k(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$. Then
$A_k(x, y)\,(1 - x - x^2(1 + y^2) + x^3(1 - y^2) + y^2x^{2+k'}) = (1 - x^2)(1 - x(1 - y))$,
that is,
$A_k(x, y) = (1 - x^2)(1 - x(1 - y))/(1 - x - x^2(1 + y^2) + x^3(1 - y^2) + y^2x^{2-k})$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 11, case `k < 0`
(`integers-2024-A35-thm-11`). -/
public theorem_wanted bivariateCountGF_kArndt_neg (k' : ℕ) (hk' : 0 < k') :
    bivariateCountGF (kArndtCompositionCount (-(k' : ℤ))) *
        (1 - PowerSeries.X - PowerSeries.C (1 + Polynomial.X ^ 2) * PowerSeries.X ^ 2 +
          PowerSeries.C (1 - Polynomial.X ^ 2) * PowerSeries.X ^ 3 +
            PowerSeries.C (Polynomial.X ^ 2) * PowerSeries.X ^ (2 + k')) =
      (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X + PowerSeries.C Polynomial.X * PowerSeries.X)

/-- **Counting $k$-Arndt compositions for nonnegative $k$.** Let $k \ge 0$ be an integer and let
$a_k(n) = \sum_{m = 0}^{n} a_k(n, m)$ be the number of $k$-Arndt compositions of $n$. Then, in
$\mathbb{Z}[[x]]$,
$$\Bigl(\sum_{n \ge 0} a_k(n)\, x^n\Bigr)(1 - x - x^2 + x^3 - x^{k+3}) = 1 - x^2,$$
that is, $\sum_{n \ge 0} a_k(n)\, x^n = (1 - x^2)/(1 - x - x^2 + x^3 - x^{k+3})$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 6, case `k ≥ 0`
(`integers-2024-A35-cor-6`). -/
public theorem_wanted kArndtComposition_total_gf_nonneg (k : ℕ) :
    (PowerSeries.mk fun n =>
        ((∑ m ∈ Finset.range (n + 1), kArndtCompositionCount k n m : ℕ) : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 - PowerSeries.X ^ (k + 3)) =
      1 - PowerSeries.X ^ 2

/-- **Counting $k$-Arndt compositions for negative $k$.** Let $k = -k'$ with $k' \ge 1$ an integer,
and let $a_k(n) = \sum_{m = 0}^{n} a_k(n, m)$ be the number of $k$-Arndt compositions of $n$. Then,
in $\mathbb{Z}[[x]]$,
$$\Bigl(\sum_{n \ge 0} a_k(n)\, x^n\Bigr)(1 - x - 2x^2 + x^{2-k}) = 1 - x^2,$$
that is, $\sum_{n \ge 0} a_k(n)\, x^n = (1 - x^2)/(1 - x - 2x^2 + x^{2-k})$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 6, case `k < 0`
(`integers-2024-A35-cor-6`). -/
public theorem_wanted kArndtComposition_total_gf_neg (k' : ℕ) (hk' : 0 < k') :
    (PowerSeries.mk fun n =>
        ((∑ m ∈ Finset.range (n + 1), kArndtCompositionCount (-(k' : ℤ)) n m : ℕ) : ℤ)) *
        (1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ (2 + k')) =
      1 - PowerSeries.X ^ 2

/-- **Generating function of block Arndt compositions.** Let $k \ge 1$, let $a^{(k)}(n, m)$ be
the number of $k$-block Arndt compositions of $n$ with $m$ parts, and let
$A^{(k)}(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} a^{(k)}(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$.
Then
$A^{(k)}(x, y) \bigl(\prod_{\ell=1}^{k} (1 - x^\ell) - x^{\binom{k+1}{2}} y^k\bigr) =
\sum_{j=0}^{k-1} x^{\binom{j+1}{2}} y^j \prod_{\ell=j+1}^{k} (1 - x^\ell)$.
Equivalently, with $J_j(x, y) = x^{\binom{j+1}{2}} y^j \prod_{\ell=1}^{j} (1 - x^\ell)^{-1}$,
$A^{(k)}(x, y) = \bigl(\sum_{j=0}^{k-1} J_j(x, y)\bigr) / (1 - J_k(x, y))$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 12 (`integers-2024-A35-thm-12`). -/
public theorem_wanted bivariateCountGF_blockArndt (k : ℕ) (hk : 1 ≤ k) :
    bivariateCountGF (blockArndtCompositionCount k) *
        ((∏ ℓ ∈ Finset.Icc 1 k, (1 - PowerSeries.X ^ ℓ)) -
          PowerSeries.C (Polynomial.X ^ k) * PowerSeries.X ^ Nat.choose (k + 1) 2) =
      ∑ j ∈ Finset.range k,
        PowerSeries.C (Polynomial.X ^ j) * PowerSeries.X ^ Nat.choose (j + 1) 2 *
          ∏ ℓ ∈ Finset.Ioc j k, (1 - PowerSeries.X ^ ℓ)

end

end MetaMathlibExt
