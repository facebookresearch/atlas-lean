/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums of powers of integers and the sequence A304330

Statements from José L. Cereceda, "Sums of Powers of Integers and
the Sequence A304330", *Journal of Integer Sequences* 28 (2025),
Article 25.1.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Cereceda/cere9.html>).
Definitions are taken from the publisher TeX.

`S_k(n) = 1^k + ⋯ + n^k` is `powerSum`.  The array `R(k, m)`
(OEIS A304330 rows: `1; 1, 12; 1, 60, 360; …`) is defined by
`R(k, m) = Σ_{j=0}^m (-1)^j C(2m, j) (m - j)^{2k}`, and
`U(k, m) = (2/(2m)!)·R(k, m)`.  The inverse array `u(k, m)`, defined by
`Σ_{m=1}^k u(k, m) x^m = ∏_{i=0}^{k-1} (x - i^2)`, is the
existing specialization `MetaMathlibExt.jacobiStirlingFirst k m
(0 : ℤ)`, and the Legendre-Stirling numbers of the first kind
`Ps_m^{(r)}` (which the paper only names) are the existing
`MetaMathlibExt.legendreStirlingFirst`, i.e. the standard signed
convention `∏_{j=0}^{m-1} (x - j(j+1)) = Σ_r Ps_m^{(r)} x^r`,
which is the convention satisfying Proposition 12 (checked
numerically; the opposite sign fails).  The polynomial
identities below are stated for all `n : ℕ` where they hold at
`n = 0` as well; Lemmas 4 and 7 keep the paper's `n ≥ 1`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Enumerative.LegendreStirlingFirstKind

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

/-- **Power sums.** For natural numbers $k$ and $n$, the power sum $S_k(n)$ is the rational
number $\sum_{i=1}^{n} i^k = 1^k + 2^k + \cdots + n^k$, which is $0$ when $n = 0$. -/
def powerSum (k n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ k

/-- **The array $R(k, m)$.** For natural numbers $k$ and $m$, $R(k, m)$ is the integer
$\sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. -/
def arrayR (k m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℤ) ^ j * (Nat.choose (2 * m) j : ℤ) * ((m : ℤ) - j) ^ (2 * k)

/-- **The array $U(k, m)$.** For natural numbers $k$ and $m$, $U(k, m)$ is the rational number
$\frac{2}{(2m)!} \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. -/
def arrayU (k m : ℕ) : ℚ :=
  (2 / (Nat.factorial (2 * m) : ℚ)) *
    ∑ j ∈ Finset.range (m + 1),
      (-1 : ℚ) ^ j * (Nat.choose (2 * m) j : ℚ) * ((m : ℚ) - j) ^ (2 * k)

/-- **The Faulhaber coefficients $b_{k,r}$.** For natural numbers $p$ and $q$, let
$R(p, q) = \sum_{j=0}^{q} (-1)^j \binom{2q}{j} (q - j)^{2p}$, and for natural numbers $q$
and $s$ let $\mathrm{Ps}_q^{(s)}$ be the Legendre–Stirling number of the first kind, the
coefficient of $x^s$ in $\prod_{i=0}^{q-1} (x - i(i+1))$. For natural numbers $k$ and $r$,
$b_{k,r}$ is the rational number
$\sum_{m=r}^{k} \frac{3 \cdot 2^r}{(2m+1)!}\, R(k, m)\, \mathrm{Ps}_m^{(r)}$. -/
noncomputable def faulhaberB (k r : ℕ) : ℚ :=
  ∑ m ∈ Finset.Icc r k,
    (3 * 2 ^ r / (Nat.factorial (2 * m + 1) : ℚ)) *
      (arrayR k m : ℚ) * (MetaMathlibExt.legendreStirlingFirst m r : ℚ)

/-- **The Faulhaber coefficients $c_{k,r}$.** For natural numbers $p$ and $q$, let
$R(p, q) = \sum_{j=0}^{q} (-1)^j \binom{2q}{j} (q - j)^{2p}$, and for natural numbers $q$
and $s$ let $\mathrm{Ps}_q^{(s)}$ be the Legendre–Stirling number of the first kind, the
coefficient of $x^s$ in $\prod_{i=0}^{q-1} (x - i(i+1))$. For natural numbers $k$ and $r$,
$c_{k,r}$ is the rational number
$\sum_{m=r}^{k} \frac{2^{r+1}}{(2m+2)!\,(m+1)}\, R(k+1, m+1)\, \mathrm{Ps}_{m+1}^{(r+1)}$. -/
noncomputable def faulhaberC (k r : ℕ) : ℚ :=
  ∑ m ∈ Finset.Icc r k,
    (2 ^ (r + 1) / ((Nat.factorial (2 * m + 2) : ℚ) * (m + 1))) *
      (arrayR (k + 1) (m + 1) : ℚ) * (MetaMathlibExt.legendreStirlingFirst (m + 1) (r + 1) : ℚ)

/-- **The polynomials $Q_{k,m}$ of Theorem 10.** For natural numbers $k$, $m$ and $n$, write
$R(a, b) = \sum_{i=0}^{b} (-1)^i \binom{2b}{i} (b - i)^{2a}$ for the array of OEIS A304330.
The rational number $Q_{k,m}(n)$ is $n^{2k-1}$ if $m = 1$, and otherwise
$$Q_{k,m}(n) = 2 \sum_{j=m}^{k} \binom{2k-1}{2j-2} R(j-1, m-1) \, n^{2k-2j+1}.$$

Differences of natural numbers such as $2k - 1$ and $m - 1$ are truncated at $0$. -/
def thmQ (k m n : ℕ) : ℚ :=
  if m = 1 then (n : ℚ) ^ (2 * k - 1)
  else 2 * ∑ j ∈ Finset.Icc m k,
    (Nat.choose (2 * k - 1) (2 * j - 2) : ℚ) *
      (arrayR (j - 1) (m - 1) : ℚ) * (n : ℚ) ^ (2 * k - 2 * j + 1)

/-- **Even power sums in terms of $\binom{2n+m+1}{2m+1}$.** For natural numbers $k \ge 1$ and
$n$, write $S_{2k}(n) = 1^{2k} + 2^{2k} + \dots + n^{2k}$ and
$R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. Then
$2^{2k} S_{2k}(n) = \sum_{m=1}^{k} R(k, m) \binom{2n+m+1}{2m+1}$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Theorem 1. -/
theorem_wanted pow_mul_powerSum_even_eq_sum (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    (2 : ℚ) ^ (2 * k) * powerSum (2 * k) n =
      ∑ m ∈ Finset.Icc 1 k,
        (arrayR k m : ℚ) *
          (Nat.choose (2 * n + m + 1) (2 * m + 1) : ℚ)

/-- **Knuth's correspondence between even and odd power sums.** Let $k \ge 1$ be a natural
number, let $(a_m)_{m \ge 0}$ be a sequence of real numbers, and write
$S_j(n) = 1^j + 2^j + \dots + n^j$. Then
$\frac{S_{2k}(n)}{2n+1} = \sum_{m=1}^{k} a_m \binom{n+m}{2m}$ for every natural number $n$
if and only if $S_{2k-1}(n) = \sum_{m=1}^{k} \frac{2m+1}{m}\, a_m \binom{n+m}{2m}$ for every
natural number $n$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 2. -/
theorem_wanted powerSum_even_div_iff_odd (k : ℕ) (hk : 1 ≤ k)
    (a : ℕ → ℝ) :
    (∀ n : ℕ, (powerSum (2 * k) n : ℝ) / (2 * (n : ℝ) + 1) =
      ∑ m ∈ Finset.Icc 1 k,
        a m * (Nat.choose (n + m) (2 * m) : ℝ)) ↔
    (∀ n : ℕ, (powerSum (2 * k - 1) n : ℝ) =
      ∑ m ∈ Finset.Icc 1 k,
        ((2 * (m : ℝ) + 1) / (m : ℝ)) * a m *
          (Nat.choose (n + m) (2 * m) : ℝ))

/-- **Knuth's formula for even power sums.** For natural numbers $k \ge 1$ and $n$, write
$S_{2k}(n) = 1^{2k} + 2^{2k} + \dots + n^{2k}$ and
$R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. Then
$S_{2k}(n) = \sum_{m=1}^{k} R(k, m)\, \frac{2n+1}{2m+1} \binom{n+m}{2m}$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 3. -/
theorem_wanted powerSum_even_eq_sum (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    powerSum (2 * k) n =
      ∑ m ∈ Finset.Icc 1 k,
        (arrayR k m : ℚ) * ((2 * (n : ℚ) + 1) / (2 * (m : ℚ) + 1)) *
          (Nat.choose (n + m) (2 * m) : ℚ)

/-- **Knuth's binomial formula for the odd power sums.** For all natural numbers $k \ge 1$ and
$n$, the power sum $S_{2k-1}(n) = 1^{2k-1} + 2^{2k-1} + \cdots + n^{2k-1}$ satisfies
$$S_{2k-1}(n) = \sum_{m=1}^{k} R(k, m) \cdot \frac{1}{m} \binom{n + m}{2m},$$
where $R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$ is the array of OEIS A304330.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 3. -/
theorem_wanted powerSum_odd_eq_sum (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    powerSum (2 * k - 1) n =
      ∑ m ∈ Finset.Icc 1 k,
        (arrayR k m : ℚ) * (1 / (m : ℚ)) *
          (Nat.choose (n + m) (2 * m) : ℚ)

/-- **Sum of $2i \binom{2i+k-1}{2k-1}$.** For all natural numbers $k \ge 1$ and $n \ge 1$,
$$\sum_{i=1}^{n} 2i \binom{2i + k - 1}{2k - 1} = k \binom{2n + k + 1}{2k + 1}.$$

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 4. -/
theorem_wanted sum_two_mul_choose_eq (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n,
      (2 * i) * Nat.choose (2 * i + k - 1) (2 * k - 1)) =
      k * Nat.choose (2 * n + k + 1) (2 * k + 1)

/-- **Inversion formula for the arrays $u(k, m)$ and $U(k, m)$ (Butzer et al.).** For natural
numbers $k$ and $m$, let $u(k, m)$ be the first-kind Jacobi–Stirling number $J(k, m; 0)$, the
coefficient of $x^m$ in $\prod_{i=0}^{k-1} (x - i^2)$, and let
$U(k, m) = \frac{2}{(2m)!} \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. For all sequences
$(a_k)_{k \ge 0}$ and $(b_k)_{k \ge 0}$ of real numbers, $a_k = \sum_{m=1}^{k} u(k, m)\, b_m$
holds for every $k \ge 1$ if and only if $b_k = \sum_{m=1}^{k} U(k, m)\, a_m$ holds for every
$k \ge 1$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 5. -/
theorem_wanted inversion_uU (a b : ℕ → ℝ) :
    (∀ k : ℕ, 1 ≤ k → a k =
      ∑ m ∈ Finset.Icc 1 k, (MetaMathlibExt.jacobiStirlingFirst k m (0 : ℤ) : ℝ) * b m) ↔
    (∀ k : ℕ, 1 ≤ k → b k =
      ∑ m ∈ Finset.Icc 1 k, (arrayU k m : ℝ) * a m)

/-- **Closed form for the array $R(k, m)$.** Let $k$ and $m$ be natural numbers with
$1 \le m \le k$, and let $R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. Then
$$R(k, m) = 2^{2k+m-1}\, m! \sum_{b} \frac{(2k)!}{b_1! \cdots b_k!}
\prod_{r=1}^{k} \left(\frac{1}{4^r (2r)!}\right)^{b_r},$$
where the sum runs over all $k$-tuples $b = (b_1, \dots, b_k)$ of natural numbers with
$b_1 + 2 b_2 + \dots + k b_k = k$ and $b_1 + \dots + b_k = m$ (each such $b_r$ is at most $k$).

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Corollary 6. -/
theorem_wanted arrayR_eq_closedForm (k m : ℕ) (hm1 : 1 ≤ m)
    (hmk : m ≤ k) :
    (arrayR k m : ℚ) =
      (2 : ℚ) ^ (2 * k + m - 1) * (Nat.factorial m : ℚ) *
        ∑ b ∈ Finset.univ.filter
            (fun b : Fin k → Fin (k + 1) =>
              (∑ r : Fin k, (r.val + 1) * (b r).val) = k ∧
              (∑ r : Fin k, (b r).val) = m),
          ((Nat.factorial (2 * k) : ℚ) /
            ∏ r : Fin k, (Nat.factorial (b r).val : ℚ)) *
            ∏ r : Fin k,
              (1 / ((4 : ℚ) ^ (r.val + 1) *
                (Nat.factorial (2 * (r.val + 1)) : ℚ))) ^ ((b r).val)

/-- **Sum of $i \binom{i+k-1}{2k-1}$.** For all natural numbers $k \ge 1$ and $n \ge 1$,
$$\sum_{i=1}^{n} i \binom{i + k - 1}{2k - 1} = \frac{k(2n + 1)}{2k + 1} \binom{n + k}{2k}.$$

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 7. -/
theorem_wanted sum_mul_choose_eq (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n,
      (i : ℚ) * (Nat.choose (i + k - 1) (2 * k - 1) : ℚ)) =
      ((k : ℚ) * (2 * (n : ℚ) + 1) / (2 * (k : ℚ) + 1)) *
        (Nat.choose (n + k) (2 * k) : ℚ)

/-- **Odd power sums in terms of $\binom{n+m}{2m-1}$.** For natural numbers $k \ge 1$ and $n$,
write $S_{2k-1}(n) = 1^{2k-1} + 2^{2k-1} + \dots + n^{2k-1}$, let
$R(p, q) = \sum_{j=0}^{q} (-1)^j \binom{2q}{j} (q - j)^{2p}$, and let $Q_{k,1}(n) = n^{2k-1}$ and
$Q_{k,m}(n) = 2 \sum_{j=m}^{k} \binom{2k-1}{2j-2} R(j-1, m-1)\, n^{2k-2j+1}$ for $m \ge 2$. Then
$2^{2k-1} S_{2k-1}(n) = \sum_{m=1}^{k} Q_{k,m}(n) \binom{n+m}{2m-1}$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Theorem 10. -/
theorem_wanted pow_mul_powerSum_odd_eq_sum (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    (2 : ℚ) ^ (2 * k - 1) * powerSum (2 * k - 1) n =
      ∑ m ∈ Finset.Icc 1 k,
        thmQ k m n * (Nat.choose (n + m) (2 * m - 1) : ℚ)

/-- **Faulhaber form of the even power sums.** For all natural numbers $k \ge 1$ and $n$,
writing $S_j(n) = 1^j + 2^j + \cdots + n^j$ for the power sums and $b_{k,r}$ for the Faulhaber
coefficients of Proposition 12, the rational numbers satisfy
$S_{2k}(n) = S_2(n) \sum_{r=1}^{k} b_{k,r} \, S_1(n)^{r-1}$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 12. -/
theorem_wanted powerSum_even_faulhaber (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    powerSum (2 * k) n =
      powerSum 2 n * ∑ r ∈ Finset.Icc 1 k,
        faulhaberB k r * (powerSum 1 n) ^ (r - 1)

/-- **Faulhaber form of the odd power sums.** For all natural numbers $k \ge 1$ and $n$,
writing $S_j(n) = 1^j + 2^j + \cdots + n^j$ for the power sums and $c_{k,r}$ for the Faulhaber
coefficients of Proposition 12, the rational numbers satisfy
$S_{2k+1}(n) = S_1(n)^2 \sum_{r=1}^{k} c_{k,r} \, S_1(n)^{r-1}$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 12. -/
theorem_wanted powerSum_odd_faulhaber (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    powerSum (2 * k + 1) n =
      (powerSum 1 n) ^ 2 * ∑ r ∈ Finset.Icc 1 k,
        faulhaberC k r * (powerSum 1 n) ^ (r - 1)

/-- **Vanishing alternating sum of the A304330 array.** For every natural number $k \ge 2$,
$$\sum_{m=1}^{k} (-1)^m \frac{((m-1)!)^2}{(2m)!} R(k, m) = 0,$$
where $R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$ is the array of OEIS A304330.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 15. -/
theorem_wanted sum_neg_factorial_sq_div_arrayR_eq_zero (k : ℕ)
    (hk : 2 ≤ k) :
    (∑ m ∈ Finset.Icc 1 k,
      (-1 : ℚ) ^ m *
        ((Nat.factorial (m - 1) : ℚ) ^ 2 /
          (Nat.factorial (2 * m) : ℚ)) * (arrayR k m : ℚ)) = 0

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
