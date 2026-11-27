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
`n = 0` as well; Lemma 4 keeps the paper's `n ≥ 1`.
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
public import MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

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

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
