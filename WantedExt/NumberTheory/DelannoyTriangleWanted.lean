/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Congruence properties for the Delannoy triangle coefficients

Statements from Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", *Journal of Integer Sequences* 29
(2026), Article 26.5.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Djadi/djadi6.html>).

The Delannoy triangle coefficient `C(n, k)_{[2]}` is
the Delannoy number `D(k, n - k)
= ∑_j C(k, j) C(n - k, j) 2^j` (this reading, rather
than `D(n, k)`, is forced by Theorems 1 and 9, both
verified numerically under it). For `k ≤ n` this
agrees with the existing
`MetaMathlibExt.ordinaryRiordanPascalLikeMatrix n k 1`
(the `r = 1` case of that Riordan array is documented
there as the Delannoy triangle; agreement checked
numerically for `n, k ≤ 9`), which is used below;
all statements only use `k ≤ n`. The central Delannoy
number `D_k = ∑_j C(k, j)^2 2^j` is the existing
`MetaMathlibExt.binomialPowerSeq 1 1 k`
`= ∑_j C(k, j) C(k + j, j)` (agreement checked
numerically for `k ≤ 11`). Also `q_p(2)` is the
existing `Int.fermatQuotient`, and the harmonic
numbers are taken in `ZMod m` (all denominators are
units at the stated ranges). All congruences were
verified numerically at small primes.

Not stated (see the source audit table): Lemma 12,
whose sequence `T_k(b, c)` is not defined in the
extracted statements.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix
public import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
public import MathlibExt.NumberTheory.FermatQuotient

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

/-- **Harmonic numbers modulo $m$.** For natural numbers $m$ and $k$, the harmonic number
$H_k$ modulo $m$ is the residue $\sum_{i=1}^{k} i^{-1}$ in $\mathbb{Z}/m\mathbb{Z}$, where
$i^{-1}$ is the inverse of $i$ modulo $m$ when $i$ is coprime to $m$; for other $i$ it is the
conventional value that Mathlib assigns to the inverse of a non-unit. -/
def harmonicMod (m k : ℕ) : ZMod m :=
  ∑ i ∈ Finset.Icc 1 k, (i : ZMod m)⁻¹

/-- **Harmonic numbers of order two modulo $m$.** For natural numbers $m$ and $k$, the
harmonic number $H_{k,2}$ of order two modulo $m$ is the residue $\sum_{i=1}^{k} (i^2)^{-1}$
in $\mathbb{Z}/m\mathbb{Z}$, where $(i^2)^{-1}$ is the inverse of $i^2$ modulo $m$ when $i$ is
coprime to $m$; for other $i$ it is the conventional value that Mathlib assigns to the
inverse of a non-unit. -/
def harmonic2Mod (m k : ℕ) : ZMod m :=
  ∑ i ∈ Finset.Icc 1 k, ((i : ZMod m) ^ 2)⁻¹

/-- **Delannoy triangle entries $T(2p, p; 1)$ and $T(2p-1, p-1; 1)$ modulo $p^3$.** Let
$p \ge 5$ be a prime, let $q_p(2) = (2^{p-1} - 1)/p$ be the Fermat quotient of $2$, and let
$T(n, k; 1)$ denote the entry of the ordinary Riordan Pascal-like triangle with $r = 1$ (the
Delannoy triangle). Then
$$T(2p, p; 1) \equiv 3 + 2p\,q_p(2) - p^2 q_p(2)^2 \pmod{p^3}$$
and
$$T(2p-1, p-1; 1) \equiv 1 + 2p\,q_p(2) - p^2 q_p(2)^2 \pmod{p^3}.$$

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Theorem 1. -/
theorem_wanted delannoy_two_mul (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
          (2 * p) p 1 : ZMod (p ^ 3)) =
        3 + 2 * (p : ZMod (p ^ 3)) *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) -
          (p : ZMod (p ^ 3)) ^ 2 *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) ^ 2 ∧
      (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
            (2 * p - 1) (p - 1) 1 : ZMod (p ^ 3)) =
        1 + 2 * (p : ZMod (p ^ 3)) *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) -
          (p : ZMod (p ^ 3)) ^ 2 *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) ^ 2

/-- **Delannoy triangle entry $T(np-1, p-1; 1)$ modulo $p^3$.** Let $p \ge 5$ be a prime and
$n \ge 1$ a natural number, let $q_p(2) = (2^{p-1} - 1)/p$ be the Fermat quotient of $2$, and
let $T(a, b; 1)$ denote the entry of the ordinary Riordan Pascal-like triangle with $r = 1$
(the Delannoy triangle). Then
$$T(np - 1, p - 1; 1) \equiv 1 + (n - 1)\,p\,q_p(2)\,\bigl(2 - p\,q_p(2)\bigr) \pmod{p^3}.$$

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Theorem 4. -/
theorem_wanted delannoy_mul_sub_one (p n : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
          (n * p - 1) (p - 1) 1 : ZMod (p ^ 3)) =
      1 + ((n : ZMod (p ^ 3)) - 1) * (p : ZMod (p ^ 3)) *
          (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) *
        (2 - (p : ZMod (p ^ 3)) *
          (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)))

/-- **Expansion of $\binom{sp-1}{k}$ modulo $p^3$.** Let $p$ be an odd prime, $s$ an integer
and $k$ a natural number with $1 \le k \le p - 1$, and let $H_k = \sum_{i=1}^{k} i^{-1}$ and
$H_{k,2} = \sum_{i=1}^{k} (i^2)^{-1}$ be the harmonic numbers of orders one and two in
$\mathbb{Z}/p^3\mathbb{Z}$. Then in $\mathbb{Z}/p^3\mathbb{Z}$
$$
\frac{1}{k!} \prod_{i=1}^{k} (sp - i) =
(-1)^k \Bigl(1 - sp\,H_k + \frac{s^2 p^2}{2} \bigl(H_k^2 - H_{k,2}\bigr)\Bigr),
$$
where $1/k!$ and $1/2$ are inverses in $\mathbb{Z}/p^3\mathbb{Z}$; the left side is the
binomial coefficient $\binom{sp-1}{k}$.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 5. -/
theorem_wanted choose_mul_sub_one_mod (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (s : ℤ) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ p - 1) :
    (∏ i ∈ Finset.Icc 1 k,
        ((s * (p : ℤ) - (i : ℤ)) : ZMod (p ^ 3))) *
        ((Nat.factorial k : ZMod (p ^ 3)))⁻¹ =
      (-1) ^ k * (1 - (s : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) *
          harmonicMod (p ^ 3) k +
        (s : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) ^ 2 *
          (2 : ZMod (p ^ 3))⁻¹ *
          (harmonicMod (p ^ 3) k ^ 2 - harmonic2Mod (p ^ 3) k))

/-- **Sums of $2^k/k$ and $2^k/k^2$ over $1 \le k \le p - 1$.** Let $p > 3$ be a prime and let
$q_p(2) = (2^{p-1} - 1)/p$ be the Fermat quotient of $2$. Then
$$\sum_{k=1}^{p-1} \frac{2^k}{k} \equiv -2\,q_p(2) \pmod{p^2}$$
and
$$\sum_{k=1}^{p-1} \frac{2^k}{k^2} \equiv -q_p(2)^2 \pmod{p},$$
where $1/k$ is the inverse of $k$ modulo $p^2$ and $1/k^2$ the inverse of $k^2$ modulo $p$.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 6. -/
theorem_wanted sum_two_pow_div (p : ℕ) (hp : p.Prime)
    (hp3 : 3 < p) (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (∑ k ∈ Finset.Icc 1 (p - 1),
        (2 : ZMod (p ^ 2)) ^ k * (k : ZMod (p ^ 2))⁻¹) =
        -2 * (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 2)) ∧
      (∑ k ∈ Finset.Icc 1 (p - 1),
          (2 : ZMod p) ^ k * ((k : ZMod p) ^ 2)⁻¹) =
        -((Int.fermatQuotient p hp 2 h2p : ZMod p)) ^ 2

/-- **Sum of $H_k 2^k / k$ over $1 \le k \le p - 1$ modulo $p$.** Let $p \ge 5$ be a prime, let
$q_p(2) = (2^{p-1} - 1)/p$ be the Fermat quotient of $2$, and let $H_k = \sum_{i=1}^{k} 1/i$
be the harmonic number modulo $p$, where $1/i$ is the inverse of $i$ modulo $p$. Then
$$\sum_{k=1}^{p-1} \frac{H_k\, 2^k}{k} \equiv -q_p(2)^2 \pmod{p}.$$

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 7. -/
theorem_wanted sum_harmonic_two_pow_div (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (∑ k ∈ Finset.Icc 1 (p - 1),
        harmonicMod p k * (2 : ZMod p) ^ k * (k : ZMod p)⁻¹) =
      -((Int.fermatQuotient p hp 2 h2p : ZMod p)) ^ 2

/-- **Sum of the Delannoy triangle entries in rows $0$ to $p - 1$ modulo $p$.** Let $p$ be an
odd prime and let $T(n, k; 1)$ denote the entry of the ordinary Riordan Pascal-like triangle
with $r = 1$ (the Delannoy triangle). Then
$$\sum_{n=0}^{p-1} \sum_{k=0}^{n} T(n, k; 1) \equiv \left(\frac{2}{p}\right) \pmod{p},$$
where $\left(\frac{2}{p}\right)$ is the Legendre symbol.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Theorem 9. -/
theorem_wanted sum_delannoy (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (∑ n ∈ Finset.range p, ∑ k ∈ Finset.range (n + 1),
        (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
            n k 1 : ZMod p)) =
      (legendreSym p 2 : ZMod p)

/-- **Reflection congruence for binomial coefficients modulo a prime.** For a prime $p$ and
natural numbers $j$ and $k$ with $j \le k \le p - 2$,
$$\binom{p-j}{k+1} + (-1)^k \binom{k+j}{k+1} \equiv 0 \pmod{p}.$$

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 11. -/
theorem_wanted choose_add_choose_mod (p j k : ℕ)
    (hp : p.Prime) (hjk : j ≤ k) (hk : k ≤ p - 2) :
    (Nat.choose (p - j) (k + 1) : ZMod p) +
        (-1) ^ k * (Nat.choose (k + j) (k + 1) : ZMod p) = 0

/-- **A binomial sum through central Delannoy numbers.** For every natural number $k$,
$$4 \sum_{j=0}^{k} \binom{k}{j} \binom{k+j}{k+1} = D_{k+1} - 3 D_k,$$
where $D_n = A_{1,1}(n) = \sum_{i=0}^{n} \binom{n}{i} \binom{n+i}{i}$ is the binomial-power
number with $r = s = 1$, that is, the $n$-th central Delannoy number.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 13. -/
theorem_wanted sum_choose_choose_binomialPowerSeq (k : ℕ) :
    4 * (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j * Nat.choose (k + j) (k + 1) : ℤ)) =
      (MetaMathlibExt.binomialPowerSeq 1 1 (k + 1) : ℤ) -
        3 * (MetaMathlibExt.binomialPowerSeq 1 1 k : ℤ)

end MathlibExt.NumberTheory.DelannoyTriangleWanted
