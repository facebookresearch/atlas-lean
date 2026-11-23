/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.Combinatorics.AssociatedStirlingEulerian

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Circular Eulerian numbers are shifted Eulerian numbers.** An excedance of a permutation
$\sigma$ of $n$ objects $1, \dots, n$ is an index $i$ with $\sigma(i) > i$. Let $C_{n,m}$ be the
number of circular permutations of $n$ objects (permutations with a single cycle through all
$n \ge 1$ points) with exactly $m$ excedances, and let $A_{n,m}$ be the number of permutations of
$n$ objects with exactly $m$ excedances (the $0$-associated Stirling Eulerian number, which
counts the permutations all of whose cycle lengths exceed $0$, that is, all permutations). Then
$C_{1,0} = 1$; for all $n \ge 2$ and $1 \le m \le n$ we have $C_{n,m} = A_{n-1,m-1}$; and for
every $n \ge 2$ the polynomial identity $C_n(x) = x\,A_{n-1}(x)$ holds in $\mathbb{Z}[x]$, where
$C_n(x) = \sum_{m=0}^{n} C_{n,m} x^m$ and $A_{n-1}(x) = \sum_{m=0}^{n-1} A_{n-1,m} x^m$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 5 (`jis-2025-25.5.7-thm-5`). -/
public theorem_wanted circularEulerian_eq_eulerian :
    circularEulerian 1 0 = 1 ∧
    (∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ n →
      circularEulerian n m = rAssociatedStirlingEulerian 0 (n - 1) (m - 1)) ∧
    ∀ n : ℕ, 2 ≤ n →
      (∑ m ∈ Finset.range (n + 1), (circularEulerian n m : ℤ[X]) * X ^ m) =
        X * ∑ m ∈ Finset.range n,
          (rAssociatedStirlingEulerian 0 (n - 1) m : ℤ[X]) * X ^ m

/-- **Recurrence for permutations with cycle lengths at most r, by excedances.** Let $r \ge 2$.
An excedance of a permutation $\sigma$ is an $i$ with $\sigma(i) > i$. Let $A^{r-}_{n,m}$ be the
number of permutations of $\{1, \dots, n\}$ all of whose cycles have length at most $r$ and which
have exactly $m$ excedances, and let $C_{\ell,i}$ be the number of circular permutations of
$\ell$ objects (permutations with a single cycle through all points) with exactly $i$
excedances. Then for all natural numbers $m \le n$,
$$A^{r-}_{n+1,m} = \sum_{j=1}^{r-1} \binom{n}{j} \sum_{i=0}^{m} C_{j+1,i}\, A^{r-}_{n-j,m-i} +
A^{r-}_{n,m}.$$
A term with $j > n$ vanishes because $\binom{n}{j} = 0$; there $n - j$ is read as $0$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 10 (`jis-2025-25.5.7-thm-10`). -/
public theorem_wanted rMinusAssociatedStirlingEulerian_succ (r n m : ℕ)
    (hr : 2 ≤ r) (hm : m ≤ n) :
    rMinusAssociatedStirlingEulerian r (n + 1) m =
      ∑ j ∈ Finset.Icc 1 (r - 1), n.choose j *
          ∑ i ∈ Finset.range (m + 1),
            circularEulerian (j + 1) i * rMinusAssociatedStirlingEulerian r (n - j) (m - i) +
        rMinusAssociatedStirlingEulerian r n m

/-- **Recurrence for the $r$-associated Stirling Eulerian numbers.** For natural numbers $r$, $n$,
$m$ let $A^r_{n,m}$ be the number of permutations $\sigma$ of $\{0, \dots, n-1\}$ with exactly
$m$ excedances (points $i$ with $\sigma(i) > i$) all of whose cycles (fixed points counted as
cycles of length one) have length greater than $r$, and for natural numbers $a$, $b$ let
$C_{a,b}$ be the circular Eulerian number, the number of permutations of $\{0, \dots, a-1\}$,
$a \ge 1$, that consist of a single cycle through all points and have exactly $b$ excedances
($C_{0,b} = 0$). If $m \le n$ and $n \ge r + 1$, then
$$A^r_{n,m} = m A^r_{n-1,m} + (n-m) A^r_{n-1,m-1} +
\binom{n-1}{r} \sum_{s=0}^{m} C_{r+1,s} A^r_{n-r-1,m-s},$$
where the term $(n-m) A^r_{n-1,m-1}$ is read as $0$ when $m = 0$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 30 (`jis-2025-25.5.7-thm-30`). -/
public theorem_wanted rAssociatedStirlingEulerian_recurrence (r n m : ℕ)
    (hm : m ≤ n) (hn : r + 1 ≤ n) :
    rAssociatedStirlingEulerian r n m =
      m * rAssociatedStirlingEulerian r (n - 1) m +
        (if m = 0 then 0 else (n - m) * rAssociatedStirlingEulerian r (n - 1) (m - 1)) +
        (n - 1).choose r *
          ∑ s ∈ Finset.range (m + 1),
            circularEulerian (r + 1) s * rAssociatedStirlingEulerian r (n - r - 1) (m - s)

/-- **Convolution recurrence for the $r$-associated Stirling Eulerian numbers.** For natural
numbers $r$, $n$, $m$ let $A^r_{n,m}$ be the number of permutations $\sigma$ of
$\{0, \dots, n-1\}$ with exactly $m$ excedances (points $i$ with $\sigma(i) > i$) all of whose
cycles (fixed points counted as cycles of length one) have length greater than $r$, and for
natural numbers $a$, $b$ let $C_{a,b}$ be the circular Eulerian number, the number of
permutations of $\{0, \dots, a-1\}$, $a \ge 1$, that consist of a single cycle through all
points and have exactly $b$ excedances ($C_{0,b} = 0$). If $r \ge 1$, $m \le n$ and
$n \ge r + 1$, then
$$A^r_{n+1,m} = \sum_{j=r}^{n} \binom{n}{j} \sum_{i=1}^{m} C_{j+1,i} A^r_{n-j,m-i}.$$

The hypothesis $r \ge 1$ is needed: for $r = 0$, $n = 1$, $m = 0$ the left side is
$A^0_{2,0} = 1$ (the identity) while the right side is $0$, every inner sum over $1 \le i \le 0$
being empty.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 31 (`jis-2025-25.5.7-thm-31`). -/
public theorem_wanted rAssociatedStirlingEulerian_succ (r n m : ℕ) (hr : 1 ≤ r)
    (hm : m ≤ n) (hn : r + 1 ≤ n) :
    rAssociatedStirlingEulerian r (n + 1) m =
      ∑ j ∈ Finset.Icc r n, n.choose j *
        ∑ i ∈ Finset.Icc 1 m,
          circularEulerian (j + 1) i * rAssociatedStirlingEulerian r (n - j) (m - i)

/-- **Derangements weighted by excedances and cycle weight $-2$.** Let $n \ge 1$. For a
permutation $\sigma$ let $e(\sigma)$ be its number of excedances (indices $i$ with
$\sigma(i) > i$) and $c(\sigma)$ its number of cycles. Summing over the derangements $\sigma$ of
$n$ objects (permutations without fixed points), the polynomial
$(x - 1)^2 \sum_{\sigma} x^{e(\sigma)} (-2)^{c(\sigma)}$ equals
$-2x\,\big(-2^{n-1} x - 2^{n-1} x^{n-1} + (x+1)^n\big)$ in $\mathbb{Z}[x]$; that is,
$\sum_{\sigma} x^{e(\sigma)} (-2)^{c(\sigma)} = -2x(-2^{n-1}x - 2^{n-1}x^{n-1} + (x+1)^n)/(x-1)^2$
with the denominator cleared.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 55 (`jis-2025-25.5.7-cor-55`). -/
public theorem_wanted derangement_excedance_cycle_sum_neg_two (n : ℕ) (hn : 1 ≤ n) :
    (X - 1) ^ 2 *
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ≠ i),
          (X ^ excedanceCount n σ * (-2) ^ σ.cycleType.card : ℤ[X]) =
      -2 * X * (-(2 ^ (n - 1)) * X - 2 ^ (n - 1) * X ^ (n - 1) + (X + 1) ^ n)


/-! ### Exponential generating functions (Theorems 6-35, Corollaries 12-44)

Throughout, `R` is a commutative `ℚ`-algebra and `x q : R` (take `R = ℚ[x, q]` for the
paper's indeterminates). `permExcedanceCycleEGF P x q` is the paper's
`∑_n ∑_{σ ∈ P_n} x^{e(σ)} q^{c(σ)} u^n/n!` (at `q = 1` the series `P(x,u)`),
`A_j(x) = ∑_{σ ∈ S_j} x^{e(σ)}` is written out as a sum over `Equiv.Perm (Fin j)`, and
`exp F` for `F` with zero constant term is `PowerSeries.subst F (PowerSeries.exp R)`.
A statement `L = ln F` is rendered as `exp L = F` with `L(0) = 0`, and `F^q` as
`exp (q ln F)`: for every `L` with zero constant term and `exp L = F`, the claim holds
with `ln F := L` (over a `ℚ`-algebra such `L` exists and is unique). -/

/-- **Logarithm of the Eulerian generating function.** Let $R$ be a commutative $\mathbb{Q}$-algebra
and $x \in R$, and work with formal power series in $u$ over $R$. For a permutation $\sigma$ write
$e(\sigma)$ for its number of excedances (points $i$ with $\sigma(i) > i$), and let $S_n$ be the
set of permutations of $\{0, \dots, n-1\}$. Let
$A(x,u) = \sum_{n \ge 0} \sum_{\sigma \in S_n} x^{e(\sigma)} u^n/n!$ be the exponential generating
function of excedances over all permutations, and let $C(x,u)$ be the same sum restricted to
circular permutations, that is, to the permutations of $n \ge 1$ points that consist of a single
cycle. Then $\exp C(x,u) = A(x,u)$, that is, $C(x,u) = \ln A(x,u)$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 6 (`jis-2025-25.5.7-thm-6`). -/
public theorem_wanted exp_circularPermEGF_eq_permEGF {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) :
    PowerSeries.subst
        (permExcedanceCycleEGF (fun n σ => 0 < n ∧ ∀ i j, σ.SameCycle i j) x 1)
        (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1

/-- **Excedance generating function of circular permutations of at most $r$ objects.** Let
$R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 1$. For a permutation $\sigma$
let $e(\sigma)$ be its number of excedances (indices $i$ with $\sigma(i) > i$), and for
$j \ge 0$ let $A_j(x) = \sum_{\sigma} x^{e(\sigma)}$, summed over all permutations $\sigma$ of
$j$ objects. Then in $R[[u]]$
$\sum_{n=1}^{r} \sum_{\sigma} x^{e(\sigma)} u^n/n! =
u + x \sum_{j=1}^{r-1} A_j(x)\,u^{j+1}/(j+1)!$, where the inner sum on the left runs over the
circular permutations $\sigma$ of $n$ objects (those with a single cycle through all $n$
points).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 7 (`jis-2025-25.5.7-thm-7`). -/
public theorem_wanted circularRMinusPermEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 1 ≤ r) :
    permExcedanceCycleEGF (fun n σ => (0 < n ∧ ∀ i j, σ.SameCycle i j) ∧ n ≤ r) x 1 =
      PowerSeries.X + ∑ j ∈ Finset.Icc 1 (r - 1),
        PowerSeries.C ((((j + 1).factorial : ℚ)⁻¹) •
          (x * ∑ σ : Equiv.Perm (Fin j), x ^ excedanceCount j σ)) * PowerSeries.X ^ (j + 1)

/-- **Excedance generating function of circular permutations of $r$ objects.** Let $R$ be a
commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 2$. For a permutation $\sigma$ let
$e(\sigma)$ be its number of excedances (indices $i$ with $\sigma(i) > i$), and for $j \ge 0$ let
$A_j(x) = \sum_{\sigma} x^{e(\sigma)}$, summed over all permutations $\sigma$ of $j$ objects. Then
the power series $\sum_{\sigma} x^{e(\sigma)} u^r/r!$ in $R[[u]]$, summed over the circular
permutations $\sigma$ of $r$ objects (those with a single cycle through all $r$ points), equals
$x\,A_{r-1}(x)\,u^r/r!$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 8 (`jis-2025-25.5.7-thm-8`). -/
public theorem_wanted circularRCyclePermEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (fun n σ => (0 < n ∧ ∀ i j, σ.SameCycle i j) ∧ n = r) x 1 =
      PowerSeries.C (((r.factorial : ℚ)⁻¹) •
        (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
        PowerSeries.X ^ r

/-- **Excedance generating function of circular permutations of more than $r$ objects.** Let $R$
be a commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 2$, and work with formal power series
in $u$ over $R$. For a permutation $\sigma$ let $e(\sigma)$ be its number of excedances (indices
$i$ with $\sigma(i) > i$). For $j \ge 0$ let $A_j(x) = \sum_{\sigma} x^{e(\sigma)}$, summed over
all permutations $\sigma$ of $j$ objects, and let $A(x,u) = \sum_{n \ge 0} A_n(x)\, u^n/n!$. Let
$C^{r+}(x,u) = \sum_{n \ge r+1} \sum_{\sigma} x^{e(\sigma)} u^n/n!$, where the inner sum runs over
the circular permutations $\sigma$ of $n$ objects (those with a single cycle through all $n$
points). Then
$$\exp C^{r+}(x,u) =
A(x,u) \exp\Bigl(-u - x \sum_{i=1}^{r-1} A_i(x)\, \frac{u^{i+1}}{(i+1)!}\Bigr).$$

This is the identity
$C^{r+}(x,u) = \ln\bigl(A(x,u) \exp(-u - x \sum_{i=1}^{r-1} A_i(x)\, u^{i+1}/(i+1)!)\bigr)$
written in exponential form.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 9 (`jis-2025-25.5.7-thm-9`). -/
public theorem_wanted exp_circularRPlusPermEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 2 ≤ r) :
    PowerSeries.subst
        (permExcedanceCycleEGF (fun n σ => (0 < n ∧ ∀ i j, σ.SameCycle i j) ∧ r + 1 ≤ n) x 1)
        (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1 *
        PowerSeries.subst
          (-(PowerSeries.X + ∑ i ∈ Finset.Icc 1 (r - 1),
            PowerSeries.C ((((i + 1).factorial : ℚ)⁻¹) •
              (x * ∑ σ : Equiv.Perm (Fin i), x ^ excedanceCount i σ)) *
              PowerSeries.X ^ (i + 1)))
          (PowerSeries.exp R)

/-- **Exponential generating function of permutations with cycle lengths at most $r$.** Let $R$
be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r \ge 2$ be a natural number. For a
permutation $\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$ for its number of excedances
(indices $i$ with $\sigma(i) > i$), and let $A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Let
$A^{r-}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles, fixed points included, have
at most $r$ elements. Then
$$A^{r-}(x,u) = \exp\left(u + x \sum_{j=1}^{r-1} \frac{A_j(x)\, u^{j+1}}{(j+1)!}\right),$$
where $\exp$ of a series with zero constant term is its substitution into the exponential series.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 11 (`jis-2025-25.5.7-thm-11`). -/
public theorem_wanted rMinusAssociatedPermEGF_eq_exp {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1 =
      PowerSeries.subst
        (PowerSeries.X + ∑ j ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C ((((j + 1).factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin j), x ^ excedanceCount j σ)) *
            PowerSeries.X ^ (j + 1))
        (PowerSeries.exp R)

/-- **Logarithm of the generating function of permutations with short cycles.** Let $R$ be a
commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 2$ an integer, and work with formal power
series in $u$ over $R$. For a permutation $\sigma$ write $e(\sigma)$ for its number of excedances
(points $i$ with $\sigma(i) > i$). Let
$C^{r-}(x,u) = \sum_{n=1}^{r} \sum_{\sigma} x^{e(\sigma)} u^n/n!$, the inner sum over the
permutations of $n$ points that consist of a single cycle, and let
$A^{r-}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n!$, the inner sum over the
permutations of $n$ points all of whose cycles, fixed points included, have length at most $r$.
Then $\exp C^{r-}(x,u) = A^{r-}(x,u)$, that is, $C^{r-}(x,u) = \ln A^{r-}(x,u)$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 12 (`jis-2025-25.5.7-cor-12`). -/
public theorem_wanted exp_circularRMinusPermEGF_eq_rMinusAssociatedPermEGF {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (r : ℕ) (hr : 2 ≤ r) :
    PowerSeries.subst
        (permExcedanceCycleEGF (fun n σ => (0 < n ∧ ∀ i j, σ.SameCycle i j) ∧ n ≤ r) x 1)
        (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1

/-- **Primitive of the Eulerian generating function.** Let $R$ be a commutative
$\mathbb{Q}$-algebra and $x \in R$, and work with formal power series in $u$ over $R$. For a
permutation $\sigma$ write $e(\sigma)$ for its number of excedances (points $i$ with
$\sigma(i) > i$), let $S_n$ be the set of permutations of $\{0, \dots, n-1\}$, and let
$A(x,u) = \sum_{n \ge 0} \sum_{\sigma \in S_n} x^{e(\sigma)} u^n/n!$. If $P(u)$ is a formal power
series in $u$ over $R$ with zero constant term whose derivative is $A(x,u)$, then
$\exp\bigl(x P(u) - (x-1)u\bigr) = A(x,u)$.

This is the paper's $P(x,u) = (\ln A(x,u) + u(x-1))/x$ with the division by $x$ cleared and the
logarithm exponentiated.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 13 (`jis-2025-25.5.7-cor-13`). -/
public theorem_wanted exp_eulerianEGF_primitive {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (P : PowerSeries R) (hP0 : PowerSeries.constantCoeff P = 0)
    (hP : PowerSeries.derivative (R := R) P = permExcedanceCycleEGF (fun _ _ => True) x 1) :
    PowerSeries.subst (PowerSeries.C x * P - PowerSeries.C (x - 1) * PowerSeries.X)
        (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1

/-- **Generating function of permutations with cycle lengths at most $r$ and $k$ cycles.** Let
$R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r, k$ be natural numbers with
$r \ge 2$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$ for its number of
excedances (indices $i$ with $\sigma(i) > i$) and $c(\sigma)$ for its number of cycles, fixed
points included, and let $A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Let
$A^{r-}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles, fixed points included, have
at most $r$ elements, and let $A^{r-}_k(x,u)$ be the same series with the inner sum restricted to
those $\sigma$ with $c(\sigma) = k$. Then
$$A^{r-}_k(x,u) = \frac{1}{k!}\Big(u + x \sum_{j=1}^{r-1} \frac{A_j(x)\, u^{j+1}}{(j+1)!}\Big)^k,$$
and $A^{r-}_k(x,u) = L^k/k!$ for every $L \in R[[u]]$ with zero constant term and
$\exp(L) = A^{r-}(x,u)$, where $\exp$ of a series with zero constant term is its substitution
into the exponential series.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 14 (`jis-2025-25.5.7-thm-14`). -/
public theorem_wanted rMinusAssociatedPermEGF_cycleCount_eq {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (r k : ℕ) (hr : 2 ≤ r) :
    (∀ L : PowerSeries R, PowerSeries.constantCoeff L = 0 →
      PowerSeries.subst L (PowerSeries.exp R) =
        permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1 →
      permExcedanceCycleEGF
          (fun n σ => IsRMinusAssociatedCyclePerm r n σ ∧ cycleQuotientCount σ = k) x 1 =
        ((k.factorial : ℚ)⁻¹) • L ^ k) ∧
    permExcedanceCycleEGF
        (fun n σ => IsRMinusAssociatedCyclePerm r n σ ∧ cycleQuotientCount σ = k) x 1 =
      ((k.factorial : ℚ)⁻¹) •
        (PowerSeries.X + ∑ j ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C ((((j + 1).factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin j), x ^ excedanceCount j σ)) *
            PowerSeries.X ^ (j + 1)) ^ k

/-- **Cycle-counting generating function for cycle lengths at most r.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, let $x, q \in R$ and let $r \ge 2$. For a permutation $\sigma$ write
$e(\sigma)$ for its number of excedances (the $i$ with $\sigma(i) > i$) and $c(\sigma)$ for its
number of cycles, fixed points included, and for $j \ge 1$ let
$A_j(x) = \sum_{\sigma} x^{e(\sigma)}$, summed over the permutations $\sigma$ of
$\{1, \dots, j\}$. Then, as formal power series in $u$ over $R$,
$$\sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} =
\exp\Bigl(q\Bigl(u + x \sum_{j=1}^{r-1} A_j(x) \frac{u^{j+1}}{(j+1)!}\Bigr)\Bigr),$$
where the inner sum on the left runs over the permutations $\sigma$ of $\{1, \dots, n\}$ all of
whose cycles have length at most $r$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 15 (`jis-2025-25.5.7-thm-15`). -/
public theorem_wanted rMinusAssociatedPermEGF_q_eq_exp {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (r : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x q =
      PowerSeries.subst
        (PowerSeries.C q * (PowerSeries.X + ∑ j ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C ((((j + 1).factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin j), x ^ excedanceCount j σ)) *
            PowerSeries.X ^ (j + 1)))
        (PowerSeries.exp R)

/-- **Cycle lengths at most r: the q-analogue is a q-th power.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, let $x, q \in R$ and let $r \ge 2$. For a permutation $\sigma$ write
$e(\sigma)$ for its number of excedances (the $i$ with $\sigma(i) > i$) and $c(\sigma)$ for its
number of cycles, fixed points included, and for $t \in R$ let
$$F_t(u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} t^{c(\sigma)},$$
where the inner sum runs over the permutations $\sigma$ of $\{1, \dots, n\}$ all of whose cycles
have length at most $r$. If $L$ is a formal power series in $u$ over $R$ with constant term $0$
and $\exp(L) = F_1(u)$, then $F_q(u) = \exp(qL)$. This is the identity $F_q = F_1^{\,q}$ with the
power read as $\exp(q \ln F_1)$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 16 (`jis-2025-25.5.7-cor-16`). -/
public theorem_wanted rMinusAssociatedPermEGF_q_eq_pow {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (r : ℕ) (hr : 2 ≤ r) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1) :
    permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x q =
      PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- **Recurrence for $r$-cycle Stirling Eulerian numbers.** An excedance of a permutation
$\sigma$ of $\{0, \dots, N-1\}$ is an index $i$ with $\sigma(i) > i$. Let $A^{(r)}_{N,M}$ be the
number of permutations of $\{0, \dots, N-1\}$ with exactly $M$ excedances all of whose cycles,
fixed points included, have exactly $r$ elements, and let $C_{r,k}$ be the number of permutations
of $\{0, \dots, r-1\}$ with exactly $k$ excedances that consist of a single cycle through all $r$
points. Then for all natural numbers $r$, $n$, $m$ with $r \ge 2$ and $m \le n$,
$$A^{(r)}_{n+1,m} = \binom{n}{r-1} \sum_{k=1}^{m} C_{r,k}\, A^{(r)}_{n-(r-1),\,m-k},$$
where $n - (r-1)$ is truncated subtraction, equal to $0$ when $n < r - 1$ (harmless, since then
$\binom{n}{r-1} = 0$).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 20 (`jis-2025-25.5.7-thm-20`). -/
public theorem_wanted rCycleStirlingEulerian_succ (r n m : ℕ) (hr : 2 ≤ r) (hm : m ≤ n) :
    rCycleStirlingEulerian r (n + 1) m =
      n.choose (r - 1) * ∑ k ∈ Finset.Icc 1 m,
        circularEulerian r k * rCycleStirlingEulerian r (n - (r - 1)) (m - k)

/-- **Excedance generating function of permutations with all cycles of length $r$.** Let $R$ be
a commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 2$. For a permutation $\sigma$ of
$\{0, \dots, n-1\}$ let $\operatorname{exc}(\sigma)$ be the number of points $i$ with
$\sigma(i) > i$, and let $A_{r-1}(x) = \sum_{\sigma} x^{\operatorname{exc}(\sigma)}$, summed
over all permutations of $\{0, \dots, r-2\}$. Let
$A^{(r)}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{\operatorname{exc}(\sigma)} u^n/n!$, the inner
sum over the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles (fixed points
counted as cycles of length one) have length exactly $r$. Then, as formal power series in $u$
over $R$,
$$A^{(r)}(x,u) = \exp\left(\frac{x A_{r-1}(x)\, u^r}{r!}\right).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 21 (`jis-2025-25.5.7-thm-21`). -/
public theorem_wanted rCyclePermEGF_eq_exp {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (IsRCyclePerm r) x 1 =
      PowerSeries.subst
        (PowerSeries.C (((r.factorial : ℚ)⁻¹) •
          (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
          PowerSeries.X ^ r)
        (PowerSeries.exp R)

/-- **Excedance generating function of permutations with $k$ cycles, all of length $r$.** Let
$R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r$, $k$ be natural numbers with
$r \ge 2$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let $\operatorname{exc}(\sigma)$ be
the number of points $i$ with $\sigma(i) > i$, and let
$A_{r-1}(x) = \sum_{\sigma} x^{\operatorname{exc}(\sigma)}$, summed over all permutations of
$\{0, \dots, r-2\}$. Let
$A^{(r)}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{\operatorname{exc}(\sigma)} u^n/n!$, the inner
sum over the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles (fixed points
counted as cycles of length one) have length exactly $r$, and let $A^{(r)}_k(x,u)$ be the same
series with the inner sum restricted to the permutations with exactly $k$ cycles. Then
$$A^{(r)}_k(x,u) = \frac{1}{k!} \left(\frac{x A_{r-1}(x)\, u^r}{r!}\right)^k,$$
and for every formal power series $L$ in $u$ over $R$ with $L(0) = 0$ and
$\exp L = A^{(r)}(x,u)$ also $A^{(r)}_k(x,u) = L^k/k!$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 22 (`jis-2025-25.5.7-thm-22`). -/
public theorem_wanted rCyclePermEGF_cycleCount_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r k : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (fun n σ => IsRCyclePerm r n σ ∧ cycleQuotientCount σ = k) x 1 =
        ((k.factorial : ℚ)⁻¹) •
          (PowerSeries.C (((r.factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
            PowerSeries.X ^ r) ^ k ∧
    ∀ L : PowerSeries R, PowerSeries.constantCoeff L = 0 →
      PowerSeries.subst L (PowerSeries.exp R) = permExcedanceCycleEGF (IsRCyclePerm r) x 1 →
      permExcedanceCycleEGF (fun n σ => IsRCyclePerm r n σ ∧ cycleQuotientCount σ = k) x 1 =
        ((k.factorial : ℚ)⁻¹) • L ^ k

/-- **Cycle-weighted exponential formula for $r$-cycle permutations.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$, and let $r \ge 2$ be a natural number. For a permutation
$\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$ for its number of excedances (indices $i$ with
$\sigma(i) > i$) and $c(\sigma)$ for its number of cycles, fixed points included, and let
$A_{r-1}(x) = \sum_{\sigma \in S_{r-1}} x^{e(\sigma)}$. Call $\sigma$ an $r$-cycle permutation
when every cycle of $\sigma$, fixed points included, has exactly $r$ elements, and let
$A^{(r)}(q,x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n! \in R[[u]]$,
the inner sum over the $r$-cycle permutations $\sigma$ of $\{0, \dots, n-1\}$. Then
$$A^{(r)}(q,x,u) = \exp\left(\frac{q\, x\, A_{r-1}(x)\, u^r}{r!}\right),$$
where $\exp$ of a series with zero constant term is its substitution into the exponential series.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 23 (`jis-2025-25.5.7-thm-23`). -/
public theorem_wanted rCyclePermEGF_q_eq_exp {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) (r : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (IsRCyclePerm r) x q =
      PowerSeries.subst
        (PowerSeries.C q * (PowerSeries.C (((r.factorial : ℚ)⁻¹) •
          (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
          PowerSeries.X ^ r))
        (PowerSeries.exp R)

/-- **Excedance and cycle polynomial of permutations with k cycles, all of length r.** Let $R$ be
a commutative ring, let $x, q \in R$, let $r \ge 2$ and let $n, k \ge 0$. For a permutation
$\pi$ write $e(\pi)$ for its number of excedances (the $i$ with $\pi(i) > i$) and $c(\pi)$ for
its number of cycles, fixed points included, and let $A_{r-1}(x) = \sum_{\sigma} x^{e(\sigma)}$,
summed over the permutations $\sigma$ of $\{1, \dots, r - 1\}$. Summing over the permutations
$\pi$ of $\{1, \dots, n\}$ that have exactly $k$ cycles, all of length exactly $r$,
$$\sum_{\pi} x^{e(\pi)} q^{c(\pi)} = \frac{(rk)!}{(r!)^k\, k!}\, x^k q^k A_{r-1}(x)^k$$
if $n = kr$, and the sum is $0$ otherwise.

The quotient $(rk)!/((r!)^k k!)$ is an exact natural-number division.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 24 (`jis-2025-25.5.7-cor-24`). -/
public theorem_wanted sum_rCyclePerm_cycleCount_eq {R : Type*} [CommRing R] (x q : R)
    (r n k : ℕ) (hr : 2 ≤ r) :
    ∑ σ ∈ Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => IsRCyclePerm r n σ ∧ cycleQuotientCount σ = k),
      x ^ excedanceCount n σ * q ^ cycleQuotientCount σ =
    if n = k * r then
      (((r * k).factorial / (r.factorial ^ k * k.factorial) : ℕ) : R) * x ^ k * q ^ k *
        (∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ) ^ k
    else 0

/-- **Number of permutations with all cycles of length $r$.** Let $r \ge 2$ and $n \ge 0$. The
number of permutations of $n$ objects all of whose cycles, fixed points counted as cycles of
length one, have length exactly $r$ equals $n!/(r^{n/r}\,(n/r)!)$ if $r$ divides $n$, and $0$
otherwise.

When $r$ divides $n$ the quotient is an integer, so the natural-number division is exact.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 25 (`jis-2025-25.5.7-cor-25`). -/
public theorem_wanted card_rCyclePerm (r n : ℕ) (hr : 2 ≤ r) :
    (Finset.univ.filter (IsRCyclePerm r n)).card =
      if r ∣ n then n.factorial / (r ^ (n / r) * (n / r).factorial) else 0

/-- **Exponential generating function for permutations with all cycles of length $r$.** Let
$r \ge 2$ and, for each $n$, let $S_n^r$ be the set of permutations of $\{0, \dots, n-1\}$ all
of whose cycles (fixed points counted as cycles of length one) have length exactly $r$. Then, as
formal power series over $\mathbb{Q}$,
$$\sum_{n \ge 0} |S_n^r| \frac{u^n}{n!} = \exp\left(\frac{u^r}{r}\right).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 26 (`jis-2025-25.5.7-cor-26`). -/
public theorem_wanted rCyclePermCountEGF_eq_exp (r : ℕ) (hr : 2 ≤ r) :
    PowerSeries.mk (fun n => ((Finset.univ.filter (IsRCyclePerm r n)).card : ℚ) /
        n.factorial) =
      PowerSeries.subst (PowerSeries.C ((r : ℚ)⁻¹) * PowerSeries.X ^ r) (PowerSeries.exp ℚ)

/-- **Excedance generating function of permutations with all cycles longer than $r$.** Let $R$
be a commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 1$. For a permutation $\sigma$ of
$\{0, \dots, n-1\}$ let $\operatorname{exc}(\sigma)$ be the number of points $i$ with
$\sigma(i) > i$, let $A_n(x) = \sum_{\sigma} x^{\operatorname{exc}(\sigma)}$, summed over all
permutations of $\{0, \dots, n-1\}$, and let $A(x,u) = \sum_{n \ge 0} A_n(x) u^n/n!$. Let
$A^r(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{\operatorname{exc}(\sigma)} u^n/n!$, the inner sum
over the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles (fixed points counted
as cycles of length one) have length greater than $r$. Then, as formal power series in $u$
over $R$,
$$A^r(x,u) = A(x,u) \exp\left(-u - x \sum_{j=1}^{r-1} \frac{A_j(x)\, u^{j+1}}{(j+1)!}\right).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 32 (`jis-2025-25.5.7-thm-32`). -/
public theorem_wanted rAssociatedPermEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 1 ≤ r) :
    permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1 =
      permExcedanceCycleEGF (fun _ _ => True) x 1 *
        PowerSeries.subst
          (-(PowerSeries.X + ∑ j ∈ Finset.Icc 1 (r - 1),
            PowerSeries.C ((((j + 1).factorial : ℚ)⁻¹) •
              (x * ∑ σ : Equiv.Perm (Fin j), x ^ excedanceCount j σ)) *
              PowerSeries.X ^ (j + 1)))
          (PowerSeries.exp R)

/-- **Logarithm of the generating function of permutations with long cycles.** Let $R$ be a
commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 0$ an integer, and work with formal power
series in $u$ over $R$. For a permutation $\sigma$ write $e(\sigma)$ for its number of excedances
(points $i$ with $\sigma(i) > i$). Let
$C^{r+}(x,u) = \sum_{n \ge r+1} \sum_{\sigma} x^{e(\sigma)} u^n/n!$, the inner sum over the
permutations of $n$ points that consist of a single cycle, and let
$A^{r}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n!$, the inner sum over the
permutations of $n$ points all of whose cycles, fixed points included, have length greater than
$r$. Then $\exp C^{r+}(x,u) = A^{r}(x,u)$, that is, $C^{r+}(x,u) = \ln A^{r}(x,u)$.

At $r = 0$ every permutation has all cycle lengths greater than $0$, so $A^{0}(x,u)$ runs over
all permutations, $C^{0+}(x,u)$ over all circular permutations, and this is Theorem 6.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 33 (`jis-2025-25.5.7-cor-33`). -/
public theorem_wanted exp_circularRPlusPermEGF_eq_rAssociatedPermEGF {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (r : ℕ) :
    PowerSeries.subst
        (permExcedanceCycleEGF (fun n σ => (0 < n ∧ ∀ i j, σ.SameCycle i j) ∧ r + 1 ≤ n) x 1)
        (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1

/-- **Permutations with $k$ cycles, all of length greater than $r$, by excedances.** Let $R$ be a
commutative $\mathbb{Q}$-algebra, $x \in R$ and $r, k \in \mathbb{N}$. For a permutation
$\sigma$ of $\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with $\sigma(i) > i$ and
$c(\sigma)$ the number of cycles of $\sigma$, fixed points included. Let
$A^r(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles (fixed points
included, as cycles of length $1$) have length greater than $r$, and let $A^r_k(x,u)$ be the same
series with the inner sum further restricted to the $\sigma$ with $c(\sigma) = k$. If
$L \in R[[u]]$ has zero constant term and $\exp(L) = A^r(x,u)$, where
$\exp(F) = \sum_{m \ge 0} F^m/m!$, then $A^r_k(x,u) = L^k/k!$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 34 (`jis-2025-25.5.7-thm-34`). -/
public theorem_wanted rAssociatedPermEGF_cycleCount_eq {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (r k : ℕ) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1) :
    permExcedanceCycleEGF (fun n σ => IsRAssociatedCyclePerm r n σ ∧ cycleQuotientCount σ = k) x 1 =
      ((k.factorial : ℚ)⁻¹) • L ^ k

/-- **The $q$-analogue for cycles longer than $r$ is a $q$-th power.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$ and $r$ a natural number. For a permutation $\sigma$ of
$\{0, \dots, n-1\}$ let $\operatorname{exc}(\sigma)$ be the number of points $i$ with
$\sigma(i) > i$ and $\operatorname{cyc}(\sigma)$ its number of cycles (fixed points counted as
cycles of length one). Let
$$A^r(q,x,u) = \sum_{n \ge 0} \frac{u^n}{n!}
\sum_{\sigma} x^{\operatorname{exc}(\sigma)} q^{\operatorname{cyc}(\sigma)},$$
the inner sum over the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles have
length greater than $r$, and let $A^r(x,u) = A^r(1,x,u)$. If $L$ is a formal power series in
$u$ over $R$ with $L(0) = 0$ and $\exp L = A^r(x,u)$, then $A^r(q,x,u) = \exp(qL)$.

This is the paper's $A^r(q,x,u) = (A^r(x,u))^q$, with the power read through the logarithm $L$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 35 (`jis-2025-25.5.7-thm-35`). -/
public theorem_wanted rAssociatedPermEGF_q_eq_pow {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) (r : ℕ) (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1) :
    permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x q =
      PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- **Excedance generating function of involutions.** Let $R$ be a commutative
$\mathbb{Q}$-algebra and $x, q \in R$. For a permutation $\sigma$ write $e(\sigma)$ for the number
of $i$ with $\sigma(i) > i$ and $c(\sigma)$ for its number of cycles, fixed points included.
Summing over the involutions $\sigma$ of $\{0, \dots, n-1\}$ (permutations all of whose cycles
have length at most $2$), the following identity of formal power series in $u$ over $R$ holds:
$$\sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} \frac{u^n}{n!} = \exp(q(u + x u^2/2)).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 39 (`jis-2025-25.5.7-cor-39`). -/
public theorem_wanted involutionEGF_q_eq_exp {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) :
    permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm 2) x q =
      PowerSeries.subst
        (PowerSeries.C q * (PowerSeries.X + PowerSeries.C ((2 : ℚ)⁻¹ • x) * PowerSeries.X ^ 2))
        (PowerSeries.exp R)

/-- **Excedance generating function of fixed-point-free involutions.** Let $R$ be a commutative
$\mathbb{Q}$-algebra and $x, q \in R$. For a permutation $\sigma$ write $e(\sigma)$ for the number
of $i$ with $\sigma(i) > i$ and $c(\sigma)$ for its number of cycles, fixed points included.
Summing over the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles have length
exactly $2$, the following identity of formal power series in $u$ over $R$ holds:
$$\sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} \frac{u^n}{n!} = \exp(q x u^2/2).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 41 (`jis-2025-25.5.7-cor-41`). -/
public theorem_wanted fixedPointFreeInvolutionEGF_q_eq_exp {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) :
    permExcedanceCycleEGF (IsRCyclePerm 2) x q =
      PowerSeries.subst (PowerSeries.C ((2 : ℚ)⁻¹ • (q * x)) * PowerSeries.X ^ 2)
        (PowerSeries.exp R)

/-- **Excedance generating function of permutations with $k$ cycles.** Let $R$ be a commutative
$\mathbb{Q}$-algebra and $x \in R$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let
$e(\sigma)$ be the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$ the number of cycles of
$\sigma$, fixed points included. Let
$A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and for $k \ge 0$ let $A_k(x,u)$ be the
same series with the inner sum restricted to the $\sigma$ with $c(\sigma) = k$. If
$L \in R[[u]]$ has zero constant term and $\exp(L) = A(x,u)$, where
$\exp(F) = \sum_{m \ge 0} F^m/m!$, then $A_k(x,u) = L^k/k!$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 43 (`jis-2025-25.5.7-cor-43`). -/
public theorem_wanted permEGF_cycleCount_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (k : ℕ) (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    permExcedanceCycleEGF (fun _ σ => cycleQuotientCount σ = k) x 1 = ((k.factorial : ℚ)⁻¹) • L ^ k

/-- **Brenti's excedance and cycle generating function.** Let $R$ be a commutative
$\mathbb{Q}$-algebra and $x, q \in R$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let
$e(\sigma)$ be the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$ the number of cycles of
$\sigma$, fixed points included. Let
$A(q,x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} \in R[[u]]$,
the inner sum over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and $A(x,u) = A(1,x,u)$. If
$L \in R[[u]]$ has zero constant term and $\exp(L) = A(x,u)$, where
$\exp(F) = \sum_{m \ge 0} F^m/m!$, then $A(q,x,u) = \exp(qL)$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 44 (`jis-2025-25.5.7-cor-44`). -/
public theorem_wanted permEGF_q_eq_pow {R : Type*} [CommRing R] [Algebra ℚ R] (x q : R)
    (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    permExcedanceCycleEGF (fun _ _ => True) x q =
      PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-! ### First `s` points in distinct cycles (Theorems 17-38, 57-66, Corollaries 40-61)

The paper's bracket `[F]_s` is the generating function `F` restricted to permutations
whose first `s` points (`0, …, s-1` in `Fin n`) lie in distinct cycles, and
`∂^s [F]_s/∂u^s` is the `s`-th iterated `u`-derivative, written
`(PowerSeries.derivative (R := R))^[s]`. Logarithms and `q`-th powers are read as in the
section above. -/

/-- **First points in distinct cycles.** For natural numbers $s$ and $n$, a permutation $\sigma$
of $\{0, 1, \dots, n-1\}$ has its first $s$ points in distinct cycles when any two points
$i, j < s$ that lie in the same cycle of $\sigma$ are equal. When $n < s$, only the points below
$n$ are constrained.

This is the side condition of the paper's $(r^-,k,s)$-, $(r^+,\star,s)$-, $((r),k,s)$-cycle and
$s$-fixed-points permutations.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Section 1 (definitions of `(r^-,k,s)`-cycle and
`s`-fixed-points permutations). -/
public def FirstPointsInDistinctCycles (s n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, (i : ℕ) < s → (j : ℕ) < s → σ.SameCycle i j → i = j

public instance (s n : ℕ) : DecidablePred (FirstPointsInDistinctCycles s n) :=
  fun σ => by unfold FirstPointsInDistinctCycles; infer_instance

/-- **The first-points condition for $s = 0$.** For every $n \ge 0$ and every permutation
$\sigma$ of $\{0, \dots, n-1\}$, the first $0$ points of $\sigma$ lie in pairwise distinct
cycles: there are no such points, so the condition is vacuous.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Section 1. -/
public theorem firstPointsInDistinctCycles_zero (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    FirstPointsInDistinctCycles 0 n σ :=
  fun _ _ hi => absurd hi (Nat.not_lt_zero _)

/-- **The identity permutation separates its first points.** For all integers $s, n \ge 0$, the
first $s$ points of the identity permutation of $\{0, \dots, n-1\}$ lie in pairwise distinct
cycles: every point forms a cycle of its own.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Section 1. -/
public theorem firstPointsInDistinctCycles_one (s n : ℕ) : FirstPointsInDistinctCycles s n 1 :=
  fun _ _ _ _ h => Equiv.Perm.sameCycle_one.mp h

/-- **First points of the transposition $(0\,1)$.** Let $\tau = (0\,1)$ be the transposition of
$\{0, 1, 2\}$. The points $0, \dots, s-1$ lie in pairwise distinct cycles of $\tau$ for $s = 1$
(trivially, as there is only one such point) but not for $s = 2$, since $0$ and $1$ lie in the
same cycle of $\tau$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Section 1. -/
public theorem firstPointsInDistinctCycles_swap :
    FirstPointsInDistinctCycles 1 3 (Equiv.swap 0 1) ∧
      ¬ FirstPointsInDistinctCycles 2 3 (Equiv.swap 0 1) := by
  decide

/-- **Derivative formula for permutations with cycle lengths at most $r$ and separated first
points.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r, s$ be natural
numbers with $r \ge 1$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$ for
its number of excedances (indices $i$ with $\sigma(i) > i$), and let
$A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Say that the first $s$ points of $\sigma$ are
separated when the points $i < \min(s, n)$ lie in pairwise distinct cycles. Let
$A^{r-}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles, fixed points included, have
at most $r$ elements, and let $F(u)$ be the same series with the inner sum restricted to those
$\sigma$ whose first $s$ points are separated. Then the $s$-th derivative of $F$ with respect to
$u$ is
$$F^{(s)}(u) = \left(1 + x \sum_{i=1}^{r-1} \frac{A_i(x)\, u^i}{i!}\right)^s A^{r-}(x,u).$$

The paper states $r \ge 2$; the case $r = 1$ also holds (both sides are $\exp(u)$), while for
$r = 0$ and $s = 1$ the identity fails (the left side is $0$, the right side $1$).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 17 (`jis-2025-25.5.7-thm-17`). -/
public theorem_wanted rMinusAssociatedPermEGF_firstPoints_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (r s : ℕ) (hr : 1 ≤ r) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRMinusAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ)
          x 1) =
      (1 + ∑ i ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C (((i.factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin i), x ^ excedanceCount i σ)) * PowerSeries.X ^ i) ^ s *
        permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1

/-- **Derivative formula for permutations with cycle lengths at most $r$, $k$ cycles and
separated first points.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let
$r, s, k$ be natural numbers with $r \ge 1$ and $s \le k$. For a permutation $\sigma$ of
$\{0, \dots, n-1\}$ write $e(\sigma)$ for its number of excedances (indices $i$ with
$\sigma(i) > i$) and $c(\sigma)$ for its number of cycles, fixed points included, and let
$A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Say that the first $s$ points of $\sigma$ are
separated when the points $i < \min(s, n)$ lie in pairwise distinct cycles. Let
$A^{r-}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles, fixed points included, have
at most $r$ elements, and let $F(u)$ be the same series with the inner sum restricted to those
$\sigma$ with $c(\sigma) = k$ whose first $s$ points are separated. If $L \in R[[u]]$ has zero
constant term and $\exp(L) = A^{r-}(x,u)$, where $\exp$ of a series with zero constant term is
its substitution into the exponential series, then the $s$-th derivative of $F$ with respect to
$u$ is
$$F^{(s)}(u) = \Big(1 + x \sum_{i=1}^{r-1} \frac{A_i(x)\, u^i}{i!}\Big)^s \frac{L^{k-s}}{(k-s)!}.$$

The hypothesis $r \ge 1$ is needed: for $r = 0$ and $s = k = 1$ the left side is $0$ and the
right side is $1$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 18 (`jis-2025-25.5.7-thm-18`). -/
public theorem_wanted rMinusAssociatedPermEGF_firstPoints_cycleCount_iterate_derivative
    {R : Type*} [CommRing R] [Algebra ℚ R] (x : R) (r s k : ℕ) (hr : 1 ≤ r) (hk : s ≤ k)
    (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (IsRMinusAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) ∧
            cycleQuotientCount σ = k) x 1) =
      (1 + ∑ i ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C (((i.factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin i), x ^ excedanceCount i σ)) * PowerSeries.X ^ i) ^ s *
        ((((k - s).factorial : ℚ)⁻¹) • L ^ (k - s))

/-- **Cycle-weighted derivative formula for permutations with cycle lengths at most $r$ and
separated first points.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x, q \in R$, and let
$r, s$ be natural numbers with $r \ge 1$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$
write $e(\sigma)$ for its number of excedances (indices $i$ with $\sigma(i) > i$) and $c(\sigma)$
for its number of cycles, fixed points included, and let
$A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Say that the first $s$ points of $\sigma$ are
separated when the points $i < \min(s, n)$ lie in pairwise distinct cycles. Let
$A^{r-}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles, fixed points included, have
at most $r$ elements, and let
$F(u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n!$, the inner sum over the
permutations $\sigma$ of $\{0, \dots, n-1\}$ with all cycles of at most $r$ elements whose first
$s$ points are separated. If $L \in R[[u]]$ has zero constant term and $\exp(L) = A^{r-}(x,u)$,
where $\exp$ of a series with zero constant term is its substitution into the exponential
series, then the $s$-th derivative of $F$ with respect to $u$ is
$$F^{(s)}(u) = q^s \left(1 + x \sum_{i=1}^{r-1} \frac{A_i(x)\, u^i}{i!}\right)^s \exp(qL).$$

The hypothesis $r \ge 1$ is needed: for $r = 0$ and $s = 1$ the left side is $0$ and the right
side is $q$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 19 (`jis-2025-25.5.7-thm-19`). -/
public theorem_wanted rMinusAssociatedPermEGF_firstPoints_q_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x q : R) (r s : ℕ) (hr : 1 ≤ r) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRMinusAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ)
          x q) =
      PowerSeries.C (q ^ s) *
        (1 + ∑ i ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C (((i.factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin i), x ^ excedanceCount i σ)) * PowerSeries.X ^ i) ^ s *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- **Derivative formula for $r$-cycle permutations with separated first points.** Let $R$ be
a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r, s$ be natural numbers with $r \ge 2$.
For a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$ for its number of excedances
(indices $i$ with $\sigma(i) > i$), and let $A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Call
$\sigma$ an $r$-cycle permutation when every cycle of $\sigma$, fixed points included, has exactly
$r$ elements, and say that its first $s$ points are separated when the points $i < \min(s, n)$
lie in pairwise distinct cycles. Let
$A^{(r)}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the $r$-cycle permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F(u)$ be the same series
with the inner sum restricted to those $\sigma$ whose first $s$ points are separated. Then the
$s$-th derivative of $F$ with respect to $u$ is
$$F^{(s)}(u) = x^s \left(\frac{A_{r-1}(x)\, u^{r-1}}{(r-1)!}\right)^s A^{(r)}(x,u).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 27 (`jis-2025-25.5.7-thm-27`). -/
public theorem_wanted rCyclePermEGF_firstPoints_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (r s : ℕ) (hr : 2 ≤ r) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) x 1) =
      PowerSeries.C (x ^ s) *
        (PowerSeries.C ((((r - 1).factorial : ℚ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ) *
          PowerSeries.X ^ (r - 1)) ^ s *
        permExcedanceCycleEGF (IsRCyclePerm r) x 1

/-- **Derivative formula for $r$-cycle permutations with $k$ cycles and separated first points.**
Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r, s, k$ be natural numbers
with $r \ge 2$ and $s \le k$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$
for its number of excedances (indices $i$ with $\sigma(i) > i$) and $c(\sigma)$ for its number of
cycles, fixed points included, and let $A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Call
$\sigma$ an $r$-cycle permutation when every cycle of $\sigma$, fixed points included, has exactly
$r$ elements, and say that its first $s$ points are separated when the points $i < \min(s, n)$
lie in pairwise distinct cycles. Let
$A^{(r)}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the $r$-cycle permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F(u)$ be the same series
with the inner sum restricted to those $\sigma$ with $c(\sigma) = k$ whose first $s$ points are
separated. If $L \in R[[u]]$ has zero constant term and $\exp(L) = A^{(r)}(x,u)$, where $\exp$ of
a series with zero constant term is its substitution into the exponential series, then the
$s$-th derivative of $F$ with respect to $u$ is
$$F^{(s)}(u) = x^s \left(\frac{A_{r-1}(x)\, u^{r-1}}{(r-1)!}\right)^s \frac{L^{k-s}}{(k-s)!}.$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 28 (`jis-2025-25.5.7-thm-28`). -/
public theorem_wanted rCyclePermEGF_firstPoints_cycleCount_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (r s k : ℕ) (hr : 2 ≤ r) (hk : s ≤ k)
    (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) = permExcedanceCycleEGF (IsRCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (IsRCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) ∧
            cycleQuotientCount σ = k) x 1) =
      PowerSeries.C (x ^ s) *
        (PowerSeries.C ((((r - 1).factorial : ℚ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ) *
          PowerSeries.X ^ (r - 1)) ^ s *
        ((((k - s).factorial : ℚ)⁻¹) • L ^ (k - s))

/-- **Cycle-weighted derivative formula for $r$-cycle permutations with separated first points.**
Let $R$ be a commutative $\mathbb{Q}$-algebra, $x, q \in R$, and let $r, s$ be natural numbers
with $r \ge 2$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$ for its
number of excedances (indices $i$ with $\sigma(i) > i$) and $c(\sigma)$ for its number of cycles,
fixed points included, and let $A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Call $\sigma$ an
$r$-cycle permutation when every cycle of $\sigma$, fixed points included, has exactly $r$
elements, and say that its first $s$ points are separated when the points $i < \min(s, n)$ lie
in pairwise distinct cycles. Let
$A^{(r)}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the $r$-cycle permutations $\sigma$ of $\{0, \dots, n-1\}$, and let
$F(u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n!$, the inner sum over the
$r$-cycle permutations $\sigma$ of $\{0, \dots, n-1\}$ whose first $s$ points are separated. If
$L \in R[[u]]$ has zero constant term and $\exp(L) = A^{(r)}(x,u)$, where $\exp$ of a series
with zero constant term is its substitution into the exponential series, then the $s$-th
derivative of $F$ with respect to $u$ is
$$F^{(s)}(u) = q^s x^s \left(\frac{A_{r-1}(x)\, u^{r-1}}{(r-1)!}\right)^s \exp(qL).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 29 (`jis-2025-25.5.7-thm-29`). -/
public theorem_wanted rCyclePermEGF_firstPoints_q_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (r s : ℕ) (hr : 2 ≤ r) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) = permExcedanceCycleEGF (IsRCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) x q) =
      PowerSeries.C (q ^ s * x ^ s) *
        (PowerSeries.C ((((r - 1).factorial : ℚ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ) *
          PowerSeries.X ^ (r - 1)) ^ s *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- **Iterated derivative for cycles longer than $r$ with $s$ points in distinct cycles.** Let
$R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r$, $s$ be natural numbers with
$r \ge 1$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let $\operatorname{exc}(\sigma)$ be
the number of points $i$ with $\sigma(i) > i$, let
$A_n(x) = \sum_{\sigma} x^{\operatorname{exc}(\sigma)}$, summed over all permutations of
$\{0, \dots, n-1\}$, and let $A(x,u) = \sum_{n \ge 0} A_n(x) u^n/n!$. Let $A^r(x,u)$ be the
series $\sum_{n \ge 0} \sum_{\sigma} x^{\operatorname{exc}(\sigma)} u^n/n!$ with the inner sum
over the permutations of $\{0, \dots, n-1\}$ all of whose cycles (fixed points counted as
cycles of length one) have length greater than $r$, and let $[A^r(x,u)]_s$ be the same series
with the inner sum further restricted to the permutations whose points among
$0, \dots, s-1$ lie in pairwise distinct cycles. Then the $s$-th formal derivative in $u$
satisfies
$$\frac{\partial^s}{\partial u^s} [A^r(x,u)]_s =
x^s \left(A(x,u) - \sum_{n=0}^{r-1} \frac{A_n(x)\, u^n}{n!}\right)^s A^r(x,u).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 36 (`jis-2025-25.5.7-thm-36`). -/
public theorem_wanted rAssociatedPermEGF_firstPoints_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (r s : ℕ) (hr : 1 ≤ r) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) x 1) =
      PowerSeries.C (x ^ s) *
        (permExcedanceCycleEGF (fun _ _ => True) x 1 - ∑ n ∈ Finset.range r,
          PowerSeries.C (((n.factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin n), x ^ excedanceCount n σ) * PowerSeries.X ^ n) ^ s *
        permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1

/-- **Iterated derivative for $k$ cycles longer than $r$ with $s$ points in distinct cycles.**
Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r$, $s$, $k$ be natural
numbers with $r \ge 1$ and $s \le k$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let
$\operatorname{exc}(\sigma)$ be the number of points $i$ with $\sigma(i) > i$, let
$A_n(x) = \sum_{\sigma} x^{\operatorname{exc}(\sigma)}$, summed over all permutations of
$\{0, \dots, n-1\}$, and let $A(x,u) = \sum_{n \ge 0} A_n(x) u^n/n!$. Let $A^r(x,u)$ be the
series $\sum_{n \ge 0} \sum_{\sigma} x^{\operatorname{exc}(\sigma)} u^n/n!$ with the inner sum
over the permutations of $\{0, \dots, n-1\}$ all of whose cycles (fixed points counted as
cycles of length one) have length greater than $r$, and let $[A^r_k(x,u)]_s$ be the same
series with the inner sum further restricted to the permutations that have exactly $k$ cycles
and whose points among $0, \dots, s-1$ lie in pairwise distinct cycles. If $L$ is a formal
power series in $u$ over $R$ with $L(0) = 0$ and $\exp L = A^r(x,u)$, then the $s$-th formal
derivative in $u$ satisfies
$$\frac{\partial^s}{\partial u^s} [A^r_k(x,u)]_s =
x^s \left(A(x,u) - \sum_{n=0}^{r-1} \frac{A_n(x)\, u^n}{n!}\right)^s \frac{L^{k-s}}{(k-s)!}.$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 37 (`jis-2025-25.5.7-thm-37`). -/
public theorem_wanted rAssociatedPermEGF_firstPoints_cycleCount_iterate_derivative
    {R : Type*} [CommRing R] [Algebra ℚ R] (x : R) (r s k : ℕ) (hr : 1 ≤ r) (hk : s ≤ k)
    (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (IsRAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) ∧
            cycleQuotientCount σ = k) x 1) =
      PowerSeries.C (x ^ s) *
        (permExcedanceCycleEGF (fun _ _ => True) x 1 - ∑ n ∈ Finset.range r,
          PowerSeries.C (((n.factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin n), x ^ excedanceCount n σ) * PowerSeries.X ^ n) ^ s *
        ((((k - s).factorial : ℚ)⁻¹) • L ^ (k - s))

/-- **Iterated derivative of the $q$-analogue for cycles longer than $r$, $s$ points apart.**
Let $R$ be a commutative $\mathbb{Q}$-algebra, $x, q \in R$, and let $r$, $s$ be natural
numbers with $r \ge 1$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let
$\operatorname{exc}(\sigma)$ be the number of points $i$ with $\sigma(i) > i$ and
$\operatorname{cyc}(\sigma)$ its number of cycles (fixed points counted as cycles of length
one), let $A_n(x) = \sum_{\sigma} x^{\operatorname{exc}(\sigma)}$, summed over all permutations
of $\{0, \dots, n-1\}$, and let $A(x,u) = \sum_{n \ge 0} A_n(x) u^n/n!$. Let $A^r(x,u)$ be the
series $\sum_{n \ge 0} \sum_{\sigma} x^{\operatorname{exc}(\sigma)} u^n/n!$ with the inner sum
over the permutations of $\{0, \dots, n-1\}$ all of whose cycles have length greater than $r$,
and let $[A^r(q,x,u)]_s$ be the series
$\sum_{n \ge 0} \sum_{\sigma} x^{\operatorname{exc}(\sigma)} q^{\operatorname{cyc}(\sigma)} u^n/n!$
with the inner sum over the permutations of $\{0, \dots, n-1\}$ all of whose cycles have length
greater than $r$ and whose points among $0, \dots, s-1$ lie in pairwise distinct cycles. If $L$
is a formal power series in $u$ over $R$ with $L(0) = 0$ and $\exp L = A^r(x,u)$, then the
$s$-th formal derivative in $u$ satisfies
$$\frac{\partial^s}{\partial u^s} [A^r(q,x,u)]_s =
q^s x^s \left(A(x,u) - \sum_{n=0}^{r-1} \frac{A_n(x)\, u^n}{n!}\right)^s \exp(qL).$$

The factor $\exp(qL)$ is the paper's $(A^r(x,u))^q$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 38 (`jis-2025-25.5.7-thm-38`). -/
public theorem_wanted rAssociatedPermEGF_firstPoints_q_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x q : R) (r s : ℕ) (hr : 1 ≤ r) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) x q) =
      PowerSeries.C (q ^ s * x ^ s) *
        (permExcedanceCycleEGF (fun _ _ => True) x 1 - ∑ n ∈ Finset.range r,
          PowerSeries.C (((n.factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin n), x ^ excedanceCount n σ) * PowerSeries.X ^ n) ^ s *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- **Excedances and cycles of involutions.** Let $R$ be a commutative $\mathbb{Q}$-algebra,
$x, q \in R$ and $n \ge 0$. For a permutation $\sigma$ write $e(\sigma)$ for the number of $i$ with
$\sigma(i) > i$ and $c(\sigma)$ for its number of cycles, fixed points included. For each $m$ let
$W(m) = \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)}$, summed over the involutions $\sigma$ of
$\{0, \dots, m-1\}$ (permutations all of whose cycles have length at most $2$). Then
$$W(2n) = \sum_{k=0}^{n} \frac{(2n)!}{2^{n-k} (2k)! (n-k)!} q^{n+k} x^{n-k}$$
and
$$W(2n+1) = \sum_{k=0}^{n} \frac{(2n+1)!}{2^{n-k} (2k+1)! (n-k)!} q^{n+k+1} x^{n-k}.$$

The paper prints the summation index as $j$ while the summands use $k$; the sums are read over
$k$, as forced by Corollary 39: an involution of $2n$ (resp. $2n+1$) points with $n - k$
two-cycles has $2k$ (resp. $2k+1$) fixed points.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 40 (`jis-2025-25.5.7-cor-40`). -/
public theorem_wanted involution_excedance_cycle_sum {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) (n : ℕ) :
    (∑ σ ∈ Finset.univ.filter (IsRMinusAssociatedCyclePerm 2 (2 * n)),
        x ^ excedanceCount (2 * n) σ * q ^ cycleQuotientCount σ =
      ∑ k ∈ Finset.range (n + 1),
        (((2 * n).factorial : ℚ) / (2 ^ (n - k) * (2 * k).factorial * (n - k).factorial)) •
          (q ^ (n + k) * x ^ (n - k))) ∧
    ∑ σ ∈ Finset.univ.filter (IsRMinusAssociatedCyclePerm 2 (2 * n + 1)),
        x ^ excedanceCount (2 * n + 1) σ * q ^ cycleQuotientCount σ =
      ∑ k ∈ Finset.range (n + 1),
        (((2 * n + 1).factorial : ℚ) /
            (2 ^ (n - k) * (2 * k + 1).factorial * (n - k).factorial)) •
          (q ^ (n + k + 1) * x ^ (n - k))

/-- **Excedances and cycles of fixed-point-free involutions.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$ and $n \ge 0$. For a permutation $\sigma$ write $e(\sigma)$ for
the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$ for its number of cycles, fixed points
included. Summing over the permutations $\sigma$ of $\{0, \dots, 2n-1\}$ all of whose cycles have
length exactly $2$,
$$\sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} = \frac{(2n)!}{2^n\, n!}\, q^n x^n.$$

The paper prints the right-hand side as a sum over $j = 0, \dots, n$ of a summand free of $j$,
which is $n + 1$ times too large (for $n = 1$ the only such involution, $(0\,1)$, has weight
$q x$); the single term is the reading forced by Corollary 41, $\exp(q x u^2/2)$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 42 (`jis-2025-25.5.7-cor-42`). -/
public theorem_wanted fixedPointFreeInvolution_excedance_cycle_sum {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (n : ℕ) :
    ∑ σ ∈ Finset.univ.filter (IsRCyclePerm 2 (2 * n)),
        x ^ excedanceCount (2 * n) σ * q ^ cycleQuotientCount σ =
      (((2 * n).factorial : ℚ) / (2 ^ n * n.factorial)) • (q ^ n * x ^ n)

/-- **Derivative formula for permutations whose first $s$ points lie in distinct cycles.** Let
$R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$ and $s \in \mathbb{N}$. For a permutation
$\sigma$ of $\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with $\sigma(i) > i$. Let
$A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $A_{[s]}(x,u)$ be the same series
with the inner sum restricted to the $\sigma$ in which no two distinct points less than $s$ lie
in the same cycle. Then the $s$-th derivative in $u$ is
$$\frac{d^s}{du^s} A_{[s]}(x,u) = \bigl(A(x,u) \exp((x-1)u)\bigr)^s A(x,u),$$
where $\exp(F) = \sum_{m \ge 0} F^m/m!$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 45 (`jis-2025-25.5.7-cor-45`). -/
public theorem_wanted permEGF_firstPoints_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (s : ℕ) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF (FirstPointsInDistinctCycles s) x 1) =
      (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        permExcedanceCycleEGF (fun _ _ => True) x 1

/-- **Derivative formula for permutations with $k$ cycles whose first $s$ points lie in distinct
cycles.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$ and $s \le k$ natural numbers.
For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with
$\sigma(i) > i$ and $c(\sigma)$ the number of cycles of $\sigma$, fixed points included. Let
$A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $A_{[s],k}(x,u)$ be the same
series with the inner sum restricted to the $\sigma$ with $c(\sigma) = k$ in which no two
distinct points less than $s$ lie in the same cycle. If $L \in R[[u]]$ has zero constant term
and $\exp(L) = A(x,u)$, where $\exp(F) = \sum_{m \ge 0} F^m/m!$, then the $s$-th derivative in
$u$ is
$$\frac{d^s}{du^s} A_{[s],k}(x,u) =
\bigl(A(x,u) \exp((x-1)u)\bigr)^s \frac{L^{k-s}}{(k-s)!}.$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 46 (`jis-2025-25.5.7-cor-46`). -/
public theorem_wanted permEGF_firstPoints_cycleCount_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (s k : ℕ) (hk : s ≤ k) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => FirstPointsInDistinctCycles s n σ ∧ cycleQuotientCount σ = k) x 1) =
      (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        ((((k - s).factorial : ℚ)⁻¹) • L ^ (k - s))

/-- **$q$-analogue of the derivative formula for permutations whose first $s$ points lie in
distinct cycles.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x, q \in R$ and
$s \in \mathbb{N}$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let $e(\sigma)$ be the
number of $i$ with $\sigma(i) > i$ and $c(\sigma)$ the number of cycles of $\sigma$, fixed points
included. Let $A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$,
the inner sum over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let
$A_{[s]}(q,x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)}$, the
inner sum over the permutations $\sigma$ of $\{0, \dots, n-1\}$ in which no two distinct points
less than $s$ lie in the same cycle. If $L \in R[[u]]$ has zero constant term and
$\exp(L) = A(x,u)$, where $\exp(F) = \sum_{m \ge 0} F^m/m!$, then the $s$-th derivative in $u$ is
$$\frac{d^s}{du^s} A_{[s]}(q,x,u) = q^s \bigl(A(x,u) \exp((x-1)u)\bigr)^s \exp(qL).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 47 (`jis-2025-25.5.7-cor-47`). -/
public theorem_wanted permEGF_firstPoints_q_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (s : ℕ) (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF (FirstPointsInDistinctCycles s) x q) =
      PowerSeries.C (q ^ s) *
        (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- **Signed excedance sum with weight $-s$ over permutations with separated first points.** Let
$R$ be a commutative ring, $x \in R$ and $n, s \ge 0$ integers. For a permutation $\sigma$ write
$e(\sigma)$ for its number of excedances (points $i$ with $\sigma(i) > i$) and $c(\sigma)$ for
its number of cycles, fixed points included. Summing over the permutations $\sigma$ of
$\{0, \dots, n+s-1\}$ in which the points $0, \dots, s-1$ lie in pairwise distinct cycles,
$\sum_{\sigma} x^{e(\sigma)} (-s)^{c(\sigma)} = (-1)^s s^{n+s} (x-1)^n$, with $0^0 = 1$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 48 (`jis-2025-25.5.7-cor-48`). -/
public theorem_wanted firstPoints_excedance_cycle_sum_neg {R : Type*} [CommRing R] (x : R)
    (n s : ℕ) :
    ∑ σ ∈ Finset.univ.filter (FirstPointsInDistinctCycles s (n + s)),
        x ^ excedanceCount (n + s) σ * (-(s : R)) ^ cycleQuotientCount σ =
      (-1) ^ s * (s : R) ^ (n + s) * (x - 1) ^ n

/-- **Signed excedance sum with weight $-(s+1)$ over permutations with separated first points.**
Let $R$ be a commutative ring, $x \in R$ and $n \ge 1$, $s \ge 0$ integers. For a permutation
$\sigma$ write $e(\sigma)$ for its number of excedances (points $i$ with $\sigma(i) > i$) and
$c(\sigma)$ for its number of cycles, fixed points included. Summing over the permutations
$\sigma$ of $\{0, \dots, n+s-1\}$ in which the points $0, \dots, s-1$ lie in pairwise distinct
cycles,
$\sum_{\sigma} x^{e(\sigma)} (-(s+1))^{c(\sigma)} = (-1)^s (s+1)^s (x s^n - (s+1)^n) (x-1)^{n-1}$.

The hypothesis $n \ge 1$ makes $(x-1)^{n-1}$ a polynomial.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 49 (`jis-2025-25.5.7-cor-49`). -/
public theorem_wanted firstPoints_excedance_cycle_sum_neg_succ {R : Type*} [CommRing R]
    (x : R) (n s : ℕ) (hn : 1 ≤ n) :
    ∑ σ ∈ Finset.univ.filter (FirstPointsInDistinctCycles s (n + s)),
        x ^ excedanceCount (n + s) σ * (-((s : R) + 1)) ^ cycleQuotientCount σ =
      (-1) ^ s * ((s : R) + 1) ^ s * (x * (s : R) ^ n - ((s : R) + 1) ^ n) * (x - 1) ^ (n - 1)

/-- **Derangements whose first $s$ points lie in distinct cycles.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$ and $s \ge 0$. For a permutation $\sigma$ let $e(\sigma)$ be
its number of excedances (indices $i$ with $\sigma(i) > i$) and $c(\sigma)$ its number of
cycles, fixed points included. Let $A(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n!$,
summed over all permutations $\sigma$ of $n$ objects, and let $L \in R[[u]]$ have constant term
$0$ and satisfy $\exp L = A(x,u)$. Let
$D_s(q,x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n!$, the inner sum
over the derangements $\sigma$ of $n$ objects (permutations without fixed points) in which the
first $s$ points (all points, if $n < s$) lie in pairwise distinct cycles. Then the $s$-th
derivative of $D_s$ with respect to $u$ equals $q^s x^s (A(x,u) - 1)^s \exp\big(q\,(L - u)\big)$,
which is the paper's $q^s x^s (A(x,u) - 1)^s (A(x,u) e^{-u})^q$ with the power read through $L$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 51 (`jis-2025-25.5.7-cor-51`). -/
public theorem_wanted derangementEGF_firstPoints_q_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x q : R) (s : ℕ) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRAssociatedCyclePerm 1 n σ ∧ FirstPointsInDistinctCycles s n σ) x q) =
      PowerSeries.C (q ^ s * x ^ s) * (permExcedanceCycleEGF (fun _ _ => True) x 1 - 1) ^ s *
        PowerSeries.subst (PowerSeries.C q * (L - PowerSeries.X)) (PowerSeries.exp R)

/-- **Derangements with the first $s$ points in distinct cycles, cycle weight $-s$.** Let
$n, s \ge 0$. For a permutation $\sigma$ let $e(\sigma)$ be its number of excedances (indices
$i$ with $\sigma(i) > i$) and $c(\sigma)$ its number of cycles, fixed points included. Summing
over the derangements $\sigma$ of $n + s$ objects (permutations without fixed points) in which
the first $s$ points lie in pairwise distinct cycles, the identity
$(x - 1)^s \sum_{\sigma} x^{e(\sigma)} (-s)^{c(\sigma)} = (-1)^s (s x)^s
\sum_{i} \binom{n}{i_1, \dots, i_s} \prod_{j=1}^{s} (x^{i_j} - 1)$
holds in $\mathbb{Z}[x]$, where $i = (i_1, \dots, i_s)$ runs over the $s$-tuples of positive
integers with $i_1 + \dots + i_s = n$ and $\binom{n}{i_1, \dots, i_s}$ is the multinomial
coefficient. This is the paper's formula
$\sum_{\sigma} x^{e(\sigma)} (-s)^{c(\sigma)} = (-1)^s (s x/(x-1))^s \sum_{i}
\binom{n}{i_1, \dots, i_s} \prod_{j} (x^{i_j} - 1)$ with the denominator cleared.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 52 (`jis-2025-25.5.7-cor-52`). -/
public theorem_wanted derangement_firstPoints_excedance_cycle_sum_neg (n s : ℕ) :
    (X - 1 : ℤ[X]) ^ s *
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + s)) =>
            IsRAssociatedCyclePerm 1 (n + s) σ ∧ FirstPointsInDistinctCycles s (n + s) σ),
          X ^ excedanceCount (n + s) σ * (-(s : ℤ[X])) ^ cycleQuotientCount σ =
      (-1) ^ s * ((s : ℤ[X]) * X) ^ s *
        ∑ i ∈ (Finset.Nat.antidiagonalTuple s n).filter (fun i => ∀ j, 1 ≤ i j),
          (Nat.multinomial Finset.univ i : ℤ[X]) * ∏ j, (X ^ i j - 1)

/-- **Derangements with the first $s$ points in distinct cycles, cycle weight $-(s+1)$.** Let
$n, s \ge 0$. For a permutation $\sigma$ let $e(\sigma)$ be its number of excedances (indices
$i$ with $\sigma(i) > i$) and $c(\sigma)$ its number of cycles, fixed points included. Summing
over the derangements $\sigma$ of $n + s$ objects (permutations without fixed points) in which
the first $s$ points lie in pairwise distinct cycles, the identity
$(x - 1)^{s+1} \sum_{\sigma} x^{e(\sigma)} (-s-1)^{c(\sigma)} = (-1)^s (s+1)^s x^s
\sum_{\ell=0}^{n} \binom{n}{\ell} (x - x^\ell) \sum_{i} \binom{n-\ell}{i_1, \dots, i_s}
\prod_{j=1}^{s} (x^{i_j} - 1)$
holds in $\mathbb{Z}[x]$, where for each $\ell$ the tuple $i = (i_1, \dots, i_s)$ runs over the
$s$-tuples of positive integers with $i_1 + \dots + i_s = n - \ell$, and
$\binom{n-\ell}{i_1, \dots, i_s}$ is the multinomial coefficient. This is the corrected form of
the paper's formula, with the denominator $(x-1)^{s+1}$ cleared.

The printed Corollary 54 omits the binomial coefficient $\binom{n}{\ell}$ and is false as
printed: for $s = 1$, $n = 3$ and $x = 2$ the left side is $-4$ and the printed right side is
$-20$. The binomial comes from the paper's own proof, which extracts the coefficient of
$u^n/n!$ from the product of the exponential generating functions
$(\sum_{n \ge 1} (x^n - 1) u^n/n!)^s$ and $\sum_{n \ge 0} (x - x^n)/(x-1)\,u^n/n!$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 54 (`jis-2025-25.5.7-cor-54`). -/
public theorem_wanted derangement_firstPoints_excedance_cycle_sum_neg_succ (n s : ℕ) :
    (X - 1 : ℤ[X]) ^ (s + 1) *
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + s)) =>
            IsRAssociatedCyclePerm 1 (n + s) σ ∧ FirstPointsInDistinctCycles s (n + s) σ),
          X ^ excedanceCount (n + s) σ * (-((s : ℤ[X]) + 1)) ^ cycleQuotientCount σ =
      (-1) ^ s * ((s : ℤ[X]) + 1) ^ s * X ^ s *
        ∑ l ∈ Finset.range (n + 1), (n.choose l : ℤ[X]) * (X - X ^ l) *
          ∑ i ∈ (Finset.Nat.antidiagonalTuple s (n - l)).filter (fun i => ∀ j, 1 ≤ i j),
            (Nat.multinomial Finset.univ i : ℤ[X]) * ∏ j, (X ^ i j - 1)

/-- **Excedance generating function of s-fixed-points permutations.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x \in R$ and $s$ a natural number. Call a permutation $\sigma$ of
$\{0, \dots, n-1\}$ an $s$-fixed-points permutation if every fixed point of $\sigma$ is less than
$s$ and any two points less than $s$ in the same cycle of $\sigma$ are equal. Write $e(\sigma)$
for the number of $i$ with $\sigma(i) > i$, let $A(x,u) = \sum_{n \ge 0} \sum_{\sigma}
x^{e(\sigma)} u^n/n!$ over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F(x,u)$ be
the same series restricted to the $s$-fixed-points permutations. Then, as formal power series in
$u$ over $R$,
$$\frac{d^s}{du^s} F(x,u) = \left(A(x,u) \exp((x-1)u)\right)^s A(x,u) \exp(-u).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 57 (`jis-2025-25.5.7-thm-57`). -/
public theorem_wanted fixedPointsPermEGF_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (s : ℕ) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (∀ i : Fin n, σ i = i → (i : ℕ) < s) ∧ FirstPointsInDistinctCycles s n σ)
          x 1) =
      (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        permExcedanceCycleEGF (fun _ _ => True) x 1 *
        PowerSeries.subst (-PowerSeries.X) (PowerSeries.exp R)

/-- **Excedance generating function of s-fixed-points permutations with k cycles.** Let $R$ be a
commutative $\mathbb{Q}$-algebra, $x \in R$, and $s \le k$ natural numbers. Call a permutation
$\sigma$ of $\{0, \dots, n-1\}$ an $s$-fixed-points permutation if every fixed point of $\sigma$
is less than $s$ and any two points less than $s$ in the same cycle of $\sigma$ are equal. Write
$e(\sigma)$ for the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$ for the number of cycles
of $\sigma$, fixed points included. Let $A(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)}
u^n/n!$ over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F_k(x,u)$ be the same
series restricted to the $s$-fixed-points permutations with $c(\sigma) = k$. Then for every
formal power series $L$ in $u$ over $R$ with zero constant term and $\exp(L) = A(x,u)$,
$$\frac{d^s}{du^s} F_k(x,u) = \left(A(x,u) \exp((x-1)u)\right)^s \frac{(L - u)^{k-s}}{(k-s)!}.$$

Here $L - u$ is the paper's $\ln(A(x,u) \exp(-u))$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 58 (`jis-2025-25.5.7-thm-58`). -/
public theorem_wanted fixedPointsPermEGF_cycleCount_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (s k : ℕ) (hk : s ≤ k) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => ((∀ i : Fin n, σ i = i → (i : ℕ) < s) ∧
            FirstPointsInDistinctCycles s n σ) ∧ cycleQuotientCount σ = k) x 1) =
      (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        ((((k - s).factorial : ℚ)⁻¹) • (L - PowerSeries.X) ^ (k - s))

/-- **Cycle-counting excedance generating function of s-fixed-points permutations.** Let $R$ be a
commutative $\mathbb{Q}$-algebra, $x, q \in R$ and $s$ a natural number. Call a permutation
$\sigma$ of $\{0, \dots, n-1\}$ an $s$-fixed-points permutation if every fixed point of $\sigma$
is less than $s$ and any two points less than $s$ in the same cycle of $\sigma$ are equal. Write
$e(\sigma)$ for the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$ for the number of cycles
of $\sigma$, fixed points included. Let $A(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)}
u^n/n!$ over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let
$F(q,x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n!$ over the
$s$-fixed-points permutations $\sigma$ of $\{0, \dots, n-1\}$. Then for every formal power series
$L$ in $u$ over $R$ with zero constant term and $\exp(L) = A(x,u)$,
$$\frac{d^s}{du^s} F(q,x,u) = q^s \left(A(x,u) \exp((x-1)u)\right)^s \exp(qL) \exp(-qu).$$

Here $\exp(qL)$ is the paper's $(A(x,u))^q$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 59 (`jis-2025-25.5.7-thm-59`). -/
public theorem_wanted fixedPointsPermEGF_q_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (s : ℕ) (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (∀ i : Fin n, σ i = i → (i : ℕ) < s) ∧ FirstPointsInDistinctCycles s n σ)
          x q) =
      PowerSeries.C (q ^ s) *
        (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R) *
        PowerSeries.subst (-(PowerSeries.C q * PowerSeries.X)) (PowerSeries.exp R)

/-- **Signed excedance–cycle sum over s-fixed-points permutations, cycle weight -s.** Let $R$ be a
commutative ring, $x \in R$, and $s \le n$ natural numbers. Call a permutation $\sigma$ of
$\{0, \dots, n-1\}$ an $s$-fixed-points permutation if every fixed point of $\sigma$ is less than
$s$ and any two points less than $s$ in the same cycle of $\sigma$ are equal. Write $e(\sigma)$
for the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$ for the number of cycles of $\sigma$,
fixed points included. Then, summing over the $s$-fixed-points permutations of
$\{0, \dots, n-1\}$,
$$\sum_{\sigma} x^{e(\sigma)} (-s)^{c(\sigma)} = (-1)^s s^n x^{n-s}.$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 60 (`jis-2025-25.5.7-cor-60`). -/
public theorem_wanted fixedPointsPerm_excedance_cycle_sum_neg {R : Type*} [CommRing R] (x : R)
    (n s : ℕ) (hn : s ≤ n) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (∀ i : Fin n, σ i = i → (i : ℕ) < s) ∧ FirstPointsInDistinctCycles s n σ),
        x ^ excedanceCount n σ * (-(s : R)) ^ cycleQuotientCount σ =
      (-1) ^ s * (s : R) ^ n * x ^ (n - s)

/-- **Signed excedance–cycle sum over s-fixed-points permutations, cycle weight -s-1.** Let
$s \le n$ be natural numbers. Call a permutation $\sigma$ of $\{0, \dots, n-1\}$ an
$s$-fixed-points permutation if every fixed point of $\sigma$ is less than $s$ and any two points
less than $s$ in the same cycle of $\sigma$ are equal. Write $e(\sigma)$ for the number of $i$
with $\sigma(i) > i$ and $c(\sigma)$ for the number of cycles of $\sigma$, fixed points included.
Then, summing over the $s$-fixed-points permutations $\sigma$ of $\{0, \dots, n-1\}$, the sum
$S = \sum_{\sigma} x^{e(\sigma)} (-s-1)^{c(\sigma)}$ in the polynomial ring $\mathbb{Z}[x]$
satisfies
$$(x - 1) S = (-1)^s (s+1)^s \left(x (s x + 1)^{n-s} - (s+1)^{n-s} x^{n-s}\right).$$

This is the paper's formula with the denominator $x - 1$ cleared.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 61 (`jis-2025-25.5.7-cor-61`). -/
public theorem_wanted fixedPointsPerm_excedance_cycle_sum_neg_succ (n s : ℕ) (hn : s ≤ n) :
    (X - 1 : ℤ[X]) *
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            (∀ i : Fin n, σ i = i → (i : ℕ) < s) ∧ FirstPointsInDistinctCycles s n σ),
          X ^ excedanceCount n σ * (-((s : ℤ[X]) + 1)) ^ cycleQuotientCount σ =
      (-1) ^ s * ((s : ℤ[X]) + 1) ^ s *
        (X * ((s : ℤ[X]) * X + 1) ^ (n - s) - ((s : ℤ[X]) + 1) ^ (n - s) * X ^ (n - s))

/-- **Derivative formula for prescribed cycle lengths through the first $s$ points.** Let $R$ be
a commutative $\mathbb{Q}$-algebra, $x \in R$, $s \in \mathbb{N}$ and
$r : \mathbb{N} \to \mathbb{N}$ with $r(i) \ge 2$ for all $i < s$. For a permutation $\sigma$ of
$\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with $\sigma(i) > i$, and for $m \ge 0$
let $A_m(x) = \sum_{\sigma} x^{e(\sigma)}$ over all permutations $\sigma$ of
$\{0, \dots, m-1\}$. Let
$A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F(x,u)$ be the same series with
the inner sum restricted to the $\sigma$ in which no two distinct points less than $s$ lie in
the same cycle and each point $i < s$ lies in a cycle of length $r(i)$. Then the $s$-th
derivative in $u$ is
$$\frac{d^s}{du^s} F(x,u) = x^s \Bigl(\prod_{i=0}^{s-1}
\frac{A_{r(i)-1}(x)\, u^{r(i)-1}}{(r(i)-1)!}\Bigr) A(x,u).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 62 (`jis-2025-25.5.7-thm-62`). -/
public theorem_wanted prescribedCyclePermEGF_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (s : ℕ) (r : ℕ → ℕ) (hr : ∀ i < s, 2 ≤ r i) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => FirstPointsInDistinctCycles s n σ ∧ ∀ i : Fin n, (i : ℕ) < s →
            (Finset.univ.filter (σ.SameCycle i)).card = r i) x 1) =
      PowerSeries.C (x ^ s) *
        (∏ i ∈ Finset.range s,
          PowerSeries.C ((((r i - 1).factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin (r i - 1)), x ^ excedanceCount (r i - 1) σ) *
            PowerSeries.X ^ (r i - 1)) *
        permExcedanceCycleEGF (fun _ _ => True) x 1

/-- **Derivative formula for prescribed cycle lengths through the first $s$ points, with $k$
cycles.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, $s \le k$ natural numbers
and $r : \mathbb{N} \to \mathbb{N}$ with $r(i) \ge 2$ for all $i < s$. For a permutation $\sigma$
of $\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$
the number of cycles of $\sigma$, fixed points included, and for $m \ge 0$ let
$A_m(x) = \sum_{\sigma} x^{e(\sigma)}$ over all permutations $\sigma$ of $\{0, \dots, m-1\}$. Let
$A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F_k(x,u)$ be the same series with
the inner sum restricted to the $\sigma$ with $c(\sigma) = k$ in which no two distinct points
less than $s$ lie in the same cycle and each point $i < s$ lies in a cycle of length $r(i)$. If
$L \in R[[u]]$ has zero constant term and $\exp(L) = A(x,u)$, where
$\exp(G) = \sum_{m \ge 0} G^m/m!$, then the $s$-th derivative in $u$ is
$$\frac{d^s}{du^s} F_k(x,u) = x^s \Bigl(\prod_{i=0}^{s-1}
\frac{A_{r(i)-1}(x)\, u^{r(i)-1}}{(r(i)-1)!}\Bigr) \frac{L^{k-s}}{(k-s)!}.$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 63 (`jis-2025-25.5.7-thm-63`). -/
public theorem_wanted prescribedCyclePermEGF_cycleCount_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (s k : ℕ) (r : ℕ → ℕ) (hr : ∀ i < s, 2 ≤ r i)
    (hk : s ≤ k) (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (FirstPointsInDistinctCycles s n σ ∧ ∀ i : Fin n, (i : ℕ) < s →
            (Finset.univ.filter (σ.SameCycle i)).card = r i) ∧ cycleQuotientCount σ = k)
          x 1) =
      PowerSeries.C (x ^ s) *
        (∏ i ∈ Finset.range s,
          PowerSeries.C ((((r i - 1).factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin (r i - 1)), x ^ excedanceCount (r i - 1) σ) *
            PowerSeries.X ^ (r i - 1)) *
        ((((k - s).factorial : ℚ)⁻¹) • L ^ (k - s))

/-- **$q$-analogue of the derivative formula for prescribed cycle lengths through the first $s$
points.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x, q \in R$, $s \in \mathbb{N}$ and
$r : \mathbb{N} \to \mathbb{N}$ with $r(i) \ge 2$ for all $i < s$. For a permutation $\sigma$ of
$\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$ the
number of cycles of $\sigma$, fixed points included, and for $m \ge 0$ let
$A_m(x) = \sum_{\sigma} x^{e(\sigma)}$ over all permutations $\sigma$ of $\{0, \dots, m-1\}$. Let
$A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let
$F(q,x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)}$, the inner
sum over the permutations $\sigma$ of $\{0, \dots, n-1\}$ in which no two distinct points less
than $s$ lie in the same cycle and each point $i < s$ lies in a cycle of length $r(i)$. If
$L \in R[[u]]$ has zero constant term and $\exp(L) = A(x,u)$, where
$\exp(G) = \sum_{m \ge 0} G^m/m!$, then the $s$-th derivative in $u$ is
$$\frac{d^s}{du^s} F(q,x,u) = q^s x^s \Bigl(\prod_{i=0}^{s-1}
\frac{A_{r(i)-1}(x)\, u^{r(i)-1}}{(r(i)-1)!}\Bigr) \exp(qL).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 64 (`jis-2025-25.5.7-thm-64`). -/
public theorem_wanted prescribedCyclePermEGF_q_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (s : ℕ) (r : ℕ → ℕ) (hr : ∀ i < s, 2 ≤ r i) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => FirstPointsInDistinctCycles s n σ ∧ ∀ i : Fin n, (i : ℕ) < s →
            (Finset.univ.filter (σ.SameCycle i)).card = r i) x q) =
      PowerSeries.C (q ^ s * x ^ s) *
        (∏ i ∈ Finset.range s,
          PowerSeries.C ((((r i - 1).factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin (r i - 1)), x ^ excedanceCount (r i - 1) σ) *
            PowerSeries.X ^ (r i - 1)) *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- **Permutations with all cycle lengths in a prescribed set.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$, and let $\mathcal{R}$ be a finite set of integers, each at
least $2$. For a permutation $\sigma$ let $e(\sigma)$ be its number of excedances (indices $i$
with $\sigma(i) > i$) and $c(\sigma)$ its number of cycles, fixed points included, and for
$j \ge 0$ let $A_j(x) = \sum_{\sigma} x^{e(\sigma)}$, summed over all permutations $\sigma$ of
$j$ objects. Then in $R[[u]]$
$\sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n! =
\exp\big(q x \sum_{r \in \mathcal{R}} A_{r-1}(x)\,u^r/r!\big)$, where the inner sum on the left
runs over the permutations $\sigma$ of $n$ objects all of whose cycles, fixed points included,
have length in $\mathcal{R}$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 65 (`jis-2025-25.5.7-thm-65`). -/
public theorem_wanted cycleLengthsInEGF_q_eq_exp {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) (ℛ : Finset ℕ) (hℛ : ∀ r ∈ ℛ, 2 ≤ r) :
    permExcedanceCycleEGF
        (fun n σ => ∀ i : Fin n, (Finset.univ.filter (σ.SameCycle i)).card ∈ ℛ) x q =
      PowerSeries.subst
        (PowerSeries.C q * ∑ r ∈ ℛ,
          PowerSeries.C (((r.factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
            PowerSeries.X ^ r)
        (PowerSeries.exp R)

/-- **$q$-analogue of the derivative formula for prescribed cycle lengths through the first $s$
points, other cycle lengths in a set $\mathcal{R}$.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$, $s \in \mathbb{N}$, $r : \mathbb{N} \to \mathbb{N}$ with
$r(i) \ge 2$ for all $i < s$, and $\mathcal{R}$ a finite set of natural numbers, each at least
$2$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with
$\sigma(i) > i$ and $c(\sigma)$ the number of cycles of $\sigma$, fixed points included, and for
$m \ge 0$ let $A_m(x) = \sum_{\sigma} x^{e(\sigma)}$ over all permutations $\sigma$ of
$\{0, \dots, m-1\}$. Let $B(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)}$,
the inner sum over the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles (fixed
points included) have length in $\mathcal{R}$. Let
$F(q,x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)}$, the inner
sum over the permutations $\sigma$ of $\{0, \dots, n-1\}$ in which no two distinct points less
than $s$ lie in the same cycle, each point $i < s$ lies in a cycle of length $r(i)$, and every
cycle containing no point less than $s$ has length in $\mathcal{R}$. If $L \in R[[u]]$ has zero
constant term and $\exp(L) = B(x,u)$, where $\exp(G) = \sum_{m \ge 0} G^m/m!$, then the $s$-th
derivative in $u$ is
$$\frac{d^s}{du^s} F(q,x,u) = q^s x^s \Bigl(\prod_{i=0}^{s-1}
\frac{A_{r(i)-1}(x)\, u^{r(i)-1}}{(r(i)-1)!}\Bigr) \exp(qL).$$

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 66 (`jis-2025-25.5.7-thm-66`). -/
public theorem_wanted prescribedCycleLengthsInEGF_q_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x q : R) (s : ℕ) (r : ℕ → ℕ) (hr : ∀ i < s, 2 ≤ r i)
    (ℛ : Finset ℕ) (hℛ : ∀ m ∈ ℛ, 2 ≤ m) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF
        (fun n σ => ∀ i : Fin n, (Finset.univ.filter (σ.SameCycle i)).card ∈ ℛ) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (FirstPointsInDistinctCycles s n σ ∧ ∀ i : Fin n, (i : ℕ) < s →
            (Finset.univ.filter (σ.SameCycle i)).card = r i) ∧
            ∀ i : Fin n, (∀ j : Fin n, (j : ℕ) < s → ¬ σ.SameCycle i j) →
              (Finset.univ.filter (σ.SameCycle i)).card ∈ ℛ) x q) =
      PowerSeries.C (q ^ s * x ^ s) *
        (∏ i ∈ Finset.range s,
          PowerSeries.C ((((r i - 1).factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin (r i - 1)), x ^ excedanceCount (r i - 1) σ) *
            PowerSeries.X ^ (r i - 1)) *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- **Permutations avoiding a prescribed set of cycle lengths.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$, and let $\mathcal{R}$ be a finite set of integers, each at
least $2$. For a permutation $\sigma$ let $e(\sigma)$ be its number of excedances (indices $i$
with $\sigma(i) > i$) and $c(\sigma)$ its number of cycles, fixed points included; for
$j \ge 0$ let $A_j(x) = \sum_{\sigma} x^{e(\sigma)}$, summed over all permutations $\sigma$ of
$j$ objects; and let $A(q,x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n!$,
summed over all permutations $\sigma$ of $n$ objects. Then in $R[[u]]$
$\sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n! =
A(q,x,u) \exp\big(-q x \sum_{r \in \mathcal{R}} A_{r-1}(x)\,u^r/r!\big)$, where the inner sum on
the left runs over the permutations $\sigma$ of $n$ objects none of whose cycles has length in
$\mathcal{R}$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 67 (`jis-2025-25.5.7-cor-67`). -/
public theorem_wanted cycleLengthsNotInEGF_q_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) (ℛ : Finset ℕ) (hℛ : ∀ r ∈ ℛ, 2 ≤ r) :
    permExcedanceCycleEGF
        (fun n σ => ∀ i : Fin n, (Finset.univ.filter (σ.SameCycle i)).card ∉ ℛ) x q =
      permExcedanceCycleEGF (fun _ _ => True) x q *
        PowerSeries.subst
          (-(PowerSeries.C q * ∑ r ∈ ℛ,
            PowerSeries.C (((r.factorial : ℚ)⁻¹) •
              (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
              PowerSeries.X ^ r))
          (PowerSeries.exp R)

end

end MetaMathlibExt
