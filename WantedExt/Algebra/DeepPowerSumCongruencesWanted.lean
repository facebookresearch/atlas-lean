/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.Algebra.DeepPowerSumCongruences
public import MathlibExt.Algebra.DeepPowerSumCongruences.DividedPowerIdeal
public import MathlibExt.Algebra.DeepPowerSumCongruences.DividedPowerSpan
public import MathlibExt.Algebra.DeepPowerSumCongruences.DVRMaximalIdeal
public import MathlibExt.Algebra.DeepPowerSumCongruences.DVRMaximalIdealPow
public import MathlibExt.Algebra.DeepPowerSumCongruences.Moebius
public import MathlibExt.Algebra.DeepPowerSumCongruences.PadicInt
public import MathlibExt.Algebra.DeepPowerSumCongruences.PEquivClass
public import MathlibExt.Algebra.DeepPowerSumCongruences.PartitionProduct
public import MathlibExt.Algebra.DeepPowerSumCongruences.PowerSumExp

/-!
# Elementary symmetric functions and deep power-sum congruences

Statements from Samuele Anni, Alexandru Ghitza and Anna Medvedovsky, *Elementary Symmetric
Functions and Deep Power-Sum Congruences*, INTEGERS 24 (2024), Article A46 (arXiv `2207.07108`,
TeX source read).

Conventions. A torsion-free `ℤ_(p)`-algebra `A` is a commutative ring with `IsAddTorsionFree A` in
which every natural number prime to `p` is a unit. An ideal `𝔞` is a *divided-power ideal* when
`a ^ k / k! ∈ 𝔞` for every `a ∈ 𝔞` and `k ≥ 1`; stated division-free as `IsDividedPowerIdeal`.
"`x ≡ y mod n𝔞`" is `∃ c ∈ 𝔞, x - y = n * c`. For a monic `P ∈ A[X]`, `polyElemSymm P n` is the
paper's `e_n(P)` and `polyPowerSum P n` its `p_n(P)`, defined through Newton's identities with
`p_0(P) = deg P`, as in the paper's Notation of Section 3.2. Symmetric functions are taken in
finitely many variables (`MvPolynomial σ ℚ`, `σ` finite), which loses nothing for identities
between them.

Proposition 3, `pow_mem_prime_pow_padicValNat_factorial_iff`, Kummer's theorem for multinomial
coefficients, `padicValNat_multinomial_eq_sum_carries`, and Corollary 24,
`padicValNat_sum_le_add_padicValNat_multinomial`, are proved in
`MathlibExt.Algebra.DeepPowerSumCongruences`.

The $p$-splitting relation `IsPSplitting`, the $p$-equivalence classes `pEquivClass` and their class
sums `pEquivClassSum` used below are defined in
`MathlibExt.Algebra.DeepPowerSumCongruences.PEquivClass`, which also proves that the signs in a
class sum are constant for odd $p$ (`pEquivClassSum_eq_neg_one_pow_smul`).
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- **The zero ideal is a divided-power ideal.** In every commutative ring, the zero ideal is a
divided-power ideal.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 2.2 (the definition). -/
theorem isDividedPowerIdeal_bot {A : Type*} [CommRing A] : IsDividedPowerIdeal (⊥ : Ideal A) := by
  intro a ha k hk
  rw [Ideal.mem_bot] at ha
  refine ⟨0, Ideal.zero_mem _, ?_⟩
  rw [ha, zero_pow (by omega), mul_zero]

/-- **Ideals with divided powers are divided-power ideals.** Let $I$ be an ideal of a commutative
ring $A$. If $I$ carries a divided-power structure $(\gamma_k)_{k \ge 0}$ in the usual sense, then
$I$ is a divided-power ideal: for every $a \in I$ and every $k \ge 1$ there is $c \in I$ with
$a^k = k!\, c$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 2.2 (the maps `γ_k(a) = a ^ k / k!`). -/
theorem DividedPowers.isDividedPowerIdeal {A : Type*} [CommRing A] {I : Ideal A}
    (hI : DividedPowers I) : IsDividedPowerIdeal I := by
  intro a ha k hk
  exact ⟨hI.dpow k a, hI.dpow_mem (by omega) ha, (hI.factorial_mul_dpow_eq_pow ha).symm⟩

/-- **Elementary symmetric functions of a polynomial.** Let $P$ be a polynomial of degree $d$ over
a commutative ring, with $d = 0$ for $P = 0$. For a natural number $n$, $e_n(P)$ is $(-1)^n$ times
the coefficient of $X^{d - n}$ in $P$ if $n \le d$, and $0$ if $n > d$. In particular
$e_0(P) = 1$ when $P$ is monic.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2, Notation. -/
noncomputable def polyElemSymm {A : Type*} [CommRing A] (P : A[X]) (n : ℕ) : A :=
  if n ≤ P.natDegree then (-1) ^ n * P.coeff (P.natDegree - n) else 0

/-- **The zeroth elementary symmetric function of a monic polynomial.** For every monic
polynomial $P$ over a commutative ring, $e_0(P) = 1$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2, Notation. -/
theorem polyElemSymm_zero {A : Type*} [CommRing A] {P : A[X]} (hP : P.Monic) :
    polyElemSymm P 0 = 1 := by
  simp [polyElemSymm, hP.coeff_natDegree]

/-- **Elementary symmetric functions vanish above the degree.** Let $P$ be a polynomial of degree
$d$ over a commutative ring, with $d = 0$ for $P = 0$. Then $e_n(P) = 0$ for every $n > d$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2, Notation. -/
theorem polyElemSymm_of_natDegree_lt {A : Type*} [CommRing A] {P : A[X]} {n : ℕ}
    (h : P.natDegree < n) : polyElemSymm P n = 0 := by
  simp [polyElemSymm, Nat.not_le.mpr h]

/-- **Power sums of a polynomial.** For a polynomial $P$ over a commutative ring $A$, with
elementary symmetric functions $e_i = e_i(P)$, the power sums $p_n = p_n(P) \in A$ are defined
recursively: $p_0$ is the degree of $P$ as a natural number ($0$ for $P = 0$), and for
$n \ge 1$ Newton's identity holds:

$$p_n = \sum_{i=1}^{n-1} (-1)^{i-1} e_i\, p_{n-i} + (-1)^{n-1} n\, e_n.$$

If $P$ is monic and $P = (X - \alpha_1) \cdots (X - \alpha_d)$, then
$p_n = \alpha_1^n + \cdots + \alpha_d^n$ for every $n$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Sections 2.1 and 3.2 (Newton's identities,
Macdonald I.2.11'). -/
noncomputable def polyPowerSum {A : Type*} [CommRing A] (P : A[X]) : ℕ → A
  | 0 => P.natDegree
  | n + 1 => (-1) ^ n * ((n + 1 : ℕ) : A) * polyElemSymm P (n + 1) +
      ∑ i : Fin n, (-1) ^ (i : ℕ) * polyElemSymm P (i + 1) * polyPowerSum P (n - i)
  decreasing_by omega

/-- **The zeroth power sum of a polynomial is its degree.** For every polynomial $P$ over a
commutative ring $A$, the power sum $p_0(P)$ equals the degree of $P$ as a natural number
(taken to be $0$ for $P = 0$), viewed as an element of $A$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2, Notation. -/
theorem polyPowerSum_zero {A : Type*} [CommRing A] (P : A[X]) :
    polyPowerSum P 0 = P.natDegree := by
  rw [polyPowerSum]

/-- **The first power sum is the first elementary symmetric function.** For every polynomial $P$
over a commutative ring, $p_1(P) = e_1(P)$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2 (Newton's identities). -/
theorem polyPowerSum_one {A : Type*} [CommRing A] (P : A[X]) :
    polyPowerSum P 1 = polyElemSymm P 1 := by
  rw [polyPowerSum]
  simp

/-- **Newton's recurrence for the power sums of a polynomial.** For every polynomial $P$ over a
commutative ring and every $n \ge 0$, writing $e_i = e_i(P)$ and $p_i = p_i(P)$ for the
elementary symmetric functions and power sums of $P$,

$$p_{n+1} = (-1)^n (n+1)\, e_{n+1} + \sum_{i=0}^{n-1} (-1)^i e_{i+1}\, p_{n-i}.$$

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2 (Newton's identities). -/
theorem polyPowerSum_succ {A : Type*} [CommRing A] (P : A[X]) (n : ℕ) :
    polyPowerSum P (n + 1) = (-1) ^ n * ((n + 1 : ℕ) : A) * polyElemSymm P (n + 1) +
      ∑ i : Fin n, (-1) ^ (i : ℕ) * polyElemSymm P (i + 1) * polyPowerSum P (n - i) := by
  rw [polyPowerSum]

/-- **Product of a divided-power ideal with an ideal.** Let $A$ be a commutative ring. If
$\mathfrak{a}$ is a divided-power ideal of $A$, then for every ideal $\mathfrak{b}$ of $A$ the
product $\mathfrak{a}\mathfrak{b}$ is a divided-power ideal.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 6 (`integers-2024-A46-cor-6`). -/
public theorem_wanted IsDividedPowerIdeal.mul {A : Type*} [CommRing A] {I : Ideal A}
    (hI : IsDividedPowerIdeal I) (J : Ideal A) : IsDividedPowerIdeal (I * J)

/-- **Congruent elementary symmetric functions give deep power-sum congruences.** Let $p$ be a
prime and let $A$ be a commutative ring without additive torsion in which every natural number
not divisible by $p$ is a unit (a torsion-free $\mathbb{Z}_{(p)}$-algebra). Let
$\mathfrak{a}$ be a divided-power ideal of $A$, let $P, Q \in A[X]$ be monic and let $N \ge 1$;
write $e_n$ and $p_n$ for the elementary symmetric functions and power sums of a polynomial.
If $e_n(P) - e_n(Q) \in \mathfrak{a}$ for every $n$ with $1 \le n \le N$, then there is
$c \in \mathfrak{a}$ with $p_N(P) - p_N(Q) = N c$, that is,
$p_N(P) \equiv p_N(Q) \pmod{N \mathfrak{a}}$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 12 (`integers-2024-A46-prop-12`). -/
public theorem_wanted polyPowerSum_sub_mem_of_polyElemSymm_sub_mem {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] [IsAddTorsionFree A] (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
    {I : Ideal A} (hI : IsDividedPowerIdeal I) {P Q : A[X]} (hP : P.Monic) (hQ : Q.Monic)
    {N : ℕ} (hN : 1 ≤ N)
    (h : ∀ n, 1 ≤ n → n ≤ N → polyElemSymm P n - polyElemSymm Q n ∈ I) :
    ∃ c ∈ I, polyPowerSum P N - polyPowerSum Q N = (N : A) * c

/-- **Power-sum congruences imply elementary symmetric congruences.** Let $p$ be a prime and $A$ a
torsion-free commutative ring in which every natural number not divisible by $p$ is a unit (a
torsion-free $\mathbb{Z}_{(p)}$-algebra). Let $\mathfrak{a}$ be a divided-power ideal of $A$, let
$P, Q \in A[X]$ be monic and let $N$ be a natural number. Suppose that for every $n$ with
$1 \le n \le N$ there is $c \in \mathfrak{a}$ with $p_n(P) - p_n(Q) = n c$, that is,
$p_n(P) \equiv p_n(Q) \pmod{n \mathfrak{a}}$. Then $e_n(P) - e_n(Q) \in \mathfrak{a}$ for every $n$
with $1 \le n \le N$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 13 (`integers-2024-A46-prop-13`). -/
public theorem_wanted polyElemSymm_sub_mem_of_polyPowerSum_sub_mem {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] [IsAddTorsionFree A] (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
    {I : Ideal A} (hI : IsDividedPowerIdeal I) {P Q : A[X]} (hP : P.Monic) (hQ : Q.Monic)
    {N : ℕ}
    (h : ∀ n, 1 ≤ n → n ≤ N → ∃ c ∈ I, polyPowerSum P n - polyPowerSum Q n = (n : A) * c) :
    ∀ n, 1 ≤ n → n ≤ N → polyElemSymm P n - polyElemSymm Q n ∈ I

/-- **The generating function of the elementary symmetric polynomials.** Let $\sigma$ be a finite
set of variables, and in $\mathbb{Q}[x_i : i \in \sigma]$ let $e_k$ be the $k$-th elementary
symmetric polynomial and $p_n = \sum_{i \in \sigma} x_i^n$ the $n$-th power sum. Then, as formal
power series in $t$ with coefficients in $\mathbb{Q}[x_i : i \in \sigma]$,
$$\sum_{k \ge 0} e_k t^k = \exp\Big(\sum_{n \ge 1} \frac{(-1)^{n-1}}{n} p_n t^n\Big).$$

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 20 (`integers-2024-A46-prop-20`). -/
public theorem_wanted exp_signedPowerSumSeries_eq_esymmSeries (σ : Type*) [Fintype σ] :
    (PowerSeries.subst (PowerSeries.mk fun n => if n = 0 then 0 else
        ((-1 : ℚ) ^ (n - 1) / n) • MvPolynomial.psum σ ℚ n) (PowerSeries.exp ℚ) :
        PowerSeries (MvPolynomial σ ℚ)) =
      PowerSeries.mk fun k => MvPolynomial.esymm σ ℚ k

/-- **Elementary symmetric polynomials in terms of power sums.** Let $\sigma$ be a finite set of
variables, and in $\mathbb{Q}[x_i : i \in \sigma]$ let $e_n$ be the $n$-th elementary symmetric
polynomial and $p_k = \sum_{i \in \sigma} x_i^k$ the $k$-th power sum. For a partition $\lambda$
of $n$ with parts $\lambda_1, \dots, \lambda_\ell$, write
$p_\lambda = p_{\lambda_1} \cdots p_{\lambda_\ell}$, $\varepsilon_\lambda = (-1)^{n - \ell}$ and
$z_\lambda = \prod_a a^{r_a} \, r_a!$, where $r_a$ is the number of parts equal to $a$ and the
product runs over the distinct parts $a$. Then for every $n \ge 0$,
$$e_n = \sum_{\lambda \vdash n} \frac{\varepsilon_\lambda}{z_\lambda} \, p_\lambda.$$

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 21 (`integers-2024-A46-cor-21`). -/
public theorem_wanted esymm_eq_sum_partitions (σ : Type*) [Fintype σ] (n : ℕ) :
    MvPolynomial.esymm σ ℚ n = ∑ l : n.Partition,
      ((-1 : ℚ) ^ (n - Multiset.card l.parts) /
        ((l.parts.toFinset.prod fun a => a ^ l.parts.count a * (l.parts.count a).factorial :
          ℕ) : ℚ)) • (l.parts.map (MvPolynomial.psum σ ℚ)).prod

/-- **The Artin–Hasse exponential has $p$-integral coefficients.** Let $p$ be a prime and let
$F(z) = \exp\big(\sum_{j \ge 0} z^{p^j} / p^j\big) \in \mathbb{Q}[[z]]$ be the Artin–Hasse
exponential. For every $n \ge 0$, the coefficient of $z^n$ in $F$, written in lowest terms, has a
denominator not divisible by $p$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 29 (`integers-2024-A46-cor-29`). -/
public theorem_wanted artinHasse_coeff_den_not_dvd (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ¬ p ∣ (PowerSeries.coeff n (PowerSeries.subst
      (PowerSeries.mk fun m : ℕ => if p ^ Nat.log p m = m then (m : ℚ)⁻¹ else 0)
      (PowerSeries.exp ℚ) : PowerSeries ℚ)).den

/-- **The Artin–Hasse exponential as a product.** Let $p$ be a prime, let $\mu$ be the Möbius
function and let $F(z) = \exp\big(\sum_{j \ge 0} z^{p^j} / p^j\big) \in \mathbb{Q}[[z]]$ be the
Artin–Hasse exponential. For $d \ge 1$ and $a \in \mathbb{Q}$ write
$(1 - z^d)^a = \exp\big(a \log(1 - z^d)\big)$, where $\log(1 - z^d) = -\sum_{k \ge 1} z^{dk}/k$.
Then for every $N \ge 0$, $F$ has the same coefficients of $z^0, \dots, z^N$ as the finite product
of the series $(1 - z^d)^{-\mu(d)/d}$ over the integers $1 \le d \le N$ not divisible by $p$.
Since the factors with $d > N$ are $1 + O(z^{N+1})$, this is the identity
$F(z) = \prod_{p \nmid d} (1 - z^d)^{-\mu(d)/d}$ read coefficientwise.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 27 (`integers-2024-A46-prop-27`). -/
public theorem_wanted artinHasse_eq_prod_one_sub_pow (p : ℕ) [Fact p.Prime] (N : ℕ) :
    PowerSeries.trunc (N + 1) (PowerSeries.subst
      (PowerSeries.mk fun m : ℕ => if p ^ Nat.log p m = m then (m : ℚ)⁻¹ else 0)
      (PowerSeries.exp ℚ) : PowerSeries ℚ) =
    PowerSeries.trunc (N + 1) (∏ d ∈ Finset.Icc 1 N with ¬ p ∣ d,
      (PowerSeries.subst (PowerSeries.mk fun m : ℕ => if m ≠ 0 ∧ d ∣ m then
          (-(ArithmeticFunction.moebius d : ℚ) / d) * (-(d : ℚ) / m) else 0)
        (PowerSeries.exp ℚ) : PowerSeries ℚ))

/-- **Multiplicativity of $g_\lambda$ over disjoint parts.** Let $p$ be a prime, $\sigma$ a finite
set of variables, and for a multiset $\lambda$ of parts let $g_\lambda$ be its $p$-equivalence class
sum in $\mathbb{Q}[x_i : i \in \sigma]$. Let $\lambda$ and $\mu$ be multisets of natural numbers,
none of whose elements is divisible by $p$ (so no part is $0$), with no part in common. Then
$g_{\lambda + \mu} = g_\lambda \, g_\mu$, where $\lambda + \mu$ is the union of $\lambda$ and $\mu$
counted with multiplicity. Moreover $g_\lambda = \prod_u g_{(u)^{r_u(\lambda)}}$, the product over
the distinct parts $u$ of $\lambda$, where $r_u(\lambda)$ is the number of times $u$ occurs in
$\lambda$ and $(u)^r$ is the multiset of $r$ copies of $u$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 34 (`integers-2024-A46-lem-34`). -/
public theorem_wanted pEquivClassSum_add_of_disjoint (σ : Type*) [Fintype σ] {p : ℕ}
    [Fact p.Prime] {s t : Multiset ℕ} (hs : ∀ a ∈ s, ¬ p ∣ a) (ht : ∀ a ∈ t, ¬ p ∣ a)
    (hst : ∀ a ∈ s, a ∉ t) :
    pEquivClassSum σ p (s + t) = pEquivClassSum σ p s * pEquivClassSum σ p t ∧
      pEquivClassSum σ p s =
        ∏ u ∈ s.toFinset, pEquivClassSum σ p (Multiset.replicate (s.count u) u)

/-- **$g_\lambda$ is $p$-integral.** Let $p$ be a prime, $\sigma$ a finite set of variables and
$\lambda$ a partition of $n$. Every coefficient of the $p$-equivalence class sum $g_\lambda$ in
$\mathbb{Q}[x_i : i \in \sigma]$ is a rational number whose denominator in lowest terms is not
divisible by $p$.

This is the paper's $g_\lambda \in \Lambda_{\mathbb{Z}_{(p)}}$, in finitely many variables.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 36 (`integers-2024-A46-prop-36`). -/
public theorem_wanted pEquivClassSum_coeff_den_not_dvd (σ : Type*) [Fintype σ] {p : ℕ}
    [Fact p.Prime] {n : ℕ} (l : n.Partition) (m : σ →₀ ℕ) :
    ¬ p ∣ ((pEquivClassSum σ p l.parts).coeff m).den

end

end MetaMathlibExt
