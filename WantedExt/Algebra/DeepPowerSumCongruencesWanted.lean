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
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- **Divided-power ideal.** An ideal $I$ of a commutative ring $A$ is a *divided-power ideal* when
for every $a \in I$ and every integer $k \ge 1$ there is $c \in I$ with $a^k = k! \, c$, that is,
$a^k \in k! \, I$. For a prime $p$, in a torsion-free $\mathbb{Z}_{(p)}$-algebra this says
$a^k / k! \in I$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 2.2. -/
def IsDividedPowerIdeal {A : Type*} [CommRing A] (I : Ideal A) : Prop :=
  ∀ a ∈ I, ∀ k : ℕ, 1 ≤ k → ∃ c ∈ I, a ^ k = (k.factorial : A) * c

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

/-- **A prime-exponent criterion for powers in an ideal.** Let $p$ be a prime, $v_p$ the $p$-adic
valuation, and $\mathfrak{b}$ an ideal of a commutative ring $B$.
The following are equivalent: for every $n \ge 1$ and every $a \in \mathfrak{b}$ there is
$c \in \mathfrak{b}$ with $a^n = p^{v_p(n!)} c$; and for every $a \in \mathfrak{b}$ there is
$c \in \mathfrak{b}$ with $a^p = p c$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 3 (`integers-2024-A46-prop-3`). -/
public theorem_wanted pow_mem_prime_pow_padicValNat_factorial_iff {p : ℕ} [Fact p.Prime]
    {B : Type*} [CommRing B] (I : Ideal B) :
    (∀ n : ℕ, 1 ≤ n → ∀ a ∈ I, ∃ c ∈ I, a ^ n = (p : B) ^ padicValNat p n.factorial * c) ↔
      ∀ a ∈ I, ∃ c ∈ I, a ^ p = (p : B) * c

/-- **The $p$-th power criterion for divided-power ideals.** Let $p$ be a prime and let $A$ be a
commutative ring in which every natural number not divisible by $p$ is a unit (a
$\mathbb{Z}_{(p)}$-algebra). An ideal $\mathfrak{a}$ of $A$ is a divided-power ideal if and only if
for every $a \in \mathfrak{a}$ there is $c \in \mathfrak{a}$ with $a^p = p\,c$, that is,
$a^p \in p\mathfrak{a}$.

The paper also assumes $A$ torsion-free; the statement does not need it.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 4 (`integers-2024-A46-cor-4`). -/
public theorem_wanted isDividedPowerIdeal_iff_pow_prime_mem {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) (I : Ideal A) :
    IsDividedPowerIdeal I ↔ ∀ a ∈ I, ∃ c ∈ I, a ^ p = (p : A) * c

/-- **Divided-power ideals generated by a set.** Let $p$ be a prime and $A$ a commutative ring in
which every natural number not divisible by $p$ is a unit (a $\mathbb{Z}_{(p)}$-algebra). For a
subset $S \subseteq A$, the ideal $\mathfrak{a}$ generated by $S$ is a divided-power ideal if and
only if for every $a \in S$ there is $c \in \mathfrak{a}$ with $a^p = pc$, that is,
$a^p \in p\mathfrak{a}$.

Torsion-freeness of $A$ is not needed.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 5 (`integers-2024-A46-prop-5`). -/
public theorem_wanted isDividedPowerIdeal_span_iff {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) (S : Set A) :
    IsDividedPowerIdeal (Ideal.span S) ↔ ∀ a ∈ S, ∃ c ∈ Ideal.span S, a ^ p = (p : A) * c

/-- **Product of a divided-power ideal with an ideal.** Let $A$ be a commutative ring. If
$\mathfrak{a}$ is a divided-power ideal of $A$, then for every ideal $\mathfrak{b}$ of $A$ the
product $\mathfrak{a}\mathfrak{b}$ is a divided-power ideal.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 6 (`integers-2024-A46-cor-6`). -/
public theorem_wanted IsDividedPowerIdeal.mul {A : Type*} [CommRing A] {I : Ideal A}
    (hI : IsDividedPowerIdeal I) (J : Ideal A) : IsDividedPowerIdeal (I * J)

/-- **Powers of the maximal ideal of a DVR that are divided-power ideals.** Let $p$ be a prime and
let $O$ be a discrete valuation ring with maximal ideal $\mathfrak{m}$ such that
$pO = \mathfrak{m}^e$ for some integer $e \ge 1$. Then for every $k \ge 0$, the ideal
$\mathfrak{m}^k$ is a divided-power ideal if and only if $e \le (p - 1)k$.

Equivalently, with $v_p(\mathfrak{m}) = 1/e$, the condition is $v_p(\mathfrak{m}^k) \ge 1/(p - 1)$.
The paper states this for $p$-adic discrete valuation rings and remarks that it also holds for
localizations of rings of integers; here $O$ is any such ring, and the zero ideal is omitted.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 7 (`integers-2024-A46-lem-7`). -/
public theorem_wanted isDividedPowerIdeal_maximalIdeal_pow_iff {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {e : ℕ} (he0 : e ≠ 0)
    (he : Ideal.span {(p : O)} = IsLocalRing.maximalIdeal O ^ e) (k : ℕ) :
    IsDividedPowerIdeal (IsLocalRing.maximalIdeal O ^ k) ↔ e ≤ (p - 1) * k

/-- **When the maximal ideal of a DVR is a divided-power ideal.** Let $p$ be a prime and let $O$ be
a discrete valuation ring with maximal ideal $\mathfrak{m}$ such that $pO = \mathfrak{m}^e$ for
some integer $e \ge 1$. Then $\mathfrak{m}$ is a divided-power ideal if and only if $e \le p - 1$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 8 (`integers-2024-A46-cor-8`). -/
public theorem_wanted isDividedPowerIdeal_maximalIdeal_iff {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {e : ℕ} (he0 : e ≠ 0)
    (he : Ideal.span {(p : O)} = IsLocalRing.maximalIdeal O ^ e) :
    IsDividedPowerIdeal (IsLocalRing.maximalIdeal O) ↔ e ≤ p - 1

/-- **$(p)$ is a divided-power ideal of $\mathbb{Z}_p$.** For every prime $p$, the ideal generated
by $p$ in the ring $\mathbb{Z}_p$ of $p$-adic integers is a divided-power ideal.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 8, last sentence
(`integers-2024-A46-cor-8`). -/
public theorem_wanted isDividedPowerIdeal_span_prime_padicInt (p : ℕ) [Fact p.Prime] :
    IsDividedPowerIdeal (Ideal.span {(p : ℤ_[p])})

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

/-- **Exponential of a power-sum series restricted to a set of degrees.** Let $\sigma$ be a finite
set of variables, and in $\mathbb{Q}[x_i : i \in \sigma]$ let $p_s = \sum_{i \in \sigma} x_i^s$
be the $s$-th power sum. Let $S$ be a set of natural numbers and let
$P_S(t) = \sum_{s \in S,\ s \ge 1} \frac{(-1)^{s-1}}{s} p_s t^s$. For a partition $\lambda$ of
$n$ with parts $\lambda_1, \dots, \lambda_\ell$, write
$p_\lambda = p_{\lambda_1} \cdots p_{\lambda_\ell}$, $\varepsilon_\lambda = (-1)^{n - \ell}$ and
$z_\lambda = \prod_a a^{r_a} \, r_a!$, where $r_a$ is the number of parts equal to $a$ and the
product runs over the distinct parts $a$. Then, as formal power series in $t$ with coefficients
in $\mathbb{Q}[x_i : i \in \sigma]$, $\exp P_S(t) = \sum_{n \ge 0} c_n t^n$, where $c_n$ is the
sum of $\varepsilon_\lambda p_\lambda / z_\lambda$ over the partitions $\lambda$ of $n$ all of
whose parts lie in $S$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 19 (`integers-2024-A46-prop-19`). -/
public theorem_wanted exp_signedPowerSumSeries_eq_sum_partitions (σ : Type*) [Fintype σ]
    (S : Set ℕ) [DecidablePred (· ∈ S)] :
    (PowerSeries.subst (PowerSeries.mk fun s => if s ∈ S ∧ s ≠ 0 then
        ((-1 : ℚ) ^ (s - 1) / s) • MvPolynomial.psum σ ℚ s else 0) (PowerSeries.exp ℚ) :
        PowerSeries (MvPolynomial σ ℚ)) =
      PowerSeries.mk fun n => ∑ l : n.Partition with ∀ a ∈ l.parts, a ∈ S,
        ((-1 : ℚ) ^ (n - Multiset.card l.parts) /
          ((l.parts.toFinset.prod fun a => a ^ l.parts.count a * (l.parts.count a).factorial :
            ℕ) : ℚ)) • (l.parts.map (MvPolynomial.psum σ ℚ)).prod

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

/-- **Kummer's theorem for multinomial coefficients.** Let $p$ be a prime and let
$r_1, \dots, r_k$ be natural numbers with sum $m$. For $i \ge 1$ let
$c_i = \lfloor ((r_1 \bmod p^i) + \dots + (r_k \bmod p^i)) / p^i \rfloor$. Then

$$v_p\binom{m}{r_1, \dots, r_k} = \sum_{i=1}^{m} c_i.$$

Here $c_i$ is the carry into digit position $i$ when $r_1 + \dots + r_k$ is added in base $p$, and
$c_i = 0$ for $i > m$, so the right side is the sum of all the carries.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Theorem 23 (`integers-2024-A46-thm-23`). -/
public theorem_wanted padicValNat_multinomial_eq_sum_carries {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (r : ι → ℕ) :
    padicValNat p (Nat.multinomial s r) =
      ∑ i ∈ Finset.Icc 1 (∑ j ∈ s, r j), (∑ j ∈ s, r j % p ^ i) / p ^ i

/-- **A valuation bound from Kummer's theorem.** Let $p$ be a prime, let $r_1, \dots, r_k$ be
natural numbers with sum $m$, and let $j$ be an index with $r_j \ne 0$. Then

$$v_p(m) \le v_p(r_j) + v_p\binom{m}{r_1, \dots, r_k},$$

that is, $v_p(r_j) \ge v_p(m) - v_p\binom{m}{r_1, \dots, r_k}$.

The hypothesis $r_j \ne 0$ is needed because $v_p(0)$ is taken to be $0$: for $(r_1, r_2) = (0, p)$
the inequality fails at $j = 1$. With the paper's convention $v_p(0) = \infty$ that case is trivial.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 24 (`integers-2024-A46-cor-24`). -/
public theorem_wanted padicValNat_sum_le_add_padicValNat_multinomial {p : ℕ} [Fact p.Prime]
    {ι : Type*} (s : Finset ι) (r : ι → ℕ) {j : ι} (hj : j ∈ s) (hr : r j ≠ 0) :
    padicValNat p (∑ i ∈ s, r i) ≤ padicValNat p (r j) + padicValNat p (Nat.multinomial s r)

/-- **Powers of elements congruent modulo a divided-power ideal.** Let $p$ be a prime, let $A$ be
a commutative ring in which every natural number not divisible by $p$ is a unit (a
$\mathbb{Z}_{(p)}$-algebra), and let $\mathfrak{a}$ be a divided-power ideal of $A$. If
$x, y \in A$ satisfy $x - y \in \mathfrak{a}$, then for every $m \ge 0$ there is
$c \in \mathfrak{a}$ with $x^{p^m} - y^{p^m} = p^m c$, and for every $n \ge 0$ there is
$c \in \mathfrak{a}$ with $x^n - y^n = n c$.

The ring $A$ is not assumed to be torsion-free.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 25 (`integers-2024-A46-lem-25`). -/
public theorem_wanted pow_sub_pow_mem_of_sub_mem {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]
    (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) {I : Ideal A} (hI : IsDividedPowerIdeal I)
    {x y : A} (hxy : x - y ∈ I) :
    (∀ m : ℕ, ∃ c ∈ I, x ^ p ^ m - y ^ p ^ m = (p : A) ^ m * c) ∧
      ∀ n : ℕ, ∃ c ∈ I, x ^ n - y ^ n = (n : A) * c

/-- **Congruence of products over a partition with multiplicities divisible by $p^v$.** Let $p$
be a prime, $A$ a commutative ring and $\mathfrak{a}$ a divided-power ideal of $A$. Let
$f, g : \mathbb{N} \to A$ satisfy $f_n - g_n \in \mathfrak{a}$ for every $n \ge 1$. For a
partition $\lambda = (\lambda_1, \dots, \lambda_k)$ of a natural number $m$, write
$f_\lambda = f_{\lambda_1} \cdots f_{\lambda_k}$ and
$g_\lambda = g_{\lambda_1} \cdots g_{\lambda_k}$. If $v$ is a natural number such that every part
of $\lambda$ occurs a multiple of $p^v$ times, then $f_\lambda - g_\lambda = p^v c$ for some
$c \in \mathfrak{a}$, that is, $f_\lambda \equiv g_\lambda \bmod p^v \mathfrak{a}$.

The paper takes $v = v_p(\lambda) = \min_i v_p(\lambda_i)$, which is false: for $p = 2$,
$\lambda = (2)$, $A = \mathbb{Z}_{(2)}$, $\mathfrak{a} = (2)$, $f_n = e_n(X^2 + 2)$ and
$g_n = e_n(X^2)$, where $e_n(P)$ is the $n$-th elementary symmetric function of the roots of $P$,
$f_n \equiv g_n \bmod 2$ for all $n$ but $f_2 - g_2 = 2 \notin 4\mathbb{Z}_{(2)}$. The paper's
proof writes $\lambda = \mu^{p^v}$ in the partition monoid, which uses the multiplicity condition
stated here. The paper's symmetric functions are abstracted to arbitrary sequences $f, g$, as the
statement only uses their values.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 26 (`integers-2024-A46-cor-26`). -/
public theorem_wanted multiset_prod_sub_prod_mem_of_count_dvd {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] {I : Ideal A} (hI : IsDividedPowerIdeal I) (f g : ℕ → A)
    (hfg : ∀ n, 1 ≤ n → f n - g n ∈ I) {n : ℕ} (l : n.Partition) {v : ℕ}
    (hv : ∀ a ∈ l.parts, p ^ v ∣ l.parts.count a) :
    ∃ c ∈ I, (l.parts.map f).prod - (l.parts.map g).prod = (p : A) ^ v * c

/-- **Möbius sum over the divisors prime to a given prime.** Let $p$ be a prime, $\mu$ the Möbius
function and $n \ge 1$. The sum of $\mu(d)$ over the divisors $d$ of $n$ with $p \nmid d$ is $1$ if
$n$ is a power of $p$ (including $n = 1 = p^0$) and $0$ otherwise.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 28 (`integers-2024-A46-lem-28`). -/
public theorem_wanted sum_moebius_divisors_not_dvd_prime {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : n ≠ 0) :
    ∑ d ∈ n.divisors with ¬ p ∣ d, ArithmeticFunction.moebius d =
      if p ^ Nat.log p n = n then 1 else 0

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

/-- **$p$-splitting of multisets of parts.** Let $p$ be a natural number and $s$, $t$ multisets of
natural numbers (multisets of parts). Then $s$ is a *$p$-splitting* of $t$ when there is $u \ge 1$
such that $t$ contains the part $pu$ and $s$ is obtained from $t$ by removing one instance of $pu$
and adding $p$ copies of $u$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Definition 30. -/
public def IsPSplitting (p : ℕ) (s t : Multiset ℕ) : Prop :=
  ∃ u, 1 ≤ u ∧ p * u ∈ t ∧ s = t.erase (p * u) + Multiset.replicate p u

/-- **$p$ copies of $u$ form a $p$-splitting of $\{pu\}$.** For every natural number $p$ and every
integer $u \ge 1$, the multiset consisting of $p$ copies of $u$ is a $p$-splitting of the
one-element multiset $\{pu\}$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Definition 30. -/
public theorem isPSplitting_replicate_singleton (p : ℕ) {u : ℕ} (hu : 1 ≤ u) :
    IsPSplitting p (Multiset.replicate p u) {p * u} :=
  ⟨u, hu, Multiset.mem_singleton_self _, by simp⟩

/-- **The $p$-equivalence class of a multiset of parts.** Let $p$ be a natural number and $\lambda$
a multiset of natural numbers whose elements sum to $n$. The $p$-equivalence class $C_\lambda$ is
the set of partitions $\mu$ of $n$ with $\mu \sim_p \lambda$, where $\sim_p$ ($p$-equivalence) is
the equivalence relation on multisets of natural numbers generated by $p$-splitting.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Definition 31. -/
public noncomputable def pEquivClass (p : ℕ) (s : Multiset ℕ) : Finset s.sum.Partition := by
  classical
  exact Finset.univ.filter fun μ => Relation.EqvGen (IsPSplitting p) μ.parts s

/-- **The $p$-equivalence class sum.** Let $\sigma$ be a finite set of variables, let $p$ be a
natural number and let $\lambda$ be a multiset of natural numbers whose elements sum to $n$. In
$\mathbb{Q}[x_i : i \in \sigma]$ let $p_k = \sum_{i \in \sigma} x_i^k$ be the $k$-th power sum. For
a partition $\mu$ of $n$ with parts $\mu_1, \dots, \mu_\ell$, write
$p_\mu = p_{\mu_1} \cdots p_{\mu_\ell}$, $\varepsilon_\mu = (-1)^{n - \ell}$ and
$z_\mu = \prod_a a^{r_a} \, r_a!$, where $r_a$ is the number of parts of $\mu$ equal to $a$ and the
product runs over the distinct parts $a$ of $\mu$. The $p$-equivalence class sum of $\lambda$ is

$$g_\lambda = \sum_{\mu \in C_\lambda} \frac{\varepsilon_\mu}{z_\mu} \, p_\mu,$$

where $C_\lambda$ is the $p$-equivalence class of $\lambda$: the set of partitions of $n$ that are
$p$-equivalent to $\lambda$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 5.2, display (8). -/
public noncomputable def pEquivClassSum (σ : Type*) [Fintype σ] (p : ℕ) (s : Multiset ℕ) :
    MvPolynomial σ ℚ :=
  ∑ μ ∈ pEquivClass p s, ((-1 : ℚ) ^ (s.sum - Multiset.card μ.parts) /
    ((μ.parts.toFinset.prod fun a => a ^ μ.parts.count a * (μ.parts.count a).factorial : ℕ) : ℚ)) • (μ.parts.map (MvPolynomial.psum σ ℚ)).prod

/-- **The class sum of the empty partition.** For every finite set of variables $\sigma$ and every
natural number $p$, the $p$-equivalence class sum of the empty multiset is $g_\emptyset = 1$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 5.2. -/
public theorem pEquivClassSum_zero (σ : Type*) [Fintype σ] (p : ℕ) :
    pEquivClassSum σ p 0 = 1 := by
  classical
  have h0 : ∀ μ : Nat.Partition 0, μ.parts = 0 := fun μ =>
    Multiset.eq_zero_of_forall_notMem fun a ha =>
      (Nat.pos_iff_ne_zero.mp (μ.parts_pos ha)) (Multiset.sum_eq_zero_iff.mp μ.parts_sum a ha)
  have hc : pEquivClass p 0 = Finset.univ := by
    ext μ
    simp only [pEquivClass, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rw [h0 μ]; exact Relation.EqvGen.refl _
  rw [pEquivClassSum, hc]
  change ∑ μ : Nat.Partition 0, _ = 1
  rw [Finset.univ_unique, Finset.sum_singleton, h0]
  simp

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

/-- **For odd $p$ the signs in $g_\lambda$ are constant.** Let $p$ be an odd prime, $\sigma$ a
finite set of variables and $\lambda$ a partition of $n$ with $\ell(\lambda)$ parts. Then the
$p$-equivalence class sum $g_\lambda$ in $\mathbb{Q}[x_i : i \in \sigma]$ satisfies

$$g_\lambda = (-1)^{n - \ell(\lambda)} \sum_{\mu \in C_\lambda} \frac{p_\mu}{z_\mu},$$

where $C_\lambda$ is the $p$-equivalence class of $\lambda$ (the partitions $\mu$ of $n$ with
$\mu \sim_p \lambda$), $p_\mu = \prod_i p_{\mu_i}$ is the product of the power sums
$p_k = \sum_{i \in \sigma} x_i^k$, and $z_\mu = \prod_a a^{r_a} \, r_a!$, the product over the
distinct parts $a$ of $\mu$, with $r_a$ the number of parts of $\mu$ equal to $a$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 35 (`integers-2024-A46-lem-35`). -/
public theorem_wanted pEquivClassSum_eq_neg_one_pow_smul (σ : Type*) [Fintype σ] {p : ℕ}
    [Fact p.Prime] (hp : Odd p) {n : ℕ} (l : n.Partition) :
    pEquivClassSum σ p l.parts = ((-1 : ℚ) ^ (n - Multiset.card l.parts)) •
      ∑ μ ∈ pEquivClass p l.parts, (1 / ((μ.parts.toFinset.prod fun a => a ^ μ.parts.count a * (μ.parts.count a).factorial : ℕ) : ℚ)) • (μ.parts.map (MvPolynomial.psum σ ℚ)).prod

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
