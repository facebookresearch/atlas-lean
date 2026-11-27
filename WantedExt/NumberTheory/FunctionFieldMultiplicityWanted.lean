/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Prime factors with given multiplicity in h-free and h-full polynomials (statements)

Statement-only targets from Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given
Multiplicity in h-Free and h-Full Polynomials over Function Fields*, over a finite field `F`
with `q = Fintype.card F` elements: Erdős–Kac laws for `ω_1` on `h`-free and `ω_h` on `h`-full
monic polynomials, the absence of a normal order for the other `ω_k`, a coprime count, and
Perron's formula. `ω_k(f)` counts the monic irreducible `P` with `P^k ∥ f` (the title's "prime
factors with given multiplicity").
-/

open scoped Interval
open Filter Polynomial UniqueFactorizationMonoid

namespace MetaMathlibExt

attribute [local instance] Classical.propDecidable

@[expose] public section

/--
**Monic polynomials of fixed degree.** For a finite field $F$ and a natural number $n$, $M_n$ is
the finite set of monic polynomials of degree $n$ over $F$: the polynomials
$X^n + c_{n-1} X^{n-1} + \dots + c_1 X + c_0$ with $c_0, \dots, c_{n-1} \in F$.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public noncomputable def fixedDegreeMonic (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) :
    Finset (Polynomial F) :=
  Finset.univ.image fun c : Fin n → F =>
    X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

/--
**Membership in $M_n$.** Let $F$ be a finite field and $n \in \mathbb{N}$. A polynomial $f$ over
$F$ lies in the set $M_n$ of monic polynomials of degree $n$ over $F$ if and only if there are
$c_0, \dots, c_{n-1} \in F$ with $f = X^n + \sum_{i=0}^{n-1} c_i X^i$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem mem_fixedDegreeMonic_iff (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (f : Polynomial F) :
    f ∈ fixedDegreeMonic F n ↔
      ∃ c : Fin n → F, X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ) = f := by
  simp [fixedDegreeMonic]

/--
**The only monic polynomial of degree zero.** For every finite field $F$, the set $M_0$ of monic
polynomials of degree $0$ over $F$ is $\{1\}$.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem fixedDegreeMonic_zero (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    fixedDegreeMonic F 0 = {1} := by
  ext f
  simp [fixedDegreeMonic]

/--
**Monic irreducible polynomials.** For a field $F$, $\mathcal{P}$ is the set of polynomials over
$F$ that are monic and irreducible; these are the prime polynomials of the paper.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public def monicIrreducible (F : Type*) [Field F] : Set (Polynomial F) :=
  {P | P.Monic ∧ Irreducible P}

/--
**Membership in the set of monic irreducible polynomials.** Let $F$ be a field. A polynomial $P$
over $F$ lies in the set $\mathcal{P}$ of monic irreducible polynomials over $F$ if and only if
$P$ is monic and irreducible.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem mem_monicIrreducible_iff (F : Type*) [Field F] (P : Polynomial F) :
    P ∈ monicIrreducible F ↔ P.Monic ∧ Irreducible P := by
  rfl

/--
**$h$-free polynomials.** Let $F$ be a field and $h$ a natural number. The set $S_h$ of
$h$-free polynomials over $F$ consists of the monic polynomials $f$ over $F$ such that no monic
irreducible polynomial $P$ over $F$ satisfies $P^h \mid f$.

The condition makes sense for every natural number $h$; the paper's asymptotic theorems
separately assume $h \ge 2$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public def hFree (F : Type*) [Field F] (h : ℕ) : Set (Polynomial F) :=
  {f | f.Monic ∧ ∀ P ∈ monicIrreducible F, ¬P ^ h ∣ f}

/--
**The polynomial $1$ is $h$-free.** For every field $F$ and every natural number $h \ge 1$,
the constant polynomial $1 \in F[X]$ is $h$-free: it is monic and no $h$-th power of a monic
irreducible polynomial divides it.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem one_mem_hFree (F : Type*) [Field F] (h : ℕ) (hh : 0 < h) :
    (1 : Polynomial F) ∈ hFree F h := by
  refine ⟨monic_one, ?_⟩
  intro P hP hdiv
  have hpow : IsUnit (P ^ h) := isUnit_iff_dvd_one.mpr hdiv
  exact hP.2.not_isUnit ((isUnit_pow_iff hh.ne').mp hpow)

/--
**$h$-full polynomials.** Let $F$ be a field and $h \in \mathbb{N}$. The set $N_h$ of $h$-full
polynomials over $F$ consists of the monic polynomials $f$ such that $P^h$ divides $f$ for
every monic irreducible polynomial $P$ that divides $f$.

As in the source, theorem statements impose $h \ge 2$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public def hFull (F : Type*) [Field F] (h : ℕ) : Set (Polynomial F) :=
  {f | f.Monic ∧ ∀ P ∈ monicIrreducible F, P ∣ f → P ^ h ∣ f}

/--
**The polynomial $1$ is $h$-full.** For every field $F$ and every natural number $h$, the
constant polynomial $1 \in F[X]$ is $h$-full: it is monic, and whenever a monic irreducible
polynomial $P$ divides it, so does $P^h$.

The divisibility condition holds vacuously, since no irreducible polynomial divides $1$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem one_mem_hFull (F : Type*) [Field F] (h : ℕ) :
    (1 : Polynomial F) ∈ hFull F h := by
  refine ⟨monic_one, ?_⟩
  intro P hP hdiv
  exact False.elim (hP.2.not_isUnit (isUnit_iff_dvd_one.mpr hdiv))

/--
**Number of prime factors of given multiplicity.** Let $F$ be a field and $k \in \mathbb{N}$. For a
nonzero polynomial $f$ over $F$, $\omega_k(f)$ is the number of distinct monic irreducible
polynomials $P$ dividing $f$ whose multiplicity in $f$ (the largest $m$ with $P^m \mid f$) is
exactly $k$. For the zero polynomial, $\omega_k(0) = 0$ by convention.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public noncomputable def omegaMult (F : Type*) [Field F] (k : ℕ) (f : Polynomial F) : ℕ := by
  classical
  exact if f = 0 then 0 else
    ((normalizedFactors f).toFinset.filter fun P => (normalizedFactors f).count P = k).card

/--
**$\omega_k$ vanishes at the zero polynomial.** For every field $F$ and every natural number $k$,
$\omega_k(0) = 0$. Here $\omega_k(f)$ is the number of distinct monic irreducible polynomials
dividing a nonzero polynomial $f$ over $F$ with multiplicity exactly $k$, and $\omega_k(0) = 0$
by convention, so this records that convention.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem omegaMult_zero (F : Type*) [Field F] (k : ℕ) :
    omegaMult F k 0 = 0 := by
  simp [omegaMult]

/--
**$\omega_k$ vanishes at the polynomial $1$.** For every field $F$ and every natural number $k$,
$\omega_k(1) = 0$, where $\omega_k(f)$ is the number of distinct monic irreducible polynomials
dividing a nonzero polynomial $f$ over $F$ with multiplicity exactly $k$.

The polynomial $1$ is a unit, so it has no monic irreducible factors.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem omegaMult_one (F : Type*) [Field F] (k : ℕ) :
    omegaMult F k 1 = 0 := by
  simp [omegaMult, normalizedFactors_one]

/--
**Degree-nondecreasing functions.** Let $F$ be a field, $U$ a set of polynomials over $F$ and
$G$ a real-valued function on polynomials over $F$. Then $G$ is degree-nondecreasing on $U$
when for all $f_1, f_2 \in U$ with $\deg f_2 \le \deg f_1$ we have $G(f_2) \le G(f_1)$. Here
$\deg$ is the natural degree, with $\deg 0 = 0$.

In particular $G$ takes the same value on members of $U$ of equal degree. The natural degree is
adequate because $U$ will consist of monic, hence nonzero, polynomials.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3 (definition preceding the requested normal-order results).
-/
public def IsDegreeNondecreasing (F : Type*) [Field F] (U : Set (Polynomial F))
    (G : Polynomial F → ℝ) : Prop :=
  ∀ ⦃f₁ f₂ : Polynomial F⦄, f₁ ∈ U → f₂ ∈ U → f₂.natDegree ≤ f₁.natDegree →
    G f₂ ≤ G f₁

/--
**Constant functions are degree-nondecreasing.** Let $F$ be a field and $U$ a set of
polynomials over $F$. For every real number $c$, the constant function with value $c$ is
degree-nondecreasing on $U$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3 (definition preceding the requested normal-order results).
-/
public theorem isDegreeNondecreasing_const (F : Type*) [Field F]
    (U : Set (Polynomial F)) (c : ℝ) :
    IsDegreeNondecreasing F U (fun _ => c) := by
  intro f₁ f₂ hf₁ hf₂ hdeg
  exact le_rfl

/--
**Normal order on a set of polynomials.** Let $F$ be a finite field, let $U$ be a set of
polynomials over $F$, and let $g, G$ be real-valued functions on polynomials over $F$. For
$n \in \mathbb{N}$ let $M_n$ be the set of monic polynomials of degree $n$ over $F$. Then $g$
has normal order $G$ on $U$ when $g$ and $G$ are nonnegative on $U$, $G$ is
degree-nondecreasing on $U$ (for $f_1, f_2 \in U$, $\deg f_2 \le \deg f_1$ implies
$G(f_2) \le G(f_1)$, with $\deg$ the natural degree), and for every real $\varepsilon > 0$ the
number of $f \in U \cap M_n$ for which $(1 - \varepsilon)G(f) < g(f) < (1 + \varepsilon)G(f)$
fails is $o(|U \cap M_n|)$ as $n \to \infty$.

The paper takes $g, G : U \to \mathbb{R}_{\ge 0}$; here both are total real-valued functions,
with nonnegativity imposed on $U$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3 (definition preceding the requested normal-order results).
-/
public noncomputable def HasNormalOrder (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (U : Set (Polynomial F)) (g G : Polynomial F → ℝ) : Prop := by
  classical
  exact
    (∀ f ∈ U, 0 ≤ g f) ∧ (∀ f ∈ U, 0 ≤ G f) ∧ IsDegreeNondecreasing F U G ∧
      ∀ ε : ℝ, 0 < ε →
        Asymptotics.IsLittleO atTop
          (fun n : ℕ =>
            (((fixedDegreeMonic F n).filter fun f =>
              f ∈ U ∧ ¬((1 - ε) * G f < g f ∧ g f < (1 + ε) * G f)).card : ℝ))
          (fun n : ℕ => (((fixedDegreeMonic F n).filter fun f => f ∈ U).card : ℝ))

/--
**Normal orders are nonnegative.** Let $F$ be a finite field, $U$ a set of polynomials over $F$,
and $g, G$ real-valued functions on polynomials over $F$. If $g$ has normal order $G$ on $U$, then
$G(f) \ge 0$ for every $f \in U$.

This is the second defining clause of a normal order.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3 (definition preceding the requested normal-order results).
-/
public theorem HasNormalOrder.nonnegative (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (U : Set (Polynomial F)) (g G : Polynomial F → ℝ)
    (horder : HasNormalOrder F U g G) (f : Polynomial F) (hf : f ∈ U) :
    0 ≤ G f := by
  exact horder.2.1 f hf

/--
**Erdős–Kac theorem for $\omega_1$ on $h$-free polynomials.** Let $F$ be a finite field, let
$h \ge 2$ and let $\alpha \le \beta$ be real numbers. A monic polynomial $f$ over $F$ is $h$-free
if $P^h \nmid f$ for every monic irreducible $P$, and $\omega_1(f)$ is the number of distinct
monic irreducible $P$ that divide $f$ with multiplicity exactly $1$. For each $n$, let $p_n$ be
the number of $h$-free monic polynomials $f$ of degree $n$ over $F$ with
$$\alpha \le \frac{\omega_1(f) - \log n}{\sqrt{\log n}} \le \beta,$$
divided by the number of all $h$-free monic polynomials of degree $n$ over $F$. Then
$p_n \to \frac{1}{\sqrt{2\pi}} \int_\alpha^\beta e^{-t^2/2}\,dt$ as $n \to \infty$.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 2.
-/
public theorem_wanted erdosKac_omegaOne_hFree
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (hh : 2 ≤ h) (α β : ℝ) (hαβ : α ≤ β) :
    Tendsto
      (fun n : ℕ =>
        (((fixedDegreeMonic F n).filter fun f =>
          f ∈ hFree F h ∧
            α ≤ ((omegaMult F 1 f : ℝ) - Real.log (n : ℝ)) /
              Real.sqrt (Real.log (n : ℝ)) ∧
            ((omegaMult F 1 f : ℝ) - Real.log (n : ℝ)) /
              Real.sqrt (Real.log (n : ℝ)) ≤ β).card : ℝ) /
          (((fixedDegreeMonic F n).filter fun f => f ∈ hFree F h).card : ℝ))
      atTop
      (nhds ((1 / Real.sqrt (2 * Real.pi)) *
        ∫ t : ℝ in α..β, Real.exp (-(t ^ 2) / 2)))

/--
**$\omega_k$ has no normal order on $h$-free polynomials for $1 < k < h$.** Let $F$ be a finite
field, let $h \ge 2$ and $1 < k < h$, and let $S_h$ be the set of $h$-free monic polynomials over
$F$. Let $G$ be a real-valued function on polynomials over $F$ that is nonnegative on $S_h$ and
degree-nondecreasing on $S_h$, that is, $G(f_2) \le G(f_1)$ whenever $f_1, f_2 \in S_h$ and
$\deg f_2 \le \deg f_1$. Then $\omega_k$, the number of monic irreducible factors of multiplicity
exactly $k$, viewed as a real-valued function, does not have normal order $G$ on $S_h$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 4.
-/
public theorem_wanted omegaMult_no_normalOrder_hFree
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k : ℕ) (hh : 2 ≤ h) (hk₁ : 1 < k) (hkh : k < h)
    (G : Polynomial F → ℝ)
    (hGnonneg : ∀ f ∈ hFree F h, 0 ≤ G f)
    (hGmono : IsDegreeNondecreasing F (hFree F h) G) :
    ¬HasNormalOrder F (hFree F h) (fun f => (omegaMult F k f : ℝ)) G

/--
**Erdős–Kac theorem for $\omega_h$ on $h$-full polynomials.** Let $F$ be a finite field, let
$h \ge 2$ and let $\alpha \le \beta$ be real numbers. A monic polynomial $f$ over $F$ is $h$-full
if $P^h \mid f$ for every monic irreducible $P$ dividing $f$, and $\omega_h(f)$ is the number of
distinct monic irreducible $P$ that divide $f$ with multiplicity exactly $h$. For each $n$, let
$p_n$ be the number of $h$-full monic polynomials $f$ of degree $n$ over $F$ with
$$\alpha \le \frac{\omega_h(f) - \log(n/h)}{\sqrt{\log(n/h)}} \le \beta,$$
divided by the number of all $h$-full monic polynomials of degree $n$ over $F$, where $n/h$ is
real division. Then $p_n \to \frac{1}{\sqrt{2\pi}} \int_\alpha^\beta e^{-t^2/2}\,dt$ as
$n \to \infty$.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 6.
-/
public theorem_wanted erdosKac_omegaH_hFull
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (hh : 2 ≤ h) (α β : ℝ) (hαβ : α ≤ β) :
    Tendsto
      (fun n : ℕ =>
        (((fixedDegreeMonic F n).filter fun f =>
          f ∈ hFull F h ∧
            α ≤ ((omegaMult F h f : ℝ) - Real.log ((n : ℝ) / (h : ℝ))) /
              Real.sqrt (Real.log ((n : ℝ) / (h : ℝ))) ∧
            ((omegaMult F h f : ℝ) - Real.log ((n : ℝ) / (h : ℝ))) /
              Real.sqrt (Real.log ((n : ℝ) / (h : ℝ))) ≤ β).card : ℝ) /
          (((fixedDegreeMonic F n).filter fun f => f ∈ hFull F h).card : ℝ))
      atTop
      (nhds ((1 / Real.sqrt (2 * Real.pi)) *
        ∫ t : ℝ in α..β, Real.exp (-(t ^ 2) / 2)))

/--
**$\omega_k$ has no normal order on $h$-full polynomials for $k > h$.** Let $F$ be a finite
field, let $2 \le h < k$, and let $N_h$ be the set of $h$-full monic polynomials over $F$. Let
$G$ be a real-valued function on polynomials over $F$ that is nonnegative on $N_h$ and
degree-nondecreasing on $N_h$, that is, $G(f_2) \le G(f_1)$ whenever $f_1, f_2 \in N_h$ and
$\deg f_2 \le \deg f_1$. Then $\omega_k$, the number of monic irreducible factors of multiplicity
exactly $k$, viewed as a real-valued function, does not have normal order $G$ on $N_h$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 8.
-/
public theorem_wanted omegaMult_no_normalOrder_hFull
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k : ℕ) (hh : 2 ≤ h) (hhk : h < k)
    (G : Polynomial F → ℝ)
    (hGnonneg : ∀ f ∈ hFull F h, 0 ≤ G f)
    (hGmono : IsDegreeNondecreasing F (hFull F h) G) :
    ¬HasNormalOrder F (hFull F h) (fun f => (omegaMult F k f : ℝ)) G

/--
**Counting $\ell$-free polynomials coprime to an irreducible.** Let $F$ be a finite field with
$q$ elements, let $\ell \ge 2$ and let $d$ be a natural number. Call a monic polynomial over $F$
$\ell$-free if it is divisible by the $\ell$-th power of no monic irreducible polynomial. There is a
constant $C \ge 0$ such that for every monic irreducible polynomial $P$ over $F$ of degree $d$,
with $|P| = q^{d}$, and every natural number $n$, the number $N$ of $\ell$-free monic polynomials
of degree $n$ over $F$ that are coprime to $P$ satisfies
$$\left| N - \frac{q^n (1 - q^{1-\ell})(1 - |P|^{-1})}{1 - |P|^{-\ell}} \right| \le C.$$
So $C$ depends on $F$, $\ell$ and $d$ but not on $P$ or $n$.

The source states the lemma for $\ell > 0$. The factor $1 - q^{1-\ell}$ equals $1/\zeta_q(\ell)$,
where $\zeta_q(s) = 1/(1 - q^{1-s})$ is the zeta function of the polynomial ring over $F$; it has
a pole at $s = 1$, so the statement here assumes $\ell \ge 2$.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 3.
-/
public theorem_wanted card_hFree_coprime_irreducible_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P ∈ monicIrreducible F, P.natDegree = d → ∀ n : ℕ,
      |(((fixedDegreeMonic F n).filter fun f =>
          f ∈ hFree F ℓ ∧ IsCoprime f P).card : ℝ) -
        ((Fintype.card F : ℝ) ^ n *
          (1 - (Fintype.card F : ℝ) ^ (1 - (ℓ : ℤ))) *
          (1 - ((Fintype.card F : ℝ) ^ P.natDegree)⁻¹) /
          (1 - (((Fintype.card F : ℝ) ^ P.natDegree) ^ ℓ)⁻¹))| ≤ C

/--
**Perron's formula for degree slices of monic polynomials.** Let $F$ be a finite field,
let $M_m$ be the set of monic polynomials of degree $m$ over $F$, let
$a \colon F[X] \to \mathbb{C}$, and write $c_m = \sum_{f \in M_m} a(f)$. Let $r$ be a real
number with $0 < r < 1$ such that the series $\sum_{m \ge 0} |c_m| r^m$ converges, and let
$A \colon \mathbb{C} \to \mathbb{C}$ satisfy $A(u) = \sum_{m \ge 0} c_m u^m$ for every
complex $u$ with $|u| = r$. Then for every $n \ge 0$,
$$c_n = \frac{1}{2\pi i} \oint_{|u| = r} \frac{A(u)}{u^{n+1}}\, du,$$
where the circle $|u| = r$ is traversed once counterclockwise.

Convergence of $\sum |c_m| r^m$ at the single radius $r$ stands in for the paper's uniform
absolute convergence on the closed disk, and $A$ only has to agree with the series on the
circle, the only values the contour integral sees.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 9.
-/
public theorem_wanted perron_formula_polynomial_degree_slice
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (a : Polynomial F → ℂ) (A : ℂ → ℂ) (r : ℝ)
    (hr₀ : 0 < r) (hr₁ : r < 1)
    (hsum : Summable fun n : ℕ =>
      ‖∑ f ∈ fixedDegreeMonic F n, a f‖ * r ^ n)
    (hA : ∀ u : ℂ, ‖u‖ = r → A u = ∑' m : ℕ,
      (∑ f ∈ fixedDegreeMonic F m, a f) * u ^ m)
    (n : ℕ) :
    (∑ f ∈ fixedDegreeMonic F n, a f) =
      (1 / (2 * Real.pi * Complex.I)) *
        ∮ u in C(0, r), A u / u ^ (n + 1)


/-- **The polynomial norm $q^{\deg f}$ over a finite field.** Let $F$ be a finite field with
$q$ elements. The norm of a polynomial $f \in F[X]$ is the real number $|f| = q^{\deg f}$ if
$f \neq 0$, and $|0| = 0$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Introduction. -/
public noncomputable def polyNorm (F : Type*) [Field F] [Fintype F] (f : Polynomial F) : ℝ :=
  if f = 0 then 0 else (Fintype.card F : ℝ) ^ f.natDegree

/-- **The zero polynomial has norm $0$.** For every finite field $F$, the norm of the zero
polynomial in $F[X]$ is $|0| = 0$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Introduction. -/
public theorem polyNorm_zero (F : Type*) [Field F] [Fintype F] : polyNorm F 0 = 0 := by
  simp [polyNorm]

/-- **A nonzero polynomial has norm $q^{\deg f}$.** Let $F$ be a finite field with $q$
elements. Every nonzero polynomial $f \in F[X]$ has norm $|f| = q^{\deg f}$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Introduction. -/
public theorem polyNorm_of_ne_zero (F : Type*) [Field F] [Fintype F] {f : Polynomial F}
    (hf : f ≠ 0) : polyNorm F f = (Fintype.card F : ℝ) ^ f.natDegree := by
  simp [polyNorm, hf]

/-- **Function field Mertens constant.** For a finite field $F$ with $q$ elements, the analogue
of the first Mertens constant is
$$B_1 = \gamma + \sum_P \left(\log\left(1 - \frac{1}{|P|}\right) + \frac{1}{|P|}\right),$$
where $\gamma$ is the Euler–Mascheroni constant, the sum runs over the monic irreducible
polynomials $P$ over $F$, and $|P| = q^{\deg P}$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Introduction. -/
public noncomputable def functionFieldMertensConstant (F : Type*) [Field F] [Fintype F] : ℝ :=
  Real.eulerMascheroniConstant +
    ∑' P : monicIrreducible F, (Real.log (1 - 1 / polyNorm F P) + 1 / polyNorm F P)

/-- **Series for the function field Mertens constant.** For a finite field $F$ with $q$ elements,
the function field Mertens constant $B_1$ of $F$ equals
$$\gamma + \sum_P \left(\log\left(1 - \frac{1}{|P|}\right) + \frac{1}{|P|}\right),$$
where $\gamma$ is the Euler–Mascheroni constant, the sum runs over the monic irreducible
polynomials $P$ over $F$, and $|P| = q^{\deg P}$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Introduction. -/
public theorem functionFieldMertensConstant_eq (F : Type*) [Field F] [Fintype F] :
    functionFieldMertensConstant F = Real.eulerMascheroniConstant +
      ∑' P : monicIrreducible F, (Real.log (1 - 1 / polyNorm F P) + 1 / polyNorm F P) := rfl

/-- **Moments of $\omega_k$ over $h$-free polynomials.** Let $F$ be a finite field and let $h$,
$k$, $j$, $n$ be natural numbers. Let $S_h$ be the set of $h$-free monic polynomials over $F$
(those divisible by no $P^h$ with $P$ monic irreducible), $M_n$ the set of monic polynomials of
degree $n$ over $F$, and $\omega_k(f)$ the number of distinct monic irreducible factors of $f$
whose multiplicity is exactly $k$. The $j$-th moment of $\omega_k$ over the $h$-free monic
polynomials of degree $n$ is the real number
$$\frac{1}{|S_h \cap M_n|} \sum_{f \in S_h \cap M_n} \omega_k(f)^j,$$
which is $0$ when $S_h \cap M_n$ is empty.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 1 and 3. -/
public noncomputable def hFreeMoment (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k j n : ℕ) : ℝ :=
  (∑ f ∈ (fixedDegreeMonic F n).filter (· ∈ hFree F h), (omegaMult F k f : ℝ) ^ j) /
    (((fixedDegreeMonic F n).filter (· ∈ hFree F h)).card : ℝ)

/-- **Explicit formula for the moments over h-free polynomials.** Let $F$ be a finite field and
let $h, k, j, n$ be natural numbers. Write $M_n$ for the monic polynomials of degree $n$ over
$F$, $S_h$ for the $h$-free monic polynomials (those divisible by the $h$-th power of no monic
irreducible polynomial) and $\omega_k(f)$ for the number of distinct monic irreducible factors of
$f$ of multiplicity exactly $k$. Then the $j$-th moment of $\omega_k$ over $S_h \cap M_n$ equals
$$\frac{1}{|S_h \cap M_n|} \sum_{f \in S_h \cap M_n} \omega_k(f)^j,$$
which is $0$ when $S_h \cap M_n$ is empty.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 1 and 3. -/
public theorem hFreeMoment_eq (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k j n : ℕ) : hFreeMoment F h k j n =
      (∑ f ∈ (fixedDegreeMonic F n).filter (· ∈ hFree F h), (omegaMult F k f : ℝ) ^ j) /
        (((fixedDegreeMonic F n).filter (· ∈ hFree F h)).card : ℝ) := rfl

/-- **The prime sum $T_h$.** Let $F$ be a finite field with $q$ elements, let $h$ be a natural
number, and write $|P| = q^{\deg P}$ for a monic irreducible polynomial $P$ over $F$. The prime
sum $T_h$ is the real number
$$T_h = \sum_P \frac{|P|^{h-1} - 1}{|P|\,(|P|^h - 1)},$$
the sum running over all monic irreducible polynomials $P$ over $F$, where, when $h = 0$, the
exponent $h - 1$ is read as $0$ and each summand, whose denominator then vanishes, is read as $0$;
the sum is taken to be $0$ if it does not converge absolutely.
For $h \ge 2$ it is the prime sum in the constant term of the mean number of monic irreducible
factors of multiplicity exactly one of a monic $h$-free polynomial of degree $n$ (Theorem 1).

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1. -/
public noncomputable def hFreeOmegaOneSum (F : Type*) [Field F] [Fintype F] (h : ℕ) : ℝ :=
  ∑' P : monicIrreducible F,
    (polyNorm F P ^ (h - 1) - 1) / (polyNorm F P * (polyNorm F P ^ h - 1))

/-- **Unfolding the prime sum $T_h$.** Let $F$ be a finite field with $q$ elements, let $h$ be a
natural number, and write $|P| = q^{\deg P}$ for a monic irreducible polynomial $P$ over $F$. Then
the prime sum $T_h$ equals the real sum over all monic irreducible polynomials $P$ over $F$
$$\sum_P \frac{|P|^{h-1} - 1}{|P|\,(|P|^h - 1)},$$
where, when $h = 0$, the exponent $h - 1$ is read as $0$ and each summand, whose denominator then
vanishes, is read as $0$; the sum is taken to be $0$ if it does not converge absolutely.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1. -/
public theorem hFreeOmegaOneSum_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) :
    hFreeOmegaOneSum F h = ∑' P : monicIrreducible F,
      (polyNorm F P ^ (h - 1) - 1) / (polyNorm F P * (polyNorm F P ^ h - 1)) := rfl

/-- **The squared prime sum $U_h$ for multiplicity $1$ on $h$-free polynomials.** Let $F$ be a
finite field with $q$ elements, let $h$ be a natural number, and for a monic irreducible
polynomial $P$ over $F$ write $|P| = q^{\deg P}$. Then $U_h$ is the real number
$$U_h = \sum_P \left(\frac{|P|^{\max(h-2,\,0)} (|P| - 1)}{|P|^h - 1}\right)^2,$$
the sum over all monic irreducible $P$, where a quotient with zero denominator (only when
$h = 0$) is read as $0$ and the sum is $0$ when the series does not converge absolutely.

$U_h$ enters the constants in the second moment and the variance of the number of distinct monic
irreducible factors of multiplicity exactly $1$ over $h$-free polynomials.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1. -/
public noncomputable def hFreeOmegaOneSqSum (F : Type*) [Field F] [Fintype F] (h : ℕ) : ℝ :=
  ∑' P : monicIrreducible F,
    (polyNorm F P ^ (h - 2) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1)) ^ 2

/-- **Series formula for the squared prime sum $U_h$.** Let $F$ be a finite field with $q$
elements, let $h$ be a natural number, and for a monic irreducible polynomial $P$ over $F$ write
$|P| = q^{\deg P}$. Then the squared prime sum $U_h$ for multiplicity $1$ on $h$-free polynomials
equals
$$\sum_P \left(\frac{|P|^{\max(h-2,\,0)} (|P| - 1)}{|P|^h - 1}\right)^2,$$
the sum over all monic irreducible $P$, where a quotient with zero denominator (only when
$h = 0$) is read as $0$ and the sum is $0$ when the series does not converge absolutely.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1. -/
public theorem hFreeOmegaOneSqSum_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) :
    hFreeOmegaOneSqSum F h = ∑' P : monicIrreducible F,
      (polyNorm F P ^ (h - 2) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1)) ^ 2 := rfl

/-- **The prime sum $S_{h,k}$ for multiplicity $k$ on $h$-free polynomials.** Let $F$ be a finite
field with $q$ elements and let $h$, $k$ be natural numbers. For a monic irreducible polynomial
$P$ over $F$ write $|P| = q^{\deg P}$ and $a_P = |P|^{\max(h-k-1,\,0)} (|P| - 1)/(|P|^h - 1)$,
read as $0$ when the denominator vanishes (only when $h = 0$). Then $S_{h,k}$ is the real number
$\sum_P a_P$, the sum over all monic irreducible $P$, taken to be $0$ when the series does not
converge absolutely.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3. -/
public noncomputable def hFreeOmegaMultSum (F : Type*) [Field F] [Fintype F] (h k : ℕ) : ℝ :=
  ∑' P : monicIrreducible F,
    polyNorm F P ^ (h - k - 1) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1)

/-- **Series formula for the prime sum $S_{h,k}$.** Let $F$ be a finite field with $q$ elements
and let $h$, $k$ be natural numbers. For a monic irreducible polynomial $P$ over $F$ write
$|P| = q^{\deg P}$ and $a_P = |P|^{\max(h-k-1,\,0)} (|P| - 1)/(|P|^h - 1)$, read as $0$ when the
denominator vanishes (only when $h = 0$). Then the prime sum $S_{h,k}$ for multiplicity $k$ on
$h$-free polynomials equals $\sum_P a_P$, the sum over all monic irreducible $P$, taken to be $0$
when the series does not converge absolutely.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3. -/
public theorem hFreeOmegaMultSum_eq (F : Type*) [Field F] [Fintype F] (h k : ℕ) :
    hFreeOmegaMultSum F h k = ∑' P : monicIrreducible F,
      polyNorm F P ^ (h - k - 1) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1) := rfl

/-- **Squared prime sum for multiplicity $k$ on $h$-free polynomials.** Let $F$ be a finite field
with $q$ elements and let $h$, $k$ be natural numbers. For a monic irreducible polynomial $P$
over $F$ write $|P| = q^{\deg P}$ and $a_P = |P|^{\max(h-k-1,\,0)} (|P| - 1)/(|P|^h - 1)$, read
as $0$ when the denominator vanishes (only when $h = 0$). The squared prime sum is the real
number $\sum_P a_P^2$, the sum over all monic irreducible $P$, taken to be $0$ when the series
does not converge absolutely.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3. -/
public noncomputable def hFreeOmegaMultSqSum (F : Type*) [Field F] [Fintype F] (h k : ℕ) : ℝ :=
  ∑' P : monicIrreducible F,
    (polyNorm F P ^ (h - k - 1) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1)) ^ 2

/-- **Series formula for the squared prime sum for multiplicity $k$ on $h$-free polynomials.**
Let $F$ be a finite field with $q$ elements and let $h$, $k$ be natural numbers. For a monic
irreducible polynomial $P$ over $F$ write $|P| = q^{\deg P}$ and
$a_P = |P|^{\max(h-k-1,\,0)} (|P| - 1)/(|P|^h - 1)$, read as $0$ when the denominator vanishes
(only when $h = 0$). Then the squared prime sum for multiplicity $k$ on $h$-free polynomials
equals $\sum_P a_P^2$, the sum over all monic irreducible $P$, taken to be $0$ when the series
does not converge absolutely.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3. -/
public theorem hFreeOmegaMultSqSum_eq (F : Type*) [Field F] [Fintype F] (h k : ℕ) :
    hFreeOmegaMultSqSum F h k = ∑' P : monicIrreducible F,
      (polyNorm F P ^ (h - k - 1) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1)) ^ 2 := rfl

/-- **Mean of $\omega_1$ over $h$-free polynomials.** Let $F$ be a finite field with $q$ elements
and let $h \ge 2$. Let $\omega_1(f)$ be the number of monic irreducible $P$ dividing $f$ exactly
once, write $|P| = q^{\deg P}$, and let $B_1 = \gamma + \sum_P (\log(1 - 1/|P|) + 1/|P|)$ be the
function field Mertens constant, with $\gamma$ the Euler–Mascheroni constant, and let
$T_h = \sum_P (|P|^{h-1} - 1)/(|P|(|P|^h - 1))$, both sums over monic irreducible $P$. Then the
mean of $\omega_1$ over the $h$-free monic polynomials of degree $n$ over $F$ is
$\log n + B_1 - T_h + O(1/n)$ as $n \to \infty$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1, Equation (4) (`integers-2025-A9-thm-1`). -/
public theorem_wanted omegaOne_hFree_mean_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) :
    (fun n : ℕ => hFreeMoment F h 1 1 n -
        (Real.log n + (functionFieldMertensConstant F - hFreeOmegaOneSum F h)))
      =O[atTop] (fun n : ℕ => 1 / (n : ℝ))

/-- **Second moment of $\omega_1$ over $h$-free polynomials.** Let $F$ be a finite field with $q$
elements, let $h \ge 2$ and let $\varepsilon > 0$. Let $\omega_1(f)$ be the number of monic
irreducible $P$ dividing $f$ exactly once, write $S_h \cap M_n$ for the set of $h$-free monic
polynomials of degree $n$ over $F$ and $|P| = q^{\deg P}$, and let
$B_1 = \gamma + \sum_P (\log(1 - 1/|P|) + 1/|P|)$ be the function field Mertens constant, with
$\gamma$ the Euler–Mascheroni constant, $T_h = \sum_P (|P|^{h-1} - 1)/(|P|(|P|^h - 1))$ and
$U_h = \sum_P (|P|^{h-2}(|P| - 1)/(|P|^h - 1))^2$, all sums over monic irreducible $P$. Then the
mean of $\omega_1^2$ over $S_h \cap M_n$ is $\log^2 n + C_2 \log n + C_3 + O(n^{\varepsilon - 1})$
as $n \to \infty$, where $C_2 = 2(B_1 - T_h) + 1$ and
$C_3 = B_1^2 + B_1 - \pi^2/6 - U_h + T_h^2 - (2B_1 + 1) T_h$.

The printed error $O_\varepsilon(q^n/n^{1-\varepsilon})$ is the error of the unnormalized sum in
the paper's proof; divided by $|S_h \cap M_n| = q^n/\zeta_q(h)$ for $n \ge h$, where
$\zeta_q(h) = (1 - q^{1-h})^{-1}$, it is $O_\varepsilon(n^{\varepsilon-1})$, the order that the
paper's remark (an extra factor $n^\varepsilon$ over the first moment's $O(1/n)$) and its
variance formula state.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1, Equation (5) (`integers-2025-A9-thm-1`). -/
public theorem_wanted omegaOne_hFree_secondMoment_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (ε : ℝ)
    (hε : 0 < ε) :
    (fun n : ℕ => hFreeMoment F h 1 2 n -
        (Real.log n ^ 2 +
          (2 * (functionFieldMertensConstant F - hFreeOmegaOneSum F h) + 1) * Real.log n +
          (functionFieldMertensConstant F ^ 2 + functionFieldMertensConstant F - Real.pi ^ 2 / 6 -
            hFreeOmegaOneSqSum F h + hFreeOmegaOneSum F h ^ 2 -
            (2 * functionFieldMertensConstant F + 1) * hFreeOmegaOneSum F h)))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- **Variance of $\omega_1$ over $h$-free polynomials.** Let $F$ be a finite field with $q$
elements, let $h \ge 2$ and let $\varepsilon > 0$. Let $\omega_1(f)$ be the number of monic
irreducible $P$ dividing $f$ exactly once, write $|P| = q^{\deg P}$, and let
$B_1 = \gamma + \sum_P (\log(1 - 1/|P|) + 1/|P|)$ be the function field Mertens constant, with
$\gamma$ the Euler–Mascheroni constant, $T_h = \sum_P (|P|^{h-1} - 1)/(|P|(|P|^h - 1))$ and
$U_h = \sum_P (|P|^{h-2}(|P| - 1)/(|P|^h - 1))^2$, all sums over monic irreducible $P$. Then the
variance of $\omega_1$ over the $h$-free monic polynomials of degree $n$ over $F$, that is, the
mean of $\omega_1^2$ minus the square of the mean of $\omega_1$, is
$\log n + B_1 - \pi^2/6 - U_h - T_h + O(n^{\varepsilon - 1})$ as $n \to \infty$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1 (`integers-2025-A9-thm-1`). -/
public theorem_wanted omegaOne_hFree_variance_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (ε : ℝ)
    (hε : 0 < ε) :
    (fun n : ℕ => hFreeMoment F h 1 2 n - hFreeMoment F h 1 1 n ^ 2 -
        (Real.log n + (functionFieldMertensConstant F - Real.pi ^ 2 / 6 -
          hFreeOmegaOneSqSum F h - hFreeOmegaOneSum F h)))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- **Mean of $\omega_k$ over $h$-free polynomials.** Let $F$ be a finite field with $q$ elements,
let $h, k$ be natural numbers with $1 < k < h$, and let $\varepsilon > 0$. Write $S_h \cap M_n$ for
the set of monic polynomials $f$ of degree $n$ over $F$ that are $h$-free (no $P^h$ with $P$ monic
irreducible divides $f$), and $\omega_k(f)$ for the number of monic irreducible $P$ that divide $f$
exactly $k$ times. For monic irreducible $P$ put $|P| = q^{\deg P}$ and
$a_P = |P|^{h-k-1}(|P| - 1)/(|P|^h - 1)$, and let $S_{h,k} = \sum_P a_P$, the sum over monic
irreducible $P$. Then, as $n \to \infty$, the mean of $\omega_k$ over
$S_h \cap M_n$ is $S_{h,k} + O(q^{n/k - n + \varepsilon n})$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3, Equation (6) (`integers-2025-A9-thm-3`). -/
public theorem_wanted omegaMult_hFree_mean_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h k : ℕ) (hk : 1 < k) (hkh : k < h)
    (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => hFreeMoment F h k 1 n - hFreeOmegaMultSum F h k)
      =O[atTop] (fun n : ℕ => (Fintype.card F : ℝ) ^ ((n : ℝ) / k - n + ε * n))

/-- **Second moment of $\omega_k$ over $h$-free polynomials.** Let $F$ be a finite field with $q$
elements, let $h, k$ be natural numbers with $1 < k < h$, and let $\varepsilon > 0$. Write
$S_h \cap M_n$ for the set of monic polynomials $f$ of degree $n$ over $F$ that are $h$-free (no
$P^h$ with $P$ monic irreducible divides $f$), and $\omega_k(f)$ for the number of monic
irreducible $P$ that divide $f$ exactly $k$ times. For monic irreducible $P$ put
$|P| = q^{\deg P}$ and $a_P = |P|^{h-k-1}(|P| - 1)/(|P|^h - 1)$, and let $S_{h,k} = \sum_P a_P$,
the sum over monic irreducible $P$. Then, as $n \to \infty$, the mean of $\omega_k^2$ over
$S_h \cap M_n$ is $S_{h,k}^2 - \sum_P a_P^2 + S_{h,k} + O(q^{n/k - n + \varepsilon n})$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3, Equation (7) (`integers-2025-A9-thm-3`). -/
public theorem_wanted omegaMult_hFree_secondMoment_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h k : ℕ) (hk : 1 < k) (hkh : k < h)
    (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => hFreeMoment F h k 2 n -
        (hFreeOmegaMultSum F h k ^ 2 - hFreeOmegaMultSqSum F h k + hFreeOmegaMultSum F h k))
      =O[atTop] (fun n : ℕ => (Fintype.card F : ℝ) ^ ((n : ℝ) / k - n + ε * n))

/-- **Derivatives at $z = 1$ of uniform approximations.** Let $r > 0$, let $D$ be the open disk of
radius $r$ centred at $1$ in $\mathbb{C}$, and let $f$ and $G_n$ ($n \in \mathbb{N}$) be complex
functions analytic on $D$. Suppose there is a real constant $C$ such that
$|G_n(z) - f(z)\, n^{z-1}| \le C\, n^{\operatorname{Re} z - 2}$ for all $n \ge 1$ and all
$z \in D$. Then for every $k \in \mathbb{N}$ and every $\varepsilon > 0$, as $n \to \infty$,

$$G_n^{(k)}(1) - \frac{d^k}{dz^k}\big(f(z)\, n^{z-1}\big)\Big|_{z=1} = O(n^{\varepsilon - 1}).$$

This is the paper's Lemma 1, a corrected version of Lalín and Zhang's Lemma 3.2; Equation (11) is
the case $k = 1$. The paper's "analytic at $z = 1$" with an error term "in a neighborhood of
$z = 1$" is read as analyticity on a fixed disk on which the bound holds with one constant for all
$n \ge 1$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 1 (`integers-2025-A9-lem-1`). -/
public theorem_wanted iteratedDeriv_sub_isBigO_of_uniform_approx
    (G : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hG : ∀ n, AnalyticOnNhd ℂ (G n) (Metric.ball 1 r))
    (hf : AnalyticOnNhd ℂ f (Metric.ball 1 r))
    (hbound : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Metric.ball (1 : ℂ) r,
      ‖G n z - f z * (n : ℂ) ^ (z - 1)‖ ≤ C * (n : ℝ) ^ (z.re - 2))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => iteratedDeriv k (G n) 1 -
        iteratedDeriv k (fun z => f z * (n : ℂ) ^ (z - 1)) 1)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- **Selberg–Delange theorem for function fields.** Let $q > 1$ and $A > 0$ be real numbers,
and let $B_z(n)$ and $C_z(n)$ be complex numbers, for $z \in \mathbb{C}$ and integers $n \ge 0$,
such that for all $z$ and $n$
$$C_z(n) = \sum_{a=0}^{n} B_z(a)\, q^{n-a} \frac{(z)_{n-a}}{(n-a)!},$$
where $(z)_m = z(z+1)\cdots(z+m-1)$ is the rising factorial. Suppose there is a constant $M$
such that for every complex $z$ with $|z| \le A$ the series
$\sum_{n \ge 0} |B_z(n)| (n+1)^{2A+2} q^{-n}$ converges and its sum is at most $M$. Then there
is a constant $K$ such that for every complex $z$ with $|z| \le A$ and every integer $n \ge 1$,
$$\left| C_z(n) - \frac{q^n n^{z-1}}{\Gamma(z)} \sum_{a \ge 0} \frac{B_z(a)}{q^a} \right|
\le K q^n n^{\operatorname{Re} z - 2}.$$

In terms of the generating functions $B(u, z) = \sum_{n \ge 0} B_z(n) u^n$ and
$C(u, z) = \sum_{n \ge 0} C_z(n) u^n$, and with $Z_q(u) = (1 - qu)^{-1}$, the hypothesis on
$C_z(n)$ says $C(u, z) = B(u, z) Z_q(u)^z$, and the main term is
$q^n n^{z-1} B(1/q, z)/\Gamma(z)$. The paper's $q$ is the size of the field. The weight
$(n+1)^{2A+2}$ replaces the paper's $n^{2A+2}$: equivalent for $n \ge 1$, it also bounds
$B_z(0)$ uniformly, without which the conclusion fails (unbounded $B_z(0)$ along $z \to 2$
with $A = 2$).

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 10 (`integers-2025-A9-thm-10`). -/
public theorem_wanted selbergDelange_functionField
    (q : ℝ) (hq : 1 < q) (A : ℝ) (hA : 0 < A) (B Cz : ℂ → ℕ → ℂ)
    (hC : ∀ z n, Cz z n = ∑ a ∈ Finset.range (n + 1),
      B z a * (q : ℂ) ^ (n - a) * (ascPochhammer ℂ (n - a)).eval z / ((n - a).factorial : ℂ))
    (hB : ∃ M : ℝ, ∀ z : ℂ, ‖z‖ ≤ A →
      Summable (fun n : ℕ => ‖B z n‖ * ((n : ℝ) + 1) ^ (2 * A + 2) / q ^ n) ∧
        ∑' n : ℕ, ‖B z n‖ * ((n : ℝ) + 1) ^ (2 * A + 2) / q ^ n ≤ M) :
    ∃ K : ℝ, ∀ z : ℂ, ‖z‖ ≤ A → ∀ n : ℕ, 1 ≤ n →
      ‖Cz z n - (q : ℂ) ^ n * (n : ℂ) ^ (z - 1) / Complex.Gamma z *
          ∑' a : ℕ, B z a / (q : ℂ) ^ a‖ ≤ K * q ^ n * (n : ℝ) ^ (z.re - 2)

/-- **Selberg–Delange theorem, $h$-th power version.** Let $q > 1$ and $A > 0$ be real numbers,
let $h \ge 1$ be an integer, let $\xi$ be a primitive $h$-th root of unity in $\mathbb{C}$, and
let $B_z(n)$ and $C_z(n)$ be complex numbers, for $z \in \mathbb{C}$ and integers $n \ge 0$,
such that for all $z$ and $n$
$$C_z(n) = \sum_{\substack{0 \le a \le n \\ h \mid n - a}} B_z(a)\, q^{(n-a)/h}
\frac{(z)_{(n-a)/h}}{((n-a)/h)!},$$
where $(z)_m = z(z+1)\cdots(z+m-1)$ is the rising factorial. Suppose there is a constant $M$
such that for every complex $z$ with $|z| \le A$ the series
$\sum_{n \ge 0} |B_z(n)| (n+1)^{2A+2} q^{-n/h}$ converges and its sum is at most $M$. Then there
is a constant $K$ such that for every complex $z$ with $|z| \le A$ and every integer $n \ge 1$,
$$\left| C_z(n) - \frac{q^{n/h} n^{z-1}}{h^z \Gamma(z)} \sum_{j=0}^{h-1} \xi^{jn}
\sum_{a \ge 0} B_z(a) \left(q^{1/h} \xi^j\right)^{-a} \right|
\le K q^{n/h} n^{\operatorname{Re} z - 2}.$$

In terms of the generating functions $B(u, z) = \sum_{n \ge 0} B_z(n) u^n$ and
$C(u, z) = \sum_{n \ge 0} C_z(n) u^n$, and with $Z_q(u) = (1 - qu)^{-1}$, the hypothesis on
$C_z(n)$ says $C(u, z) = B(u, z) Z_q(u^h)^z$, and the inner sums are
$B((q^{1/h} \xi^j)^{-1}, z)$. The paper's $q$ is the size of the field. As in the case $h = 1$,
the weight is $(n+1)^{2A+2}$ rather than $n^{2A+2}$, so that $B_z(0)$ is bounded uniformly.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 11 (`integers-2025-A9-thm-11`). -/
public theorem_wanted selbergDelange_functionField_pow
    (q : ℝ) (hq : 1 < q) (h : ℕ) (hh : 1 ≤ h) (ξ : ℂ) (hξ : IsPrimitiveRoot ξ h)
    (A : ℝ) (hA : 0 < A) (B Cz : ℂ → ℕ → ℂ)
    (hC : ∀ z n, Cz z n = ∑ a ∈ (Finset.range (n + 1)).filter (fun a => h ∣ n - a),
      B z a * (q : ℂ) ^ ((n - a) / h) * (ascPochhammer ℂ ((n - a) / h)).eval z /
        (((n - a) / h).factorial : ℂ))
    (hB : ∃ M : ℝ, ∀ z : ℂ, ‖z‖ ≤ A →
      Summable (fun n : ℕ => ‖B z n‖ * ((n : ℝ) + 1) ^ (2 * A + 2) / q ^ ((n : ℝ) / h)) ∧
        ∑' n : ℕ, ‖B z n‖ * ((n : ℝ) + 1) ^ (2 * A + 2) / q ^ ((n : ℝ) / h) ≤ M) :
    ∃ K : ℝ, ∀ z : ℂ, ‖z‖ ≤ A → ∀ n : ℕ, 1 ≤ n →
      ‖Cz z n - ((q ^ ((n : ℝ) / h) : ℝ) : ℂ) * (n : ℂ) ^ (z - 1) /
          ((h : ℂ) ^ z * Complex.Gamma z) *
          ∑ j ∈ Finset.range h, ξ ^ (j * n) *
            ∑' a : ℕ, B z a * (((q ^ ((1 : ℝ) / h) : ℝ) : ℂ) * ξ ^ j)⁻¹ ^ a‖
        ≤ K * q ^ ((n : ℝ) / h) * (n : ℝ) ^ (z.re - 2)


/-- **Coefficients of $B_{1,S_h}(u, z)$.** Let $F$ be a finite field with $q$ elements, let $h$
be a natural number and let $z$ be a complex number. Let $S_h$ be the set of $h$-free monic
polynomials over $F$ (those divisible by no $P^h$ with $P$ monic irreducible), and $\omega_1(f)$
the number of distinct monic irreducible factors of $f$ of multiplicity exactly $1$. Write
$C_{1,S_h}(u, z) = \sum_{f \in S_h} z^{\omega_1(f)} u^{\deg f}$ and
$B_{1,S_h}(u, z) = Z_q(u)^{-z} C_{1,S_h}(u, z)$, where $Z_q(u)^{-z} = (1 - qu)^z$ is the power
series with coefficient $q^m (-z)_m / m!$ at $u^m$ and $(x)_m = x(x+1) \cdots (x+m-1)$ is the
rising factorial. For a natural number $n$, $B_z(n)$ is the coefficient of $u^n$ in
$B_{1,S_h}(u, z)$, that is,
$$B_z(n) = \sum_{a=0}^{n} \Bigl(\sum_{f \in S_h,\ \deg f = a} z^{\omega_1(f)}\Bigr)
\frac{q^{n-a} (-z)_{n-a}}{(n-a)!}.$$

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 3.1 (definition preceding Lemma 2). -/
public noncomputable def hFreeOmegaOneB (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ Finset.range (n + 1),
    (∑ f ∈ (fixedDegreeMonic F a).filter (· ∈ hFree F h), z ^ omegaMult F 1 f) *
      (Fintype.card F : ℂ) ^ (n - a) * (ascPochhammer ℂ (n - a)).eval (-z) /
        ((n - a).factorial : ℂ)

/-- **Constant coefficient of $B_{1,S_h}$.** Let $F$ be a finite field with $q$ elements and let
$h \ge 1$ be a natural number. Let $S_h$ be the set of $h$-free monic polynomials over $F$ (those
divisible by no $P^h$ with $P$ monic irreducible) and $\omega_1(f)$ the number of distinct monic
irreducible factors of $f$ of multiplicity exactly $1$. For every complex number $z$, the
coefficient $B_z(0)$ of $u^0$ in the formal power series
$$B_{1,S_h}(u, z) = (1 - qu)^z \sum_{f \in S_h} z^{\omega_1(f)} u^{\deg f},$$
where $(1 - qu)^z = \sum_{m \ge 0} \binom{z}{m} (-qu)^m$, equals $1$.

The only monic polynomial of degree $0$ is $1$, which is $h$-free and has $\omega_1(1) = 0$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 3.1 (definition preceding Lemma 2). -/
public theorem hFreeOmegaOneB_zero (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (hh : 0 < h) (z : ℂ) : hFreeOmegaOneB F h z 0 = 1 := by
  simp only [hFreeOmegaOneB, zero_add, Finset.range_one, Finset.sum_singleton, fixedDegreeMonic_zero]
  rw [Finset.filter_singleton]
  simp [one_mem_hFree F h hh, omegaMult_one]

/-- **The coefficients $B_z(n)$ of the $h$-full series.** Let $F$ be a finite field with $q$
elements, let $h$ and $n$ be natural numbers and let $z$ be a complex number. Write $N_h$ for the
set of $h$-full monic polynomials over $F$ (monic $f$ such that $P^h$ divides $f$ for every monic
irreducible $P$ dividing $f$), $\omega_h(f)$ for the number of monic irreducible polynomials that
divide $f$ with multiplicity exactly $h$, and $(x)_m = x(x + 1) \cdots (x + m - 1)$ for the
rising factorial. For $0 \le a \le n$ let $c_a = \sum_f z^{\omega_h(f)}$, the sum over the
$f \in N_h$ of degree $a$. Then $B_z(n)$ is the sum of $c_a \, q^m (-z)_m / m!$ over the $a$ with
$0 \le a \le n$ and $h \mid n - a$, where $m = (n - a)/h$; when $h = 0$ only $a = n$ occurs, with
$m = 0$.

For $h \ge 1$, $B_z(n)$ is the coefficient of $u^n$ in
$B_{h,N_h}(u, z) = (1 - qu^h)^z \sum_{f \in N_h} z^{\omega_h(f)} u^{\deg f}$, since $(1 - qu^h)^z$
has coefficient $q^m (-z)_m / m!$ at $u^{hm}$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 4.1 (definition preceding Lemma 4). -/
public noncomputable def hFullOmegaHB (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range (n + 1)).filter (fun a => h ∣ n - a),
    (∑ f ∈ (fixedDegreeMonic F a).filter (· ∈ hFull F h), z ^ omegaMult F h f) *
      (Fintype.card F : ℂ) ^ ((n - a) / h) * (ascPochhammer ℂ ((n - a) / h)).eval (-z) /
        (((n - a) / h).factorial : ℂ)

/-- **Constant coefficient of $B_{h,N_h}$.** Let $F$ be a finite field with $q$ elements, let $h$
be a natural number and let $z$ be a complex number. Then the coefficient $B_z(0)$ of the
$h$-full series for $F$, $h$ and $z$ equals $1$. For $h \ge 1$, $B_z(0)$ is the constant
coefficient of $B_{h,N_h}(u, z) = (1 - qu^h)^z \sum_{f \in N_h} z^{\omega_h(f)} u^{\deg f}$,
where $N_h$ is the set of $h$-full monic polynomials over $F$ and $\omega_h(f)$ is the number of
monic irreducible polynomials dividing $f$ with multiplicity exactly $h$.

The only monic polynomial of degree $0$ is $1$, which is $h$-full and has $\omega_h(1) = 0$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 4.1 (definition preceding Lemma 4). -/
public theorem hFullOmegaHB_zero (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (z : ℂ) : hFullOmegaHB F h z 0 = 1 := by
  simp only [hFullOmegaHB, zero_add, Finset.range_one, Finset.filter_singleton, Nat.sub_self,
    dvd_zero, ite_true, Finset.sum_singleton, fixedDegreeMonic_zero]
  simp [one_mem_hFull F h, omegaMult_one]

/-- **Weighted coefficient bound for $B_{1,S_h}$.** Let $F$ be a finite field with $q$ elements,
let $h \ge 2$ be a natural number, and let $A$ and $\sigma > 1/2$ be real numbers. Let $S_h$ be
the set of $h$-free monic polynomials over $F$ (those divisible by no $P^h$ with $P$ monic
irreducible) and $\omega_1(f)$ the number of distinct monic irreducible factors of $f$ of
multiplicity exactly $1$. For a complex number $z$ and a natural number $a$ let $B_z(a)$ be the
coefficient of $u^a$ in the formal power series
$$B_{1,S_h}(u, z) = (1 - qu)^z \sum_{f \in S_h} z^{\omega_1(f)} u^{\deg f},$$
where $(1 - qu)^z = \sum_{m \ge 0} \binom{z}{m} (-qu)^m$. Then there is a real constant $c$ such
that for every complex number $z$ with $|z| \le A$ and every natural number $n \ge 2$,
$$\sum_{a=0}^{n} |B_z(a)|\, q^{-\sigma a} \le c.$$

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 2 (`integers-2025-A9-lem-2`). -/
public theorem_wanted hFreeOmegaOneB_weighted_sum_bounded
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (A σ : ℝ)
    (hσ : 1 / 2 < σ) :
    ∃ c : ℝ, ∀ z : ℂ, ‖z‖ ≤ A → ∀ n : ℕ, 2 ≤ n →
      ∑ a ∈ Finset.range (n + 1),
        ‖hFreeOmegaOneB F h z a‖ / (Fintype.card F : ℝ) ^ (σ * a) ≤ c

/-- **Uniform bound for the weighted coefficients of $B_{h,N_h}(u, z)$.** Let $F$ be a finite
field with $q$ elements, let $h \ge 2$ be a natural number, and let $A$ and $\sigma$ be real
numbers with $\sigma > 1/(h + 1)$. Then there is a real constant $c$ such that for every complex
number $z$ with $|z| \le A$ and every natural number $n \ge 2$,
$$\sum_{a=0}^{n} |B_z(a)| \, q^{-\sigma a} \le c,$$
where $B_z(a)$ is the coefficient of $u^a$ in the series $B_{h,N_h}(u, z)$ attached to the
$h$-full polynomials over $F$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 4 (`integers-2025-A9-lem-4`). -/
public theorem_wanted hFullOmegaHB_weighted_sum_bounded
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (A σ : ℝ)
    (hσ : 1 / ((h : ℝ) + 1) < σ) :
    ∃ c : ℝ, ∀ z : ℂ, ‖z‖ ≤ A → ∀ n : ℕ, 2 ≤ n →
      ∑ a ∈ Finset.range (n + 1),
        ‖hFullOmegaHB F h z a‖ / (Fintype.card F : ℝ) ^ (σ * a) ≤ c

/-- **The pole parameter $q^{1/h}\xi^j$.** Let $F$ be a finite set with $q$ elements, and let
$h, j \in \mathbb{N}$ and $\xi \in \mathbb{C}$. The pole parameter is the complex number
$q^{1/h}\xi^j$, where $q^{1/h}$ is the nonnegative real $h$-th root of $q$ (for $h = 0$ the
exponent $1/h$ is read as $0$, so that $q^{1/h} = 1$).

When $F$ is a field, $h \ge 1$ and $\xi$ is a primitive $h$-th root of unity, the inverses
$(q^{1/h}\xi^j)^{-1}$ are the poles $u$ of $Z_q(u^h)$, where $Z_q(u) = 1/(1 - qu)$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 4. -/
public noncomputable def hFullRoot (F : Type*) [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ) : ℂ :=
  (((Fintype.card F : ℝ) ^ ((1 : ℝ) / h) : ℝ) : ℂ) * ξ ^ j

/-- **Formula for the pole parameter.** Let $F$ be a finite set with $q$ elements, and let
$h, j \in \mathbb{N}$ and $\xi \in \mathbb{C}$. The pole parameter $q^{1/h}\xi^j$ equals the
real power $q^{1/h}$, whose exponent is the real number $1/h$ (read as $0$ when $h = 0$), viewed
as a complex number and multiplied by $\xi^j$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 4. -/
public theorem hFullRoot_eq (F : Type*) [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ) :
    hFullRoot F h ξ j = (((Fintype.card F : ℝ) ^ ((1 : ℝ) / h) : ℝ) : ℂ) * ξ ^ j := rfl

/-- **The Euler product $H_{N_h, S_\ell}$ for $h$-full, $\ell$-free polynomials.** Let $F$ be a
finite field, let $h$ and $\ell$ be natural numbers and let $u$ be a complex number. Then
$H_{N_h, S_\ell}(u)$ is the complex number
$$H_{N_h, S_\ell}(u) = \prod_P (1 + \frac{x^{h+1} - x^{\ell} - x^{2h} + x^{h+\ell}}{1 - x}),$$
the product running over all monic irreducible polynomials $P$ over $F$, where $x = u^{\deg P}$
in the factor for $P$ (Equation (53)), the quotient is read as $0$ when $x = 1$, and the product
is taken to be $1$ if it does not converge unconditionally.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 5, Equation (53). -/
public noncomputable def hFullFreeEulerH (F : Type*) [Field F] [Fintype F] (h ℓ : ℕ) (u : ℂ) :
    ℂ :=
  ∏' P : monicIrreducible F,
    (1 + ((u ^ (P : Polynomial F).natDegree) ^ (h + 1) - (u ^ (P : Polynomial F).natDegree) ^ ℓ -
        (u ^ (P : Polynomial F).natDegree) ^ (2 * h) +
        (u ^ (P : Polynomial F).natDegree) ^ (h + ℓ)) / (1 - u ^ (P : Polynomial F).natDegree))

/-- **Unfolding the Euler product $H_{N_h, S_\ell}$.** Let $F$ be a finite field, let $h$ and
$\ell$ be natural numbers and let $u$ be a complex number. Then $H_{N_h, S_\ell}(u)$ equals the
complex product over all monic irreducible polynomials $P$ over $F$
$$\prod_P \Bigl(1 + \frac{x^{h+1} - x^{\ell} - x^{2h} + x^{h+\ell}}{1 - x}\Bigr),$$
where $x = u^{\deg P}$ in the factor for $P$, the quotient is read as $0$ when $x = 1$, and the
product is taken to be $1$ if it does not converge unconditionally.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 5, Equation (53). -/
public theorem hFullFreeEulerH_eq (F : Type*) [Field F] [Fintype F] (h ℓ : ℕ) (u : ℂ) :
    hFullFreeEulerH F h ℓ u = ∏' P : monicIrreducible F,
      (1 + ((u ^ (P : Polynomial F).natDegree) ^ (h + 1) - (u ^ (P : Polynomial F).natDegree) ^ ℓ -
          (u ^ (P : Polynomial F).natDegree) ^ (2 * h) +
          (u ^ (P : Polynomial F).natDegree) ^ (h + ℓ)) /
        (1 - u ^ (P : Polynomial F).natDegree)) := rfl

/-- **Counting $h$-full, $\ell$-free polynomials.** Let $F$ be a finite field with $q$ elements,
let $h$ and $\ell$ be natural numbers with $0 < h < \ell$, let $\xi \in \mathbb{C}$ be a primitive
$h$-th root of unity and let $\varepsilon > 0$. A monic polynomial $f$ over $F$ is $h$-full if
$P^h \mid f$ for every monic irreducible $P$ dividing $f$, and $\ell$-free if $P^\ell \nmid f$ for
every monic irreducible $P$. Write $r_j = q^{1/h} \xi^j$ with $q^{1/h}$ the positive real root,
and let $H(u)$ be the product over all monic irreducible $P$ over $F$ of
$1 + (x^{h+1} - x^\ell - x^{2h} + x^{h+\ell})/(1 - x)$, where $x = u^{\deg P}$. Then there is a
constant $C$ such that for every $n \ge \ell$ the number $N$ of monic polynomials of degree $n$
over $F$ that are $h$-full and $\ell$-free satisfies
$$\Bigl| N - \frac{q^{n/h}}{h} \sum_{j=0}^{h-1} \xi^{jn} H(r_j^{-1}) \Bigr|
\le C q^{n/(h+1) + \varepsilon n}.$$

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 5, Equation (51) (`integers-2025-A9-lem-5`). -/
public theorem_wanted card_hFull_hFree_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h ℓ : ℕ) (hh : 0 < h) (hhℓ : h < ℓ)
    (ξ : ℂ) (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, ℓ ≤ n →
      ‖((((fixedDegreeMonic F n).filter fun f => f ∈ hFull F h ∧ f ∈ hFree F ℓ).card : ℂ)) -
          (((Fintype.card F : ℝ) ^ ((n : ℝ) / h) / h : ℝ) : ℂ) *
            ∑ j ∈ Finset.range h, ξ ^ (j * n) * hFullFreeEulerH F h ℓ (hFullRoot F h ξ j)⁻¹‖ ≤
        C * (Fintype.card F : ℝ) ^ ((n : ℝ) / (h + 1) + ε * n)

/-- **Counting $h$-full, $\ell$-free polynomials coprime to an irreducible.** Let $F$ be a finite
field with $q$ elements, let $h$ and $\ell$ be natural numbers with $0 < h < \ell$, let
$\xi \in \mathbb{C}$ be a primitive $h$-th root of unity, let $P_0$ be a monic irreducible
polynomial over $F$ and let $\varepsilon > 0$. A monic polynomial $f$ over $F$ is $h$-full if
$P^h \mid f$ for every monic irreducible $P$ dividing $f$, and $\ell$-free if $P^\ell \nmid f$ for
every monic irreducible $P$. Write $r_j = q^{1/h} \xi^j$ with $q^{1/h}$ the positive real root,
$y_j = r_j^{-\deg P_0}$, and let $H(u)$ be the product over all monic irreducible $P$ over $F$ of
$1 + (x^{h+1} - x^\ell - x^{2h} + x^{h+\ell})/(1 - x)$, where $x = u^{\deg P}$. Then there is a
constant $C$ (which may depend on $P_0$) such that for every $n \ge \ell$ the number $N$ of monic
polynomials of degree $n$ over $F$ that are $h$-full, $\ell$-free and coprime to $P_0$ satisfies
$$\Bigl| N - \frac{q^{n/h}}{h} \sum_{j=0}^{h-1} \xi^{jn} H(r_j^{-1})
\frac{1 - y_j}{1 - y_j + y_j^h - y_j^\ell} \Bigr| \le C q^{n/(h+1) + \varepsilon n}.$$

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 5, Equation (52) (`integers-2025-A9-lem-5`). -/
public theorem_wanted card_hFull_hFree_coprime_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h ℓ : ℕ) (hh : 0 < h) (hhℓ : h < ℓ)
    (ξ : ℂ) (hξ : IsPrimitiveRoot ξ h) (P₀ : Polynomial F) (hP₀ : P₀ ∈ monicIrreducible F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, ℓ ≤ n →
      ‖((((fixedDegreeMonic F n).filter fun f =>
            f ∈ hFull F h ∧ f ∈ hFree F ℓ ∧ IsCoprime f P₀).card : ℂ)) -
          (((Fintype.card F : ℝ) ^ ((n : ℝ) / h) / h : ℝ) : ℂ) *
            ∑ j ∈ Finset.range h, ξ ^ (j * n) * hFullFreeEulerH F h ℓ (hFullRoot F h ξ j)⁻¹ *
              ((1 - (hFullRoot F h ξ j)⁻¹ ^ P₀.natDegree) /
                (1 - (hFullRoot F h ξ j)⁻¹ ^ P₀.natDegree +
                  ((hFullRoot F h ξ j)⁻¹ ^ P₀.natDegree) ^ h -
                  ((hFullRoot F h ξ j)⁻¹ ^ P₀.natDegree) ^ ℓ))‖ ≤
        C * (Fintype.card F : ℝ) ^ ((n : ℝ) / (h + 1) + ε * n)

/-- **The $j$-th moment of $\omega_k$ over $h$-full polynomials of degree $n$.** Let $F$ be a
finite field and let $h$, $k$, $j$ and $n$ be natural numbers. Let $N_h \cap M_n$ be the finite
set of $h$-full monic polynomials of degree $n$ over $F$ (monic $f$ such that $P^h$ divides $f$
for every monic irreducible $P$ dividing $f$), and let $\omega_k(f)$ be the number of monic
irreducible polynomials that divide $f$ with multiplicity exactly $k$. The moment is the real
number
$$|N_h \cap M_n|^{-1} \sum_{f \in N_h \cap M_n} \omega_k(f)^j,$$
taken to be $0$ when $N_h \cap M_n$ is empty.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 5 and 7. -/
public noncomputable def hFullMoment (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k j n : ℕ) : ℝ :=
  (∑ f ∈ (fixedDegreeMonic F n).filter (· ∈ hFull F h), (omegaMult F k f : ℝ) ^ j) /
    (((fixedDegreeMonic F n).filter (· ∈ hFull F h)).card : ℝ)

/-- **The $h$-full moment is an average of $\omega_k^j$.** Let $F$ be a finite field and let $h$,
$k$, $j$ and $n$ be natural numbers. Let $N_h \cap M_n$ be the finite set of $h$-full monic
polynomials of degree $n$ over $F$ (monic $f$ such that $P^h$ divides $f$ for every monic
irreducible $P$ dividing $f$), and let $\omega_k(f)$ be the number of monic irreducible
polynomials that divide $f$ with multiplicity exactly $k$. Then the $j$-th moment of $\omega_k$
over $N_h \cap M_n$ equals
$$|N_h \cap M_n|^{-1} \sum_{f \in N_h \cap M_n} \omega_k(f)^j,$$
where the quotient is $0$ when $N_h \cap M_n$ is empty. This holds by definition.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 5 and 7. -/
public theorem hFullMoment_eq (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k j n : ℕ) : hFullMoment F h k j n =
      (∑ f ∈ (fixedDegreeMonic F n).filter (· ∈ hFull F h), (omegaMult F k f : ℝ) ^ j) /
        (((fixedDegreeMonic F n).filter (· ∈ hFull F h)).card : ℝ) := rfl

/-- **The local factor $K(P, h, j)$.** Let $F$ be a finite field with $q$ elements, let $h$ and
$j$ be natural numbers, let $\xi$ be a complex number and let $P$ be a polynomial over $F$. Write
$\rho_j = q^{1/h} \xi^j$, where $q^{1/h}$ is the positive real $h$-th root of $q$ (read as $1$
when $h = 0$), and read $\rho_j^{-1}$ as $0$ when $\rho_j = 0$; let $|P| = q^{\deg P}$ if
$P \ne 0$ and $|0| = 0$; and put $y = (\rho_j^{-1})^{\deg P}$, with $\deg 0$ read as $0$. Then
$$K(P, h, j) = \frac{1 - y}{|P|\,(1 - y) + 1},$$
read as $0$ when the denominator vanishes.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 1 (notation preceding Theorem 5). -/
public noncomputable def hFullK (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ)
    (P : Polynomial F) : ℂ :=
  (1 - (hFullRoot F h ξ j)⁻¹ ^ P.natDegree) /
    ((polyNorm F P : ℂ) * (1 - (hFullRoot F h ξ j)⁻¹ ^ P.natDegree) + 1)

/-- **Unfolding the local factor $K(P, h, j)$.** Let $F$ be a finite field with $q$ elements, let
$h$ and $j$ be natural numbers, let $\xi$ be a complex number and let $P$ be a polynomial over $F$.
Write $\rho_j = q^{1/h} \xi^j$, where $q^{1/h}$ is the positive real $h$-th root of $q$ (read as
$1$ when $h = 0$), and read $\rho_j^{-1}$ as $0$ when $\rho_j = 0$; let $|P| = q^{\deg P}$ if
$P \ne 0$ and $|0| = 0$; and put $y = (\rho_j^{-1})^{\deg P}$, with $\deg 0$ read as $0$. Then
$K(P, h, j)$ equals
$$\frac{1 - y}{|P|\,(1 - y) + 1},$$
read as $0$ when the denominator vanishes.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 1 (notation preceding Theorem 5). -/
public theorem hFullK_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ)
    (P : Polynomial F) : hFullK F h ξ j P = (1 - (hFullRoot F h ξ j)⁻¹ ^ P.natDegree) /
      ((polyNorm F P : ℂ) * (1 - (hFullRoot F h ξ j)⁻¹ ^ P.natDegree) + 1) := rfl

/-- **The Euler product $\Pi_j$ for $h$-full polynomials.** Let $F$ be a finite field with $q$
elements, let $h$ and $j$ be natural numbers and let $\xi$ be a complex number. Write
$\rho_j = q^{1/h} \xi^j$, where $q^{1/h}$ is the positive real $h$-th root of $q$ (read as $1$
when $h = 0$), read $\rho_j^{-1}$ as $0$ when $\rho_j = 0$, and write $|P| = q^{\deg P}$ for a
monic irreducible polynomial $P$ over $F$. Then $\Pi_j$ is the complex number
$$\Pi_j = \prod_P (1 - |P|^{-1})\Bigl(1 + \frac{1}{|P|\,(1 - (\rho_j^{-1})^{\deg P})}\Bigr),$$
the product running over all monic irreducible polynomials $P$ over $F$ (Equation (46)), where
$1/0$ is read as $0$, and the product is taken to be $1$ if it does not converge unconditionally.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 1 (asymptotic for `|N_h ∩ M_n|` preceding Theorem 5). -/
public noncomputable def hFullEulerProduct (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ)
    (j : ℕ) : ℂ :=
  ∏' P : monicIrreducible F, (1 - 1 / (polyNorm F P : ℂ)) *
    (1 + 1 / ((polyNorm F P : ℂ) * (1 - (hFullRoot F h ξ j)⁻¹ ^ (P : Polynomial F).natDegree)))

/-- **Unfolding the Euler product $\Pi_j$.** Let $F$ be a finite field with $q$ elements, let $h$
and $j$ be natural numbers and let $\xi$ be a complex number. Write $\rho_j = q^{1/h} \xi^j$, where
$q^{1/h}$ is the positive real $h$-th root of $q$ (read as $1$ when $h = 0$), read $\rho_j^{-1}$
as $0$ when $\rho_j = 0$, and write $|P| = q^{\deg P}$ for a monic irreducible polynomial $P$
over $F$. Then $\Pi_j$ equals the complex product over all monic irreducible polynomials $P$
over $F$
$$\prod_P (1 - |P|^{-1})\Bigl(1 + \frac{1}{|P|\,(1 - (\rho_j^{-1})^{\deg P})}\Bigr),$$
where $1/0$ is read as $0$, and the product is taken to be $1$ if it does not converge
unconditionally.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 1 (asymptotic for `|N_h ∩ M_n|` preceding Theorem 5). -/
public theorem hFullEulerProduct_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ)
    (j : ℕ) : hFullEulerProduct F h ξ j = ∏' P : monicIrreducible F,
      (1 - 1 / (polyNorm F P : ℂ)) *
        (1 + 1 / ((polyNorm F P : ℂ) *
          (1 - (hFullRoot F h ξ j)⁻¹ ^ (P : Polynomial F).natDegree))) := rfl

/-- **The $h$-full weighted mean.** Let $F$ be a finite field with $q$ elements, let
$h, n \in \mathbb{N}$, $\xi \in \mathbb{C}$ and $X : \mathbb{N} \to \mathbb{C}$. Let
$N_h \cap M_n$ be the set of $h$-full monic polynomials of degree $n$ over $F$. For each $j$ let
$\rho_j = q^{1/h}\xi^j$ be the pole parameter and let
$\Pi_j = \prod_P (1 - 1/|P|)(1 + 1/(|P|(1 - \rho_j^{-\deg P})))$, the product over monic
irreducible $P$ with $|P| = q^{\deg P}$, taken to be $1$ when the family is not multipliable.
The $h$-full weighted mean of $X$ is the complex number
$$\frac{q^{n/h}/h}{|N_h \cap M_n|} \sum_{j=0}^{h-1} \xi^{jn} \, \Pi_j \, X_j.$$
Here $q^{n/h}$ is a real power with real exponent $n/h$, and division by zero (including
$0^{-1}$) gives $0$.

It carries every $n$-dependent constant in Theorems 5 and 7.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 5 and 7. -/
public noncomputable def hFullWeightedMean (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (ξ : ℂ) (n : ℕ) (X : ℕ → ℂ) : ℂ :=
  (((Fintype.card F : ℝ) ^ ((n : ℝ) / h) / h : ℝ) : ℂ) /
      (((fixedDegreeMonic F n).filter (· ∈ hFull F h)).card : ℂ) *
    ∑ j ∈ Finset.range h, ξ ^ (j * n) * hFullEulerProduct F h ξ j * X j

/-- **Formula for the $h$-full weighted mean.** Let $F$ be a finite field with $q$ elements, let
$h, n \in \mathbb{N}$, $\xi \in \mathbb{C}$ and $X : \mathbb{N} \to \mathbb{C}$. Let
$N_h \cap M_n$ be the set of $h$-full monic polynomials of degree $n$ over $F$. For each $j$ let
$\rho_j = q^{1/h}\xi^j$ be the pole parameter and let
$\Pi_j = \prod_P (1 - 1/|P|)(1 + 1/(|P|(1 - \rho_j^{-\deg P})))$, the product over monic
irreducible $P$ with $|P| = q^{\deg P}$, taken to be $1$ when the family is not multipliable.
Then the $h$-full weighted mean of $X$ equals
$$\frac{q^{n/h}/h}{|N_h \cap M_n|} \sum_{j=0}^{h-1} \xi^{jn} \, \Pi_j \, X_j.$$
Here $q^{n/h}$ is a real power with real exponent $n/h$, and division by zero (including
$0^{-1}$) gives $0$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 5 and 7. -/
public theorem hFullWeightedMean_eq (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (ξ : ℂ) (n : ℕ) (X : ℕ → ℂ) : hFullWeightedMean F h ξ n X =
      (((Fintype.card F : ℝ) ^ ((n : ℝ) / h) / h : ℝ) : ℂ) /
          (((fixedDegreeMonic F n).filter (· ∈ hFull F h)).card : ℂ) *
        ∑ j ∈ Finset.range h, ξ ^ (j * n) * hFullEulerProduct F h ξ j * X j := rfl

/-- **The constant $\kappa_j$ for $h$-full polynomials.** Let $F$ be a finite field with $q$
elements, let $h$ and $j$ be natural numbers and let $\xi$ be a complex number. Write
$\rho = q^{1/h}\xi^j$, where $q^{1/h}$ is the positive real $h$-th root of $q$ for $h \ge 1$ and
$q^{1/h} = 1$ for $h = 0$, and let $\rho^{-1}$ be read as $0$ when $\rho = 0$. For a monic
irreducible polynomial $P$ over $F$ write $|P| = q^{\deg P}$, $y = (\rho^{-1})^{\deg P}$ and
$K(P, h, j) = (1 - y)/(|P|(1 - y) + 1)$, read as $0$ when the denominator vanishes. Then
$\kappa_j = \sum_P (K(P, h, j) - 1/|P|)$, the sum over all monic irreducible polynomials $P$ over
$F$, taken as an unconditional sum that is $0$ when the family is not summable.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5. -/
public noncomputable def hFullKSum (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ)
    (j : ℕ) : ℂ :=
  ∑' P : monicIrreducible F, (hFullK F h ξ j P - 1 / (polyNorm F P : ℂ))

/-- **The series defining $\kappa_j$.** Let $F$ be a finite field with $q$ elements, let $h$ and
$j$ be natural numbers and let $\xi$ be a complex number. Write $\rho = q^{1/h}\xi^j$, where
$q^{1/h}$ is the positive real $h$-th root of $q$ for $h \ge 1$ and $q^{1/h} = 1$ for $h = 0$, and
let $\rho^{-1}$ be read as $0$ when $\rho = 0$. For a monic irreducible polynomial $P$ over $F$
write $|P| = q^{\deg P}$, $y = (\rho^{-1})^{\deg P}$ and $K(P, h, j) = (1 - y)/(|P|(1 - y) + 1)$,
read as $0$ when the denominator vanishes. Then the constant $\kappa_j$ attached to $F$, $h$, $\xi$
and $j$ equals $\sum_P (K(P, h, j) - 1/|P|)$, the sum over all monic irreducible polynomials $P$
over $F$, taken as an unconditional sum that is $0$ when the family is not summable. This holds
by definition.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5. -/
public theorem hFullKSum_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ) :
    hFullKSum F h ξ j =
      ∑' P : monicIrreducible F, (hFullK F h ξ j P - 1 / (polyNorm F P : ℂ)) := rfl

/-- **The sum $\sum_P K(P, h, j)^2$ over monic irreducible polynomials.** Let $F$ be a finite
field with $q$ elements, let $h$ and $j$ be natural numbers and let $\xi$ be a complex number.
Write $\rho = q^{1/h}\xi^j$, where $q^{1/h}$ is the positive real $h$-th root of $q$ for $h \ge 1$
and $q^{1/h} = 1$ for $h = 0$, and let $\rho^{-1}$ be read as $0$ when $\rho = 0$. For a monic
irreducible polynomial $P$ over $F$ write $|P| = q^{\deg P}$, $y = (\rho^{-1})^{\deg P}$ and
$K(P, h, j) = (1 - y)/(|P|(1 - y) + 1)$, read as $0$ when the denominator vanishes. This defines
the complex number $\sum_P K(P, h, j)^2$, the sum over all monic irreducible polynomials $P$ over
$F$, taken as an unconditional sum that is $0$ when the family is not summable.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5. -/
public noncomputable def hFullKSqSum (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ)
    (j : ℕ) : ℂ :=
  ∑' P : monicIrreducible F, hFullK F h ξ j P ^ 2

/-- **Unfolding the sum of the squares $K(P, h, j)^2$.** Let $F$ be a finite field, let $h$ and
$j$ be natural numbers and let $\xi$ be a complex number. The quantity $\sum_P K(P, h, j)^2$ of
Theorem 5 is the complex sum, over all monic irreducible polynomials $P$ over $F$, of the squares
of the local factors $K(P, h, j)$ attached to $h$, $j$ and $\xi$, taken to be $0$ if it does not
converge absolutely.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5. -/
public theorem hFullKSqSum_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ) :
    hFullKSqSum F h ξ j = ∑' P : monicIrreducible F, hFullK F h ξ j P ^ 2 := rfl

/-- **The $h$-full prime sum $\sum_P b_P$.** Let $F$ be a finite field with $q$ elements, let
$h, k, j \in \mathbb{N}$ and $\xi \in \mathbb{C}$, and let $\rho = q^{1/h}\xi^j$ be the pole
parameter, where $q^{1/h}$ is a real power whose exponent $1/h$ is read as $0$ when $h = 0$.
For a monic irreducible polynomial $P$ over $F$ put $|P| = q^{\deg P}$,
$y_P = \rho^{-\deg P}$, $K(P, h, j) = (1 - y_P)/(|P|(1 - y_P) + 1)$ and
$b_P = |P| \, y_P^{k} \, K(P, h, j)$. The $h$-full prime sum is the complex number
$\sum_P b_P$ over all monic irreducible $P$, taken to be $0$ when the family $(b_P)$ is not
summable. Inverses use the convention $0^{-1} = 0$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7. -/
public noncomputable def hFullOmegaMultSum (F : Type*) [Field F] [Fintype F] (h k : ℕ) (ξ : ℂ)
    (j : ℕ) : ℂ :=
  ∑' P : monicIrreducible F, (polyNorm F P : ℂ) *
    (hFullRoot F h ξ j)⁻¹ ^ (k * (P : Polynomial F).natDegree) * hFullK F h ξ j P

/-- **Formula for the $h$-full prime sum $\sum_P b_P$.** Let $F$ be a finite field with $q$
elements, let $h, k, j \in \mathbb{N}$ and $\xi \in \mathbb{C}$, and let $\rho = q^{1/h}\xi^j$
be the pole parameter, where $q^{1/h}$ is a real power whose exponent $1/h$ is read as $0$
when $h = 0$. For a monic irreducible polynomial $P$ over $F$ put $|P| = q^{\deg P}$,
$K(P, h, j) = (1 - \rho^{-\deg P})/(|P|(1 - \rho^{-\deg P}) + 1)$ and
$b_P = |P| \, (\rho^{-1})^{k \deg P} \, K(P, h, j)$. Then the $h$-full prime sum $\sum_P b_P$
equals the sum of $b_P$ over all monic irreducible polynomials $P$ over $F$, taken to be $0$
when the family is not summable. Inverses use the convention $0^{-1} = 0$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7. -/
public theorem hFullOmegaMultSum_eq (F : Type*) [Field F] [Fintype F] (h k : ℕ) (ξ : ℂ)
    (j : ℕ) : hFullOmegaMultSum F h k ξ j = ∑' P : monicIrreducible F, (polyNorm F P : ℂ) *
      (hFullRoot F h ξ j)⁻¹ ^ (k * (P : Polynomial F).natDegree) * hFullK F h ξ j P := rfl

/-- **The sum $\sum_P b_P^2$ over monic irreducible polynomials.** Let $F$ be a finite field
with $q$ elements, let $h$, $k$ and $j$ be natural numbers and let $\xi$ be a complex number.
Write $\rho = q^{1/h}\xi^j$, where $q^{1/h}$ is the positive real $h$-th root of $q$ for $h \ge 1$
and $q^{1/h} = 1$ for $h = 0$, and let $\rho^{-1}$ be read as $0$ when $\rho = 0$. For a monic
irreducible polynomial $P$ over $F$ write $|P| = q^{\deg P}$, $y = (\rho^{-1})^{\deg P}$,
$K(P, h, j) = (1 - y)/(|P|(1 - y) + 1)$, read as $0$ when the denominator vanishes, and
$b_P = |P| (\rho^{-1})^{k \deg P} K(P, h, j)$. This defines the complex number $\sum_P b_P^2$, the
sum over all monic irreducible polynomials $P$ over $F$, taken as an unconditional sum that is $0$
when the family is not summable.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7. -/
public noncomputable def hFullOmegaMultSqSum (F : Type*) [Field F] [Fintype F] (h k : ℕ)
    (ξ : ℂ) (j : ℕ) : ℂ :=
  ∑' P : monicIrreducible F, ((polyNorm F P : ℂ) *
    (hFullRoot F h ξ j)⁻¹ ^ (k * (P : Polynomial F).natDegree) * hFullK F h ξ j P) ^ 2

/-- **The series defining $\sum_P b_P^2$.** Let $F$ be a finite field with $q$ elements, let $h$,
$k$ and $j$ be natural numbers and let $\xi$ be a complex number. Write $\rho = q^{1/h}\xi^j$,
where $q^{1/h}$ is the positive real $h$-th root of $q$ for $h \ge 1$ and $q^{1/h} = 1$ for
$h = 0$, and let $\rho^{-1}$ be read as $0$ when $\rho = 0$. For a monic irreducible polynomial
$P$ over $F$ write $|P| = q^{\deg P}$, $y = (\rho^{-1})^{\deg P}$ and
$K(P, h, j) = (1 - y)/(|P|(1 - y) + 1)$, read as $0$ when the denominator vanishes. Then the
constant $\sum_P b_P^2$ attached to $F$, $h$, $k$, $\xi$ and $j$ equals
$\sum_P (|P| (\rho^{-1})^{k \deg P} K(P, h, j))^2$, the sum over all monic irreducible
polynomials $P$ over $F$, taken as an unconditional sum that is $0$ when the family is not
summable. This holds by definition.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7. -/
public theorem hFullOmegaMultSqSum_eq (F : Type*) [Field F] [Fintype F] (h k : ℕ) (ξ : ℂ)
    (j : ℕ) : hFullOmegaMultSqSum F h k ξ j = ∑' P : monicIrreducible F, ((polyNorm F P : ℂ) *
      (hFullRoot F h ξ j)⁻¹ ^ (k * (P : Polynomial F).natDegree) * hFullK F h ξ j P) ^ 2 := rfl

/-- **Mean of $\omega_h$ over $h$-full polynomials.** Let $F$ be a finite field with $q$ elements,
let $h \ge 2$, let $\xi \in \mathbb{C}$ be a primitive $h$-th root of unity, and let
$\varepsilon > 0$. Write $N_h \cap M_n$ for the set of monic polynomials $f$ of degree $n$ over $F$
that are $h$-full (if a monic irreducible $P$ divides $f$, then so does $P^h$), and $\omega_h(f)$
for the number of monic irreducible $P$ that divide $f$ exactly $h$ times. For monic irreducible
$P$ and $j < h$ put $|P| = q^{\deg P}$, $y_{P,j} = (q^{1/h}\xi^j)^{-\deg P}$ with $q^{1/h} > 0$,
and $K(P, h, j) = (1 - y_{P,j})/(|P|(1 - y_{P,j}) + 1)$. Let
$\kappa_j = \sum_P (K(P, h, j) - |P|^{-1})$ and
$\Pi_j = \prod_P (1 - |P|^{-1})(1 + |P|^{-1}(1 - y_{P,j})^{-1})$, with sum and product over monic
irreducible $P$, and for $X = (X_j)_j$ put
$W_n(X) = |N_h \cap M_n|^{-1} (q^{n/h}/h) \sum_{j=0}^{h-1} \xi^{jn} \Pi_j X_j$. Let $B_1$ be the
function field Mertens constant and $L_n = \log(n/h)$. Then, as $n \to \infty$, the mean
of $\omega_h$ over $N_h \cap M_n$ is $L_n + B_1 + W_n(\kappa) + O(n^{\varepsilon - 1})$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5, Equation (8) (`integers-2025-A9-thm-5`). -/
public theorem_wanted omegaH_hFull_mean_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (ξ : ℂ)
    (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ((hFullMoment F h h 1 n : ℝ) : ℂ) -
        ((Real.log ((n : ℝ) / h) : ℂ) + (functionFieldMertensConstant F : ℂ) +
          hFullWeightedMean F h ξ n (hFullKSum F h ξ)))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- **Second moment of $\omega_h$ over $h$-full polynomials.** Let $F$ be a finite field with $q$
elements, let $h \ge 2$, let $\xi \in \mathbb{C}$ be a primitive $h$-th root of unity, and let
$\varepsilon > 0$. Write $N_h \cap M_n$ for the set of monic polynomials $f$ of degree $n$ over $F$
that are $h$-full (if a monic irreducible $P$ divides $f$, then so does $P^h$), and $\omega_h(f)$
for the number of monic irreducible $P$ that divide $f$ exactly $h$ times. For monic irreducible
$P$ and $j < h$ put $|P| = q^{\deg P}$, $y_{P,j} = (q^{1/h}\xi^j)^{-\deg P}$ with $q^{1/h} > 0$,
and $K(P, h, j) = (1 - y_{P,j})/(|P|(1 - y_{P,j}) + 1)$. Let
$\kappa_j = \sum_P (K(P, h, j) - |P|^{-1})$ and
$\Pi_j = \prod_P (1 - |P|^{-1})(1 + |P|^{-1}(1 - y_{P,j})^{-1})$, with sum and product over monic
irreducible $P$, and for $X = (X_j)_j$ put
$W_n(X) = |N_h \cap M_n|^{-1} (q^{n/h}/h) \sum_{j=0}^{h-1} \xi^{jn} \Pi_j X_j$. Let $B_1$ be the
function field Mertens constant and $L_n = \log(n/h)$. Then, as $n \to \infty$,
the mean of $\omega_h^2$ over $N_h \cap M_n$ is
$L_n^2 + (2B_1 + 1 + 2W_n(\kappa)) L_n + B_1^2 + B_1 - \pi^2/6 + W_n(X) + O(n^{\varepsilon - 1})$,
where $X_j = -\sum_P K(P, h, j)^2 + \kappa_j^2 + (2B_1 + 1)\kappa_j$.

This follows the paper's proof: the printed constant term $C_3$ has $-W_n(Z)$ in place of
$W_n(X)$, where $Z_j = \sum_P K(P, h, j)^2 + \kappa_j^2 + (2B_1 + 1)\kappa_j$; this contradicts
the final display of the proof (page 29) and the printed variance.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5, Equation (9) (`integers-2025-A9-thm-5`). -/
public theorem_wanted omegaH_hFull_secondMoment_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (ξ : ℂ)
    (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ((hFullMoment F h h 2 n : ℝ) : ℂ) -
        ((Real.log ((n : ℝ) / h) : ℂ) ^ 2 +
          (2 * (functionFieldMertensConstant F : ℂ) + 1 +
            2 * hFullWeightedMean F h ξ n (hFullKSum F h ξ)) * (Real.log ((n : ℝ) / h) : ℂ) +
          ((functionFieldMertensConstant F : ℂ) ^ 2 + (functionFieldMertensConstant F : ℂ) -
              (Real.pi : ℂ) ^ 2 / 6 +
            hFullWeightedMean F h ξ n (fun j => -hFullKSqSum F h ξ j + hFullKSum F h ξ j ^ 2 +
              (2 * (functionFieldMertensConstant F : ℂ) + 1) * hFullKSum F h ξ j))))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- **Variance of $\omega_h$ over $h$-full polynomials.** Let $F$ be a finite field with $q$
elements, let $h \ge 2$, let $\xi \in \mathbb{C}$ be a primitive $h$-th root of unity, and let
$\varepsilon > 0$. Write $N_h \cap M_n$ for the set of monic polynomials $f$ of degree $n$ over $F$
that are $h$-full (if a monic irreducible $P$ divides $f$, then so does $P^h$), and $\omega_h(f)$
for the number of monic irreducible $P$ that divide $f$ exactly $h$ times. For monic irreducible
$P$ and $j < h$ put $|P| = q^{\deg P}$, $y_{P,j} = (q^{1/h}\xi^j)^{-\deg P}$ with $q^{1/h} > 0$,
and $K(P, h, j) = (1 - y_{P,j})/(|P|(1 - y_{P,j}) + 1)$. Let
$\kappa_j = \sum_P (K(P, h, j) - |P|^{-1})$ and
$\Pi_j = \prod_P (1 - |P|^{-1})(1 + |P|^{-1}(1 - y_{P,j})^{-1})$, with sum and product over monic
irreducible $P$, and for $X = (X_j)_j$ put
$W_n(X) = |N_h \cap M_n|^{-1} (q^{n/h}/h) \sum_{j=0}^{h-1} \xi^{jn} \Pi_j X_j$. Let $B_1$ be the
function field Mertens constant and $L_n = \log(n/h)$. Then, as $n \to \infty$,
the variance of $\omega_h$ over $N_h \cap M_n$ (the mean of $\omega_h^2$ minus the square of the
mean of $\omega_h$) is
$L_n + B_1 - \pi^2/6 + W_n(Y) - W_n(\kappa)^2 + O(n^{\varepsilon - 1})$, where
$Y_j = -\sum_P K(P, h, j)^2 + \kappa_j^2 + \kappa_j$.

The printed display writes $\omega_1$ for $\omega_h$ in the definition of the variance and omits
the factor $q^{n/h}/h$ in both weighted sums; both are restored as in Equations (8) and (9), from
which the paper derives the variance.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5 (`integers-2025-A9-thm-5`). -/
public theorem_wanted omegaH_hFull_variance_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (ξ : ℂ)
    (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ((hFullMoment F h h 2 n - hFullMoment F h h 1 n ^ 2 : ℝ) : ℂ) -
        ((Real.log ((n : ℝ) / h) : ℂ) + (functionFieldMertensConstant F : ℂ) -
            (Real.pi : ℂ) ^ 2 / 6 +
          hFullWeightedMean F h ξ n
            (fun j => -hFullKSqSum F h ξ j + hFullKSum F h ξ j ^ 2 + hFullKSum F h ξ j) -
          hFullWeightedMean F h ξ n (hFullKSum F h ξ) ^ 2))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- **Mean of $\omega_k$ over $h$-full polynomials for $k > h$.** Let $F$ be a finite field with
$q$ elements, let $2 \le h < k$, let $\xi \in \mathbb{C}$ be a primitive $h$-th root of unity and
let $\varepsilon > 0$. Write $M_n$ for the set of monic polynomials of degree $n$ over $F$, $N_h$
for the set of $h$-full monic polynomials, $|P| = q^{\deg P}$, and $\omega_k(f)$ for the number of
monic irreducible $P$ dividing $f$ whose multiplicity in $f$ is exactly $k$. For $j < h$ and a
monic irreducible $P$ put $y_{P,j} = (q^{1/h}\xi^j)^{-\deg P}$, where $q^{1/h}$ is the positive
real root, $K(P, h, j) = (1 - y_{P,j})/(|P|(1 - y_{P,j}) + 1)$ and
$b_P(j) = |P| (q^{1/h}\xi^j)^{-k \deg P} K(P, h, j)$, and let
$\Pi_j = \prod_P (1 - 1/|P|)(1 + 1/(|P|(1 - y_{P,j})))$, where sums and products over $P$ run
over the monic irreducible polynomials. For $X = (X_0, \dots, X_{h-1}) \in \mathbb{C}^h$ let
$W_n(X) = |N_h \cap M_n|^{-1} (q^{n/h}/h) \sum_{j<h} \xi^{jn} \Pi_j X_j$. Then the mean of
$\omega_k$ over $N_h \cap M_n$ equals
$W_n\bigl(\sum_P b_P(0), \dots, \sum_P b_P(h-1)\bigr) + O(q^{-n/(h(h+1)) + \varepsilon n})$ as
$n \to \infty$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7 (`integers-2025-A9-thm-7`). -/
public theorem_wanted omegaMult_hFull_mean_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h k : ℕ) (hh : 2 ≤ h) (hhk : h < k)
    (ξ : ℂ) (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ((hFullMoment F h k 1 n : ℝ) : ℂ) -
        hFullWeightedMean F h ξ n (hFullOmegaMultSum F h k ξ))
      =O[atTop] (fun n : ℕ =>
        (Fintype.card F : ℝ) ^ (-((n : ℝ) / (h * (h + 1))) + ε * n))

/-- **Second moment of $\omega_k$ over $h$-full polynomials for $k > h$.** Let $F$ be a finite
field with $q$ elements, let $2 \le h < k$, let $\xi \in \mathbb{C}$ be a primitive $h$-th root of
unity and let $\varepsilon > 0$. Write $M_n$ for the set of monic polynomials of degree $n$ over
$F$, $N_h$ for the set of $h$-full monic polynomials, $|P| = q^{\deg P}$, and $\omega_k(f)$ for the
number of monic irreducible $P$ dividing $f$ whose multiplicity in $f$ is exactly $k$. For $j < h$
and a monic irreducible $P$ put $y_{P,j} = (q^{1/h}\xi^j)^{-\deg P}$, where $q^{1/h}$ is the
positive real root, $K(P, h, j) = (1 - y_{P,j})/(|P|(1 - y_{P,j}) + 1)$ and
$b_P(j) = |P| (q^{1/h}\xi^j)^{-k \deg P} K(P, h, j)$, and let
$\Pi_j = \prod_P (1 - 1/|P|)(1 + 1/(|P|(1 - y_{P,j})))$, where sums and products over $P$ run
over the monic irreducible polynomials. For $X = (X_0, \dots, X_{h-1}) \in \mathbb{C}^h$ let
$W_n(X) = |N_h \cap M_n|^{-1} (q^{n/h}/h) \sum_{j<h} \xi^{jn} \Pi_j X_j$. Then the mean of
$\omega_k^2$ over $N_h \cap M_n$ equals $W_n(X) + O(q^{-n/(h(h+1)) + \varepsilon n})$ as
$n \to \infty$, where $X_j = (\sum_P b_P(j))^2 - \sum_P b_P(j)^2 + \sum_P b_P(j)$.

This is the reading of the paper's proof. The printed statement has
$\sum_P b_P^2 - (\sum_P b_P)^2$ (with $b_P = b_P(j)$) with the signs swapped, contradicting the
computation of the second derivative in $z$ of the paper's generating function $B_{k,N_h}(u, z)$
at the end of the proof (page 31).

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7 (`integers-2025-A9-thm-7`). -/
public theorem_wanted omegaMult_hFull_secondMoment_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h k : ℕ) (hh : 2 ≤ h) (hhk : h < k)
    (ξ : ℂ) (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ((hFullMoment F h k 2 n : ℝ) : ℂ) -
        hFullWeightedMean F h ξ n (fun j => hFullOmegaMultSum F h k ξ j ^ 2 -
          hFullOmegaMultSqSum F h k ξ j + hFullOmegaMultSum F h k ξ j))
      =O[atTop] (fun n : ℕ =>
        (Fintype.card F : ℝ) ^ (-((n : ℝ) / (h * (h + 1))) + ε * n))

end

end MetaMathlibExt
