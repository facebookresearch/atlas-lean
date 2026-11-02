/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius

/-!
# Dirichlet convolutions over `𝔽_q[T]`

Self-contained identities from Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and
Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80:
Perron's formula (Lemma 1), the convolution identities of Lemmas 2-5 and Theorem 6, the Möbius
sums of Lemmas 6 and 7, the bounds of Lemma 8, the Euler-product asymptotics of Propositions 1-3,
the character-sum bound of Proposition 5, the `m = 1` exact sums of Proposition 4, and the
`B_κ`-free divisor-sum asymptotics of Theorems 1-5 (Theorems 2 and 4 for `h ≤ 2`).

Throughout, `F` is a finite field with `q = Fintype.card F` elements, `M` is the set of monic
polynomials, `|f| = q ^ deg f`, `μ` is `UniqueFactorizationMonoid.moebius`, and the primes `P`
of `F[T]` are the monic irreducible polynomials.
-/

open Polynomial UniqueFactorizationMonoid Filter Asymptotics

namespace MetaMathlibExt

@[expose] public section

/-- **Dirichlet convolution over monic divisors.** Let $F$ be a field. The Dirichlet convolution
of functions $\alpha$ and $\beta$ from $F[T]$ to $\mathbb{C}$ is the function $\alpha * \beta$
given at $f \in F[T]$ by
$$(\alpha * \beta)(f) = \sum_{g \text{ monic},\ g \mid f} \alpha(g)\, \beta(f/g),$$
the sum running over the monic divisors $g$ of $f$.

When $f = 0$ every monic polynomial divides $f$; the sum is then the sum of its nonzero terms if
there are finitely many, and $0$ otherwise.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of the
Dirichlet convolution. -/
public noncomputable def monicDirichletConv {F : Type*} [Field F] (α β : F[X] → ℂ)
    (f : F[X]) : ℂ :=
  ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, α g * β (f /ₘ g)

/-- **Dirichlet convolution at $1$.** Let $F$ be a field and let $\alpha$ and $\beta$ be functions
from $F[T]$ to $\mathbb{C}$. Their Dirichlet convolution over monic divisors satisfies
$(\alpha * \beta)(1) = \alpha(1) \beta(1)$, since the only monic divisor of $1$ is $1$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of the
Dirichlet convolution. -/
public theorem monicDirichletConv_one {F : Type*} [Field F] (α β : F[X] → ℂ) :
    monicDirichletConv α β 1 = α 1 * β 1 := by
  have hset : {g : F[X] | g.Monic ∧ g ∣ 1} = {1} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hm, hg⟩
      exact hm.isUnit_iff.mp (isUnit_of_dvd_one hg)
    · rintro rfl
      exact ⟨monic_one, dvd_rfl⟩
  rw [monicDirichletConv, hset, finsum_mem_singleton, divByMonic_one]

/-- **Perron's formula for monic polynomials over a finite field.** Let $F$ be a finite field, let
$a$ be a complex-valued function on $F[T]$, and let $\rho$ be a real number with $0 < \rho < 1$ such
that the series $\sum_f |a(f)| \rho^{\deg f}$ over all monic $f \in F[T]$ converges. Put
$A(u) = \sum_f a(f) u^{\deg f}$, the sum again over all monic $f$. Then for every natural number
$n$, with the circle $|u| = \rho$ traversed counterclockwise,

$$\sum_{f \text{ monic},\ \deg f \le n} a(f) = \frac{1}{2 \pi i} \oint_{|u| = \rho}
\frac{A(u)}{u^n (1 - u)} \, \frac{du}{u}.$$

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 1 (Perron's Formula)
(`integers-2026-A80-lem-1`). -/
public theorem_wanted monic_perron_formula {F : Type*} [Field F] [Finite F]
    (a : F[X] → ℂ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (habs : Summable fun f : {f : F[X] // f.Monic} => ‖a f‖ * ρ ^ (f : F[X]).natDegree)
    (n : ℕ) :
    ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ n}, a f =
      (2 * Real.pi * Complex.I)⁻¹ •
        ∮ u in C(0, ρ),
          (∑' f : {f : F[X] // f.Monic}, a f * u ^ (f : F[X]).natDegree) /
            (u ^ n * (1 - u)) * u⁻¹

/-- **Dirichlet convolution of completely multiplicative functions at a product.** Let $F$ be a
field and let $\alpha, \beta : F[T] \to \mathbb{C}$ be completely multiplicative, that is,
monoid homomorphisms from the multiplicative monoid of $F[T]$ to $\mathbb{C}$. Write
$\gamma = \alpha * \beta$ for their Dirichlet convolution over monic divisors and $\mu$ for the
Möbius function. Then for all monic $f, g \in F[T]$,
$$\gamma(fg) = \sum_{\ell} \mu(\ell) \alpha(\ell) \beta(\ell) \gamma(f/\ell) \gamma(g/\ell),$$
where $\ell$ runs over the monic common divisors of $f$ and $g$.

Every completely multiplicative function on monic polynomials extends to such a homomorphism (send
nonzero constants to $1$ and $0$ to $0$), and only values at monic polynomials enter.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 2
(`integers-2026-A80-lem-2`). -/
public theorem_wanted monicDirichletConv_mul_of_completelyMultiplicative {F : Type*} [Field F]
    (α β : F[X] →* ℂ) {f g : F[X]} (hf : f.Monic) (hg : g.Monic) :
    monicDirichletConv α β (f * g) =
      ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ f ∧ ℓ ∣ g},
        (moebius ℓ : ℂ) * α ℓ * β ℓ * monicDirichletConv α β (f /ₘ ℓ) *
          monicDirichletConv α β (g /ₘ ℓ)

/-- **Möbius sum over the monic divisors of a polynomial over a finite field.** Let $F$ be a finite
field with $q$ elements and let $\mu$ be the Möbius function of $F[T]$. For every monic
$f \in F[T]$,

$$\sum_{g \text{ monic},\ g \mid f} \frac{\mu(g)}{q^{\deg g}} =
\prod_{P \text{ monic irreducible},\ P \mid f} \left(1 - \frac{1}{q^{\deg P}}\right).$$

The right side is $\Phi(f) / q^{\deg f}$, where $\Phi$ is Euler's totient function on $F[T]$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 6
(`integers-2026-A80-lem-6`); `Φ` as defined after Theorem 3. -/
public theorem_wanted monic_sum_moebius_div_norm {F : Type*} [Field F] [Fintype F] {f : F[X]}
    (hf : f.Monic) :
    ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f},
        (moebius g : ℝ) / (Fintype.card F : ℝ) ^ g.natDegree =
      ∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ f},
        (1 - 1 / (Fintype.card F : ℝ) ^ P.natDegree)

/-- **Degree-weighted Möbius sum over the monic divisors of a polynomial over a finite field.** Let
$F$ be a finite field with $q$ elements and let $\mu$ be the Möbius function of $F[T]$. For every
monic $f \in F[T]$,

$$\sum_{g \text{ monic},\ g \mid f} \frac{\mu(g) \deg g}{q^{\deg g}} =
\prod_{P \mid f} \left(1 - \frac{1}{q^{\deg P}}\right)
\sum_{P \mid f} \frac{\deg P}{1 - q^{\deg P}},$$

where in the product and in the sum $P$ runs over the monic irreducible divisors of $f$.

The product is $\Phi(f) / q^{\deg f}$, where $\Phi$ is Euler's totient function on $F[T]$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 7
(`integers-2026-A80-lem-7`); `Φ` as defined after Theorem 3. -/
public theorem_wanted monic_sum_moebius_mul_natDegree_div_norm {F : Type*} [Field F] [Fintype F]
    {f : F[X]} (hf : f.Monic) :
    ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f},
        (moebius g : ℝ) * g.natDegree / (Fintype.card F : ℝ) ^ g.natDegree =
      (∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ f},
          (1 - 1 / (Fintype.card F : ℝ) ^ P.natDegree)) *
        ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ f},
          (P.natDegree : ℝ) / (1 - (Fintype.card F : ℝ) ^ P.natDegree)

/-- **Number of monic polynomials of bounded degree.** Let $F$ be a finite field with $q$
elements and let $N$ be a natural number. The number of monic polynomials in $F[T]$ of degree at
most $N$ is $(q^{N+1} - 1)/(q - 1)$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 4
(`integers-2026-A80-prop-4`), case `h = 1`, `m = 1`. -/
public theorem_wanted monic_count_natDegree_le {F : Type*} [Field F] [Fintype F] (N : ℕ) :
    (Nat.card {f : F[X] // f.Monic ∧ f.natDegree ≤ N} : ℚ) =
      ((Fintype.card F : ℚ) ^ (N + 1) - 1) / (Fintype.card F - 1)

/-- **Summatory divisor function for monic polynomials over a finite field.** Let $F$ be a finite
field with $q$ elements. For monic $f \in F[T]$, the Dirichlet convolution $(1 * 1)(f)$ of the
constant function $1$ with itself is the number of monic divisors of $f$. Then for every natural
number $N$,

$$\sum_{f \text{ monic},\ \deg f \le N} (1 * 1)(f) =
\frac{(N + 1) q^{N + 2} - (N + 2) q^{N + 1} + 1}{(q - 1)^2}.$$

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 4
(`integers-2026-A80-prop-4`), case `h = 2`, `m = 1`. -/
public theorem_wanted monic_sum_divisorCount_natDegree_le {F : Type*} [Field F] [Fintype F]
    (N : ℕ) :
    ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ N},
        monicDirichletConv (fun _ => (1 : ℂ)) (fun _ => 1) f =
      (((N + 1 : ℂ) * (Fintype.card F : ℂ) ^ (N + 2) - (N + 2) * (Fintype.card F : ℂ) ^ (N + 1)
          + 1) / ((Fintype.card F : ℂ) - 1) ^ 2)

/-- **Norm of a polynomial over a finite field.** Let $F$ be a finite field with $q$ elements. The
norm of a nonzero $f \in F[T]$ is the real number $|f| = q^{\deg f}$, and $|0| = 0$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of the
norm. -/
public noncomputable def fqNorm {F : Type*} [Field F] [Fintype F] (f : F[X]) : ℝ :=
  open scoped Classical in
  if f = 0 then 0 else (Fintype.card F : ℝ) ^ f.natDegree

/-- **The norm of a nonzero polynomial.** Let $F$ be a finite field with $q$ elements. For every
nonzero $f \in F[T]$, the norm of $f$ is $|f| = q^{\deg f}$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of the
norm. -/
public theorem fqNorm_of_ne_zero {F : Type*} [Field F] [Fintype F] {f : F[X]} (hf : f ≠ 0) :
    fqNorm f = (Fintype.card F : ℝ) ^ f.natDegree := by
  classical
  simp [fqNorm, hf]

/-- **Multiplicativity of the norm.** Let $F$ be a finite field with $q$ elements, and let
$|f| = q^{\deg f}$ be the norm of a nonzero $f \in F[T]$. For all nonzero $f, g \in F[T]$,
$|fg| = |f| \, |g|$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of the
norm. -/
public theorem fqNorm_mul {F : Type*} [Field F] [Fintype F] {f g : F[X]} (hf : f ≠ 0)
    (hg : g ≠ 0) : fqNorm (f * g) = fqNorm f * fqNorm g := by
  rw [fqNorm_of_ne_zero (mul_ne_zero hf hg), fqNorm_of_ne_zero hf, fqNorm_of_ne_zero hg,
    natDegree_mul hf hg, pow_add]

/-- **Monic polynomials of degree zero.** Let $F$ be a field. A polynomial $f \in F[T]$ is monic
of degree at most $0$ if and only if $f = 1$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 2, the set
`M_{≤ 0}`. -/
public theorem monic_natDegree_le_zero_iff {F : Type*} [Field F] {f : F[X]} :
    f.Monic ∧ f.natDegree ≤ 0 ↔ f = 1 := by
  constructor
  · rintro ⟨hm, hd⟩
    exact eq_one_of_monic_natDegree_zero hm (Nat.le_zero.mp hd)
  · rintro rfl
    exact ⟨monic_one, by simp⟩

/-- **$B_\kappa$-free polynomials.** Let $F$ be a field and let $\kappa$ assign a natural number to
each polynomial in $F[T]$. A polynomial $f \in F[T]$ is $B_\kappa$-free when $P^{\kappa(P)}$ does
not divide $f$ for any monic irreducible $P \in F[T]$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`B_κ`-free polynomials. -/
public def IsBFree {F : Type*} [Field F] (κ : F[X] → ℕ) (f : F[X]) : Prop :=
  ∀ P : F[X], P.Monic → Irreducible P → ¬ P ^ κ P ∣ f

/-- **The polynomial $1$ is $B_\kappa$-free.** Let $F$ be a field and let $\kappa$ assign to each
polynomial in $F[T]$ a natural number, with $\kappa(P) \ne 0$ for every monic irreducible $P$.
Then $1$ is $B_\kappa$-free: $P^{\kappa(P)}$ does not divide $1$ for any monic irreducible $P$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`B_κ`-free polynomials. -/
public theorem isBFree_one {F : Type*} [Field F] (κ : F[X] → ℕ)
    (hκ : ∀ P : F[X], P.Monic → Irreducible P → κ P ≠ 0) : IsBFree κ (1 : F[X]) := by
  intro P hm hP hdvd
  exact hP.not_isUnit ((isUnit_pow_iff (hκ P hm hP)).mp (isUnit_of_dvd_one hdvd))

/-- **The minimal exponent $\kappa_{\min}$.** Let $F$ be a field and let $\kappa$ be a function
from $F[T]$ to the natural numbers. Then $\kappa_{\min}$ is the minimum of $\kappa(P)$ over all
monic irreducible polynomials $P \in F[T]$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`κ_min`. -/
public noncomputable def kappaMin {F : Type*} [Field F] (κ : F[X] → ℕ) : ℕ :=
  ⨅ P : {P : F[X] // P.Monic ∧ Irreducible P}, κ P

/-- **$\kappa_{\min}$ is a lower bound for $\kappa$.** Let $F$ be a field, let $\kappa$ assign a
natural number to each polynomial in $F[T]$, and let $\kappa_{\min}$ be the minimum of $\kappa(P)$
over the monic irreducible $P \in F[T]$. Then $\kappa_{\min} \le \kappa(P)$ for every monic
irreducible $P \in F[T]$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`κ_min`. -/
public theorem kappaMin_le {F : Type*} [Field F] (κ : F[X] → ℕ) {P : F[X]} (hm : P.Monic)
    (hP : Irreducible P) : kappaMin κ ≤ κ P :=
  ciInf_le (OrderBot.bddBelow _) (⟨P, hm, hP⟩ : {P : F[X] // P.Monic ∧ Irreducible P})

/-- **The $\kappa$-power of a polynomial.** Let $F$ be a field and let $\kappa$ be a function
from $F[T]$ to the natural numbers. For nonzero $f \in F[T]$ and a monic irreducible $P$, write
$\nu_P(f)$ for the multiplicity of $P$ in $f$. The $\kappa$-power of $f$ is
$f^\kappa = \prod_P P^{\nu_P(f)\, \kappa(P)}$, the product over the monic irreducible $P$ dividing
$f$; it does not depend on the leading coefficient of $f$. For $f = 0$ the product is empty and
$0^\kappa = 1$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`f ^ κ`. -/
public noncomputable def kappaPow {F : Type*} [Field F] (κ : F[X] → ℕ) (f : F[X]) : F[X] :=
  open scoped Classical in
  ((normalizedFactors f).map fun P => P ^ κ P).prod

/-- **The $\kappa$-power of $1$.** Let $F$ be a field and let $\kappa$ be a function from $F[T]$
to the natural numbers. Then the $\kappa$-power of the constant polynomial $1$ is $1^\kappa = 1$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`f ^ κ`. -/
public theorem kappaPow_one {F : Type*} [Field F] (κ : F[X] → ℕ) :
    kappaPow κ (1 : F[X]) = 1 := by
  classical
  simp [kappaPow]

/-- **The $\kappa$-power of a monic irreducible polynomial.** Let $F$ be a field and let $\kappa$
be a function from $F[T]$ to the natural numbers. For every monic irreducible $P \in F[T]$, the
$\kappa$-power of $P$ is $P^\kappa = P^{\kappa(P)}$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`f ^ κ`. -/
public theorem kappaPow_of_irreducible {F : Type*} [Field F] (κ : F[X] → ℕ) {P : F[X]}
    (hm : P.Monic) (hP : Irreducible P) : kappaPow κ P = P ^ κ P := by
  classical
  simp [kappaPow, normalizedFactors_irreducible hP, hm.normalize_eq_self]

/-- **The $h$-fold divisor function.** Let $F$ be a field and $h$ a natural number. For
$f \in F[T]$, $d_h(f)$ is the number of $h$-tuples $(g_1, \dots, g_h)$ of monic polynomials in
$F[T]$ with $g_1 \cdots g_h = f$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`d_h`. -/
public noncomputable def monicDivisorCount {F : Type*} [Field F] (h : ℕ) (f : F[X]) : ℕ :=
  Nat.card {v : Fin h → F[X] // (∀ i, (v i).Monic) ∧ ∏ i, v i = f}

/-- **The divisor functions at $1$.** Let $F$ be a field and $h$ a natural number. Then
$d_h(1) = 1$, where $d_h(f)$ is the number of $h$-tuples of monic polynomials in $F[T]$ whose
product is $f$: the only such tuple for $f = 1$ has every entry equal to $1$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`d_h`. -/
public theorem monicDivisorCount_one {F : Type*} [Field F] (h : ℕ) :
    monicDivisorCount h (1 : F[X]) = 1 := by
  rw [monicDivisorCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨fun _ => 1, fun _ => monic_one, by simp⟩, ?_⟩
  rintro ⟨v, hv, hprod⟩
  apply Subtype.ext
  funext i
  have hdvd : v i ∣ 1 := hprod ▸ Finset.dvd_prod_of_mem v (Finset.mem_univ i)
  exact (hv i).isUnit_iff.mp (isUnit_of_dvd_one hdvd)

/-- **The divisor function $d_0$ vanishes away from $1$.** Let $F$ be a field and let $f \in F[T]$
with $f \ne 1$. Then $d_0(f) = 0$, where $d_h(f)$ is the number of $h$-tuples of monic
polynomials in $F[T]$ whose product is $f$: the only $0$-tuple is the empty one, whose product
is $1$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`d_h`. -/
public theorem monicDivisorCount_zero_of_ne_one {F : Type*} [Field F] {f : F[X]} (hf : f ≠ 1) :
    monicDivisorCount 0 f = 0 := by
  rw [monicDivisorCount, Nat.card_eq_zero]
  left
  exact ⟨fun ⟨v, _, hv⟩ => hf (by simpa using hv.symm)⟩

/-- **The divisor function $d_1$ on monic polynomials.** Let $F$ be a field. For every monic
$f \in F[T]$, $d_1(f) = 1$, where $d_h(f)$ is the number of $h$-tuples of monic polynomials in
$F[T]$ whose product is $f$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`d_h`. -/
public theorem monicDivisorCount_one_left {F : Type*} [Field F] {f : F[X]} (hf : f.Monic) :
    monicDivisorCount 1 f = 1 := by
  rw [monicDivisorCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨fun _ => f, fun _ => hf, by simp⟩, ?_⟩
  rintro ⟨v, hv, hprod⟩
  apply Subtype.ext
  funext i
  obtain rfl := Subsingleton.elim i 0
  simpa using hprod

/-- **Shifted partial sums of a Dirichlet convolution.** Let $F$ be a field, let
$\alpha, \beta \colon F[T] \to \mathbb{C}$, let $\alpha * \beta$ be their Dirichlet convolution
over monic divisors, let $f \in F[T]$ and let $n$ be a natural number. Then
$S_f[\alpha, \beta](n) = \sum_g (\alpha * \beta)(fg)$, the sum over the monic $g \in F[T]$ with
$\deg f + \deg g \le n$, where $\deg 0 = 0$. This is the paper's sum over $g$ of degree at most
$n - \deg f$.

The sum is a finitary sum: it is $0$ when infinitely many of its terms are nonzero, which can
happen only for infinite $F$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, eq. (3). -/
public noncomputable def monicConvShiftedSum {F : Type*} [Field F] (α β : F[X] → ℂ)
    (f : F[X]) (n : ℕ) : ℂ :=
  ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ f.natDegree + g.natDegree ≤ n}, monicDirichletConv α β (f * g)

/-- **Shifted partial sums vanish below $\deg f$.** Let $F$ be a field, let
$\alpha, \beta \colon F[T] \to \mathbb{C}$ and let $f \in F[T]$. For every natural number
$n < \deg f$, the shifted partial sum of the Dirichlet convolution satisfies
$S_f[\alpha, \beta](n) = 0$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, eq. (3). -/
public theorem monicConvShiftedSum_of_lt {F : Type*} [Field F] (α β : F[X] → ℂ) {f : F[X]}
    {n : ℕ} (hn : n < f.natDegree) : monicConvShiftedSum α β f n = 0 := by
  have hset : {g : F[X] | g.Monic ∧ f.natDegree + g.natDegree ≤ n} = ∅ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro _
    omega
  rw [monicConvShiftedSum, hset, finsum_mem_empty]

/-- **Partial sums of a Dirichlet convolution over monic polynomials.** Let $F$ be a field, let
$\alpha, \beta \colon F[T] \to \mathbb{C}$, and let $\alpha * \beta$ be their Dirichlet
convolution over monic divisors. For an integer $n$,
$D[\alpha, \beta](n) = \sum_g (\alpha * \beta)(g)$, the sum over the monic $g \in F[T]$ of degree
at most $n$. For $n < 0$ the sum is empty, so $D[\alpha, \beta](n) = 0$; this is how the paper's
Lemma 3 uses $D$ at $n - \deg(f \ell)$.

The sum is a finitary sum: it is $0$ when infinitely many of its terms are nonzero, which can
happen only for infinite $F$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[α, β](n)`. -/
public noncomputable def monicConvPartialSum {F : Type*} [Field F] (α β : F[X] → ℂ) (n : ℤ) : ℂ :=
  ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ (g.natDegree : ℤ) ≤ n}, monicDirichletConv α β g

/-- **$D[\alpha, \beta]$ vanishes at negative arguments.** Let $F$ be a field and let
$\alpha, \beta \colon F[T] \to \mathbb{C}$. For every integer $n < 0$, the partial sum of the
Dirichlet convolution of $\alpha$ and $\beta$ satisfies $D[\alpha, \beta](n) = 0$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[α, β](n)`. -/
public theorem monicConvPartialSum_of_neg {F : Type*} [Field F] (α β : F[X] → ℂ) {n : ℤ}
    (hn : n < 0) : monicConvPartialSum α β n = 0 := by
  have hset : {g : F[X] | g.Monic ∧ (g.natDegree : ℤ) ≤ n} = ∅ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro _
    omega
  rw [monicConvPartialSum, hset, finsum_mem_empty]

/-- **The partial sum $D[\alpha, \beta](0)$.** Let $F$ be a field and let
$\alpha, \beta \colon F[T] \to \mathbb{C}$. The partial sum of the Dirichlet convolution of
$\alpha$ and $\beta$ at $0$ is $D[\alpha, \beta](0) = \alpha(1)\, \beta(1)$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[α, β](n)`. -/
public theorem monicConvPartialSum_zero {F : Type*} [Field F] (α β : F[X] → ℂ) :
    monicConvPartialSum α β 0 = α 1 * β 1 := by
  have hset : {g : F[X] | g.Monic ∧ (g.natDegree : ℤ) ≤ 0} = {1} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [← monic_natDegree_le_zero_iff]
    exact and_congr_right fun _ => ⟨fun h => by omega, fun h => by omega⟩
  rw [monicConvPartialSum, hset, finsum_mem_singleton, monicDirichletConv_one]

/-- **Weighted convolution sum.** Let $F$ be a field, let $\gamma, \alpha, \beta$ be functions from
$F[T]$ to $\mathbb{C}$, and write $\alpha * \beta$ for the monic Dirichlet convolution of $\alpha$
and $\beta$. For a natural number $n$, let $M_{\le n}$ be the set of monic polynomials in $F[T]$ of
degree at most $n$. The weighted convolution sum is
$$D(\gamma, \alpha, \beta; n) = \sum_{f \in M_{\le n}} \gamma(f)\,(\alpha * \beta)(f).$$

When $F$ is infinite and this sum has infinitely many nonzero terms, its value is taken to be $0$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[γ, α, β](n)`. -/
public noncomputable def weightedMonicConvSum {F : Type*} [Field F] (γ α β : F[X] → ℂ)
    (n : ℕ) : ℂ :=
  ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ n}, γ f * monicDirichletConv α β f

/-- **The weighted convolution sum at degree zero.** Let $F$ be a field and let
$\gamma, \alpha, \beta$ be functions from $F[T]$ to $\mathbb{C}$, and write $\alpha * \beta$ for
the monic Dirichlet convolution. The weighted convolution sum $D(\gamma, \alpha, \beta; 0)$, the
sum of $\gamma(f)\,(\alpha * \beta)(f)$ over the monic $f \in F[T]$ of degree at most $0$, equals
$\gamma(1)\,\alpha(1)\,\beta(1)$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[γ, α, β](n)`. -/
public theorem weightedMonicConvSum_zero {F : Type*} [Field F] (γ α β : F[X] → ℂ) :
    weightedMonicConvSum γ α β 0 = γ 1 * (α 1 * β 1) := by
  have hset : {f : F[X] | f.Monic ∧ f.natDegree ≤ 0} = {1} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact monic_natDegree_le_zero_iff
  rw [weightedMonicConvSum, hset, finsum_mem_singleton, monicDirichletConv_one]

/-- **Shifted partial sums for completely multiplicative functions.** Let $F$ be a finite field
and let $\alpha, \beta \colon F[T] \to \mathbb{C}$ be completely multiplicative, that is, monoid
homomorphisms from the multiplicative monoid of $F[T]$ to $\mathbb{C}$. Write $\mu$ for the Möbius
function of $F[T]$. For $f \in F[T]$, a natural number $n$ and an integer $k$, write
$S_f[\alpha, \beta](n)$ and $D[\alpha, \beta](k)$ for the shifted partial sums and the partial
sums of the Dirichlet convolution of $\alpha$ and $\beta$ over monic divisors, where
$D[\alpha, \beta](k) = 0$ for $k < 0$. Then for every monic $f \in F[T]$ and every natural number
$n$,
$$S_f[\alpha, \beta](n) = \sum_{d \mid f} \alpha(d)\, \beta(f/d) \sum_{\ell \mid d} \mu(\ell)\,
\beta(\ell)\, D[\alpha, \beta](n - \deg(f \ell)),$$
where $d$ runs over the monic divisors of $f$, $\ell$ over the monic divisors of $d$, and
$n - \deg(f \ell)$ is computed in the integers.

The paper states this for every $f \in F[T]$, monic or not; its proof applies Lemma 2, which needs
$f$ monic.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 3
(`integers-2026-A80-lem-3`). -/
public theorem_wanted monicConvShiftedSum_eq_of_completelyMultiplicative {F : Type*} [Field F]
    [Finite F] (α β : F[X] →* ℂ) {f : F[X]} (hf : f.Monic) (n : ℕ) :
    monicConvShiftedSum α β f n =
      ∑ᶠ d ∈ {d : F[X] | d.Monic ∧ d ∣ f}, α d * β (f /ₘ d) *
        ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ d},
          (moebius ℓ : ℂ) * β ℓ * monicConvPartialSum α β ((n : ℤ) - (f * ℓ).natDegree)

/-- **Weighted convolution sums as sums of shifted sums.** Let $F$ be a finite field and let
$\gamma, \alpha, \beta$ be functions from $F[T]$ to $\mathbb{C}$. Write $\alpha * \beta$ for the
monic Dirichlet convolution, $\mu$ for the Möbius function of $F[T]$, and $\lambda = \gamma * \mu$.
For a natural number $n$ let $M_{\le n}$ be the set of monic polynomials in $F[T]$ of degree at
most $n$, let $D(\gamma, \alpha, \beta; n) = \sum_{f \in M_{\le n}} \gamma(f)\,(\alpha * \beta)(f)$
and, for monic $f$, let
$S_f(\alpha, \beta; n) = \sum_{g \text{ monic},\ \deg f + \deg g \le n} (\alpha * \beta)(fg)$.
Then
$$D(\gamma, \alpha, \beta; n) = \sum_{f \in M_{\le n}} \lambda(f)\, S_f(\alpha, \beta; n).$$

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 4
(`integers-2026-A80-lem-4`). -/
public theorem_wanted weightedMonicConvSum_eq_sum_shifted {F : Type*} [Field F] [Finite F]
    (γ α β : F[X] → ℂ) (n : ℕ) :
    weightedMonicConvSum γ α β n =
      ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ n},
        monicDirichletConv γ (fun g => (moebius g : ℂ)) f * monicConvShiftedSum α β f n

/-- **Camargo's identity over $F[T]$.** Let $F$ be a finite field and let $\mu$ be the Möbius
function of $F[T]$. For functions $\alpha, \beta \colon F[T] \to \mathbb{C}$ let
$(\alpha * \beta)(f) = \sum_{g \mid f} \alpha(g) \beta(f/g)$, over monic divisors $g$, be their
Dirichlet convolution, and let $D[\alpha, \beta](k)$ be the sum of $(\alpha * \beta)(g)$ over the
monic $g$ of degree at most $k$, which is $0$ for $k < 0$. For a further function $\gamma$ let
$D[\gamma, \alpha, \beta](n)$ be the sum of $\gamma(f) (\alpha * \beta)(f)$ over the monic $f$ of
degree at most $n$. Suppose $\alpha$ and $\beta$ are completely multiplicative, that is,
$\alpha(1) = 1$ and $\alpha(f g) = \alpha(f) \alpha(g)$ for all $f, g \in F[T]$, and likewise for
$\beta$, and let $\gamma \colon F[T] \to \mathbb{C}$ be arbitrary. Then for every natural number
$n$,

$$D[\gamma, \alpha, \beta](n) = \sum_{f \text{ monic},\ \deg f \le n} (\gamma * \mu)(f)
\sum_{d \mid f} \alpha(d) \beta(f/d) \sum_{\ell \mid d} \mu(\ell) \beta(\ell) \,
D[\alpha, \beta](n - \deg(f \ell)),$$

where $d$ runs over the monic divisors of $f$ and $\ell$ over the monic divisors of $d$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 6
(`integers-2026-A80-thm-6`). -/
public theorem_wanted weightedMonicConvSum_eq_of_completelyMultiplicative {F : Type*} [Field F]
    [Finite F] (γ : F[X] → ℂ) (α β : F[X] →* ℂ) (n : ℕ) :
    weightedMonicConvSum γ α β n =
      ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ n},
        monicDirichletConv γ (fun g => (moebius g : ℂ)) f *
          ∑ᶠ d ∈ {d : F[X] | d.Monic ∧ d ∣ f}, α d * β (f /ₘ d) *
            ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ d},
              (moebius ℓ : ℂ) * β ℓ * monicConvPartialSum α β ((n : ℤ) - (f * ℓ).natDegree)

/-- **Convolution of the $B_\kappa$-free indicator with the Möbius function.** Let $F$ be a field
and let $\kappa$ assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ne 0$ for
every monic irreducible $P \in F[T]$. Let $\mathbf{1}_{B_\kappa} \colon F[T] \to \mathbb{C}$ be
the indicator function of the $B_\kappa$-free polynomials, let $\mu$ be the Möbius function of
$F[T]$, and write $r^\kappa$ for the $\kappa$-power of a polynomial $r$. Then for every monic
$f \in F[T]$, the Dirichlet convolution of $\mathbf{1}_{B_\kappa}$ and $\mu$ over monic divisors
satisfies
$$(\mathbf{1}_{B_\kappa} * \mu)(f) = \sum_{r} \mu(r),$$
the sum running over the monic $r \in F[T]$ with $r^\kappa = f$.

There is at most one such $r$, so the right side is $\mu(r)$ if $f = r^\kappa$ for a monic $r$,
and $0$ if there is no such $r$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 5
(`integers-2026-A80-lem-5`). -/
public theorem_wanted monicDirichletConv_bFreeIndicator_moebius {F : Type*} [Field F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → κ P ≠ 0) {f : F[X]}
    (hf : f.Monic) :
    monicDirichletConv ({g : F[X] | IsBFree κ g}.indicator 1) (fun g => (moebius g : ℂ)) f =
      ∑ᶠ r ∈ {r : F[X] | r.Monic ∧ kappaPow κ r = f}, (moebius r : ℂ)

/-- **Bound on the Möbius sum over κ-th powers.** Let $F$ be a finite field with $q$ elements and
let $\kappa$ assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for
every monic irreducible $P$. Let $\kappa_{\min}$ be the minimum of $\kappa(P)$ over the monic
irreducible $P$, and for monic $r = \prod_P P^{\nu_P}$ write
$r^\kappa = \prod_P P^{\nu_P \kappa(P)}$. Then for every natural number $N \ge 1$,
$$
\Bigl|\sum_{r} \mu(r) \sum_{f \mid r^\kappa} \sum_{\ell \mid f} \mu(\ell)\Bigr| \le
q^{N/\kappa_{\min}},
$$
where $r$ runs over the monic polynomials with $\deg r^\kappa \le N$, $f$ and $\ell$ run over monic
divisors, $\mu$ is the Möbius function, and the exponent $N/\kappa_{\min}$ is a real number.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 8, eq. (6)
(`integers-2026-A80-lem-8`). -/
public theorem_wanted abs_sum_moebius_kappaPow_le {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {N : ℕ} (hN : 1 ≤ N) :
    |∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N},
        (moebius r : ℝ) * ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r},
          ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ f}, (moebius ℓ : ℝ)| ≤
      (Fintype.card F : ℝ) ^ ((N : ℝ) / kappaMin κ)

/-- **Divisor-count bound over $\kappa$-th powers of monic polynomials.** Let $F$ be a finite
field with $q$ elements and let $\kappa$ assign a natural number to each polynomial in $F[T]$,
with $\kappa(P) \ge 2$ for every monic irreducible $P$. For monic $r = \prod_P P^{\nu_P}$ write
$r^\kappa = \prod_P P^{\nu_P \kappa(P)}$, and let $\kappa_{\min}$ be the minimum of $\kappa(P)$
over the monic irreducible $P$. Then for every $\varepsilon > 0$, as $N \to \infty$,

$$\sum_{r \text{ monic},\ \deg r^\kappa \le N} \ \sum_{f \mid r^\kappa} \ \sum_{\ell \mid f} 1 =
O\left(q^{(1/\kappa_{\min} + \varepsilon) N}\right),$$

where $f$ runs over the monic divisors of $r^\kappa$ and $\ell$ over the monic divisors of $f$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 8, eq. (7)
(`integers-2026-A80-lem-8`). -/
public theorem_wanted sum_divisors_kappaPow_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => ((∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N},
        ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r},
          Nat.card {ℓ : F[X] // ℓ.Monic ∧ ℓ ∣ f} : ℕ) : ℝ)) =O[atTop]
      fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε) * N)

/-- **Euler-product asymptotic with the $(h-1)$-divisor function over $\kappa$-th powers.** Let
$F$ be a finite field with $q$ elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let
$\mu$ be the Möbius function of $F[T]$. Let $\kappa$ assign a natural number to each polynomial in
$F[T]$, with $\kappa(P) \ge 2$ for every monic irreducible $P$. For monic $r = \prod_P P^{\nu_P}$
write $r^\kappa = \prod_P P^{\nu_P \kappa(P)}$, and let $\kappa_{\min}$ be the minimum of
$\kappa(P)$ over the monic irreducible $P$. Let $m \in F[T]$ be monic, let $h \ge 1$, let
$d_{h-1}$ be the $(h-1)$-divisor function, and put $C_P = \binom{h + \kappa(P) - 1}{\kappa(P)}$.
Then for every $\varepsilon > 0$, as $N \to \infty$,

$$\sum_{\substack{r \text{ monic},\ \deg r^\kappa \le N \\ \gcd(r, m) = 1}}
\frac{\mu(r)}{|r^\kappa|} \sum_{f \mid r^\kappa} d_{h-1}(f) \sum_{g \mid f} \frac{\mu(g)}{|g|} =
\prod_{P \nmid m} \left(1 - \frac{1}{|P|^{\kappa(P)}}
\left(C_P + \frac{1}{|P|} (1 - C_P)\right)\right) +
O\left(q^{(1/\kappa_{\min} + \varepsilon - 1)(N + 1)}\right),$$

where $f$ runs over the monic divisors of $r^\kappa$, $g$ over the monic divisors of $f$, and $P$
over the monic irreducible polynomials not dividing $m$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 1
(`integers-2026-A80-prop-1`). -/
public theorem_wanted sum_moebius_kappaPow_divisorCount_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {m : F[X]}
    (hm : m.Monic) {h : ℕ} (hh : 1 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ =>
      (∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N ∧ IsCoprime r m},
          (moebius r : ℝ) / fqNorm (kappaPow κ r) *
            ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r}, (monicDivisorCount (h - 1) f : ℝ) *
              ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, (moebius g : ℝ) / fqNorm g) -
        ∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
          (1 - 1 / fqNorm (P : F[X]) ^ κ P *
            ((Nat.choose (h + κ P - 1) (κ P) : ℝ) +
              1 / fqNorm (P : F[X]) * (1 - (Nat.choose (h + κ P - 1) (κ P) : ℝ))))) =O[atTop]
      fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε - 1) * (N + 1))

/-- **Euler-product asymptotic for a degree-weighted Möbius sum over $\kappa$-th powers.** Let
$F$ be a finite field with $q$ elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let
$\mu$ be the Möbius function of $F[T]$. Let $\kappa$ assign a natural number to each polynomial in
$F[T]$, with $\kappa(P) \ge 2$ for every monic irreducible $P$. For monic $r = \prod_P P^{\nu_P}$
write $r^\kappa = \prod_P P^{\nu_P \kappa(P)}$, and let $\kappa_{\min}$ be the minimum of
$\kappa(P)$ over the monic irreducible $P$. Let $m \in F[T]$ be monic. Then for every
$\varepsilon > 0$, as $N \to \infty$,

$$\sum_{\substack{r \text{ monic},\ \deg r^\kappa \le N \\ \gcd(r, m) = 1}}
\frac{\mu(r)}{|r^\kappa|} \sum_{f \mid r^\kappa} \sum_{g \mid f} \frac{\mu(g) \deg g}{|g|} =
\prod_{P \nmid m} \left(1 - \frac{\kappa(P) + 1}{|P|^{\kappa(P)}} +
\frac{\kappa(P)}{|P|^{\kappa(P) + 1}}\right)
\sum_{P \nmid m} \frac{\kappa(P) \deg P}{|P|^{\kappa(P) + 1} - |P| (\kappa(P) + 1) + \kappa(P)} +
O\left(q^{(1/\kappa_{\min} + \varepsilon - 1)(N + 1)}\right),$$

where $f$ runs over the monic divisors of $r^\kappa$, $g$ over the monic divisors of $f$, and $P$
in the product and in the sum over the monic irreducible polynomials not dividing $m$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 2
(`integers-2026-A80-prop-2`). -/
public theorem_wanted sum_moebius_kappaPow_moebius_natDegree_isBigO {F : Type*} [Field F]
    [Fintype F] (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {m : F[X]}
    (hm : m.Monic) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ =>
      (∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N ∧ IsCoprime r m},
          (moebius r : ℝ) / fqNorm (kappaPow κ r) *
            ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r},
              ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, (moebius g : ℝ) * g.natDegree / fqNorm g) -
        (∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - (κ P + 1 : ℝ) / fqNorm (P : F[X]) ^ κ P +
              (κ P : ℝ) / fqNorm (P : F[X]) ^ (κ P + 1))) *
          ∑' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (κ P : ℝ) * (P : F[X]).natDegree /
              (fqNorm (P : F[X]) ^ (κ P + 1) - fqNorm (P : F[X]) * (κ P + 1) + κ P)) =O[atTop]
      fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε - 1) * (N + 1))

/-- **Euler-product asymptotic for a Möbius sum weighted by $\deg r^\kappa$.** Let $F$ be a finite
field with $q$ elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let $\mu$ be the
Möbius function of $F[T]$. Let $\kappa$ assign a natural number to each polynomial in $F[T]$, with
$\kappa(P) \ge 2$ for every monic irreducible $P$. For monic $r = \prod_P P^{\nu_P}$ write
$r^\kappa = \prod_P P^{\nu_P \kappa(P)}$, and let $\kappa_{\min}$ be the minimum of $\kappa(P)$
over the monic irreducible $P$. Let $m \in F[T]$ be monic. Then for every $\varepsilon > 0$, as
$N \to \infty$,

$$\sum_{\substack{r \text{ monic},\ \deg r^\kappa \le N \\ \gcd(r, m) = 1}}
\frac{\mu(r) \deg r^\kappa}{|r^\kappa|} \sum_{f \mid r^\kappa} \sum_{g \mid f} \frac{\mu(g)}{|g|}
= -\prod_{P \nmid m} \left(1 - \frac{\kappa(P) + 1}{|P|^{\kappa(P)}} +
\frac{\kappa(P)}{|P|^{\kappa(P) + 1}}\right)
\sum_{P \nmid m} \frac{\kappa(P) \deg P \, (|P| (\kappa(P) + 1) - \kappa(P))}
{|P|^{\kappa(P) + 1} - |P| (\kappa(P) + 1) + \kappa(P)} +
O\left(q^{(1/\kappa_{\min} + \varepsilon - 1)(N + 1)}\right),$$

where $f$ runs over the monic divisors of $r^\kappa$, $g$ over the monic divisors of $f$, and $P$
in the product and in the sum over the monic irreducible polynomials not dividing $m$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 3
(`integers-2026-A80-prop-3`). -/
public theorem_wanted sum_moebius_natDegree_kappaPow_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {m : F[X]}
    (hm : m.Monic) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ =>
      (∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N ∧ IsCoprime r m},
          (moebius r : ℝ) * (kappaPow κ r).natDegree / fqNorm (kappaPow κ r) *
            ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r},
              ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, (moebius g : ℝ) / fqNorm g) +
        (∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - (κ P + 1 : ℝ) / fqNorm (P : F[X]) ^ κ P +
              (κ P : ℝ) / fqNorm (P : F[X]) ^ (κ P + 1))) *
          ∑' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (κ P : ℝ) * (P : F[X]).natDegree * (fqNorm (P : F[X]) * (κ P + 1) - κ P) /
              (fqNorm (P : F[X]) ^ (κ P + 1) - fqNorm (P : F[X]) * (κ P + 1) + κ P)) =O[atTop]
      fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε - 1) * (N + 1))

/-- **Character sums of the $h$-divisor function over monic polynomials.** Let $F$ be a finite
field with $q$ elements, let $m \in F[T]$ be monic, and let $\chi$ be a non-principal Dirichlet
character modulo $m$: a multiplicative character of $F[T]/(m)$, vanishing off the units, other
than the principal one, evaluated at $f \in F[T]$ through the class of $f$ modulo $m$. Let
$h \ge 1$ be a natural number and let $d_h$ be the $h$-divisor function, so that $d_h(f)$ is the
number of $h$-tuples of monic polynomials with product $f$. Then for every natural number $N$,

$$\left| \sum_{f \text{ monic},\ \deg f \le N} \chi(f) \, d_h(f) \right| \le
(\sqrt{q} + 1)^{h (\deg m - 1)}.$$

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 5
(`integers-2026-A80-prop-5`); `χ^{(h)}` as in eq. (8). -/
public theorem_wanted norm_sum_mulChar_divisorCount_le {F : Type*} [Field F] [Fintype F]
    {m : F[X]} (hm : m.Monic) (χ : MulChar (F[X] ⧸ Ideal.span {m}) ℂ) (hχ : χ ≠ 1) {h : ℕ}
    (hh : 1 ≤ h) (N : ℕ) :
    ‖∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ N},
        χ (Ideal.Quotient.mk (Ideal.span {m}) f) * (monicDivisorCount h f : ℂ)‖ ≤
      (Real.sqrt (Fintype.card F) + 1) ^ (h * (m.natDegree - 1))

/-- **The $B_\kappa$-free divisor sum.** Let $F$ be a field, let $\kappa$ assign a natural number
to each polynomial in $F[T]$, and let $h$ and $N$ be natural numbers. Then
$\tilde D_{B_\kappa,h}(N)$ is the sum of $d_h(f)$ over the monic $B_\kappa$-free polynomials
$f \in F[T]$ of degree at most $N$, where $d_h(f)$ is the number of $h$-tuples of monic
polynomials with product $f$, and $f$ is $B_\kappa$-free when $P^{\kappa(P)}$ does not divide $f$
for any monic irreducible $P$.

The sum is meant for finite $F$; if it has infinitely many nonzero terms, its value is $0$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`D̃_{B_κ,h}(N)`. -/
public noncomputable def bFreeDivisorSum {F : Type*} [Field F] (κ : F[X] → ℕ) (h N : ℕ) : ℕ :=
  ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ N ∧ IsBFree κ f}, monicDivisorCount h f

/-- **The $B_\kappa$-free divisor sum at degree zero.** Let $F$ be a field and let $\kappa$ assign
to each polynomial in $F[T]$ a natural number, with $\kappa(P) \ne 0$ for every monic irreducible
$P$. Call $f \in F[T]$ $B_\kappa$-free when $P^{\kappa(P)}$ does not divide $f$ for any monic
irreducible $P$, let $d_h(f)$ be the number of $h$-tuples of monic polynomials with product $f$,
and let $\tilde D_{B_\kappa,h}(N)$ be the sum of $d_h(f)$ over the $B_\kappa$-free monic
$f \in F[T]$ of degree at most $N$. Then $\tilde D_{B_\kappa,h}(0) = 1$ for every natural number
$h$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`D̃_{B_κ,h}(N)`. -/
public theorem bFreeDivisorSum_zero {F : Type*} [Field F] (κ : F[X] → ℕ)
    (hκ : ∀ P : F[X], P.Monic → Irreducible P → κ P ≠ 0) (h : ℕ) :
    bFreeDivisorSum κ h 0 = 1 := by
  have hset : {f : F[X] | f.Monic ∧ f.natDegree ≤ 0 ∧ IsBFree κ f} = {1} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hm, hd, -⟩
      exact monic_natDegree_le_zero_iff.mp ⟨hm, hd⟩
    · rintro rfl
      exact ⟨monic_one, by simp, isBFree_one κ hκ⟩
  rw [bFreeDivisorSum, hset, finsum_mem_singleton, monicDivisorCount_one]

/-- **B-free divisor sum in an arithmetic progression.** For a field $F$, a function
$\kappa : F[T] \to \mathbb{N}$, natural numbers $h$ and $N$, and $a, m \in F[T]$, the natural
number $\tilde D_{\kappa,h}(N, a, m)$ is the sum of $d_h(f)$ over the monic $B_\kappa$-free
$f \in F[T]$ of degree at most $N$ with $f \equiv a \pmod m$, that is, with $m$ dividing $f - a$.
Here $d_h(f)$ is the number of $h$-tuples of monic polynomials with product $f$, and $f$ is
$B_\kappa$-free when no $P^{\kappa(P)}$ with $P$ monic irreducible divides it. The sum is finite
when $F$ is finite; it is taken to be $0$ if infinitely many of its terms are nonzero.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`D̃_{B_κ,h}(N, a, m)`. -/
public noncomputable def bFreeDivisorSumMod {F : Type*} [Field F] (κ : F[X] → ℕ) (h N : ℕ)
    (a m : F[X]) : ℕ :=
  ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ N ∧ IsBFree κ f ∧ m ∣ f - a}, monicDivisorCount h f

/-- **The progression sum modulo 1 is the full sum.** Let $F$ be a field, let
$\kappa : F[T] \to \mathbb{N}$, and let $h$ and $N$ be natural numbers. Write
$\tilde D_{\kappa,h}(N)$ for the sum of $d_h(f)$ over the monic $B_\kappa$-free $f \in F[T]$ of
degree at most $N$, and for $a, m \in F[T]$ write $\tilde D_{\kappa,h}(N, a, m)$ for the same sum
restricted to the $f$ with $f \equiv a \pmod m$. Here $d_h(f)$ is the number of $h$-tuples of
monic polynomials with product $f$, $f$ is $B_\kappa$-free when no $P^{\kappa(P)}$ with $P$ monic
irreducible divides it, and a sum with infinitely many nonzero terms is taken to be $0$. Then
for every $a \in F[T]$, $\tilde D_{\kappa,h}(N, a, 1) = \tilde D_{\kappa,h}(N)$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`D̃_{B_κ,h}(N, a, m)`. -/
public theorem bFreeDivisorSumMod_one {F : Type*} [Field F] (κ : F[X] → ℕ) (h N : ℕ)
    (a : F[X]) : bFreeDivisorSumMod κ h N a 1 = bFreeDivisorSum κ h N := by
  simp [bFreeDivisorSumMod, bFreeDivisorSum]

/-- **Asymptotic count of B-free polynomials.** Let $F$ be a finite field with $q$ elements, write
$|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let $\kappa$ assign a natural number to each
polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every monic irreducible $P$; let $\kappa_{\min}$
be the minimum of $\kappa(P)$ over the monic irreducible $P$. Let $\tilde D_{\kappa,1}(N)$ be the
sum of $d_1(f)$ (which is $1$ for monic $f$) over the monic $B_\kappa$-free $f$ of degree at most
$N$, where $f$ is $B_\kappa$-free when no $P^{\kappa(P)}$ with $P$ monic irreducible divides it.
Then for every $\varepsilon > 0$,
$$
\tilde D_{\kappa,1}(N) - \frac{q^N}{1 - 1/q} \prod_P \bigl(1 - |P|^{-\kappa(P)}\bigr) =
O\bigl(q^{(1/\kappa_{\min} + \varepsilon) N}\bigr)
$$
as $N \to \infty$, the product running over the monic irreducible $P$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 1, first formula
(`integers-2026-A80-thm-1`). -/
public theorem_wanted bFreeDivisorSum_one_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => (bFreeDivisorSum κ 1 N : ℝ) -
        (Fintype.card F : ℝ) ^ N / (1 - 1 / (Fintype.card F : ℝ)) *
          ∏' P : {P : F[X] // P.Monic ∧ Irreducible P}, (1 - 1 / fqNorm (P : F[X]) ^ κ P))
      =O[atTop] fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε) * N)

/-- **Asymptotic for the $B_\kappa$-free sum of the divisor function.** Let $F$ be a finite field
with $q$ elements and let $\kappa$ assign to each polynomial in $F[T]$ a natural number, with
$\kappa(P) \ge 2$ for every monic irreducible $P$. A polynomial $f$ is $B_\kappa$-free when
$P^{\kappa(P)}$ does not divide $f$ for any monic irreducible $P$; $d_2(f)$ is the number of
ordered pairs of monic polynomials with product $f$; $\tilde D_{B_\kappa,2}(N)$ is the sum of
$d_2(f)$ over the $B_\kappa$-free monic $f$ of degree at most $N$; $\kappa_{\min}$ is the minimum
of $\kappa(P)$ over the monic irreducible $P$; and for a monic irreducible $P$ we write
$\kappa_P = \kappa(P)$ and $|P| = q^{\deg P}$ for its norm. Then for every $\varepsilon > 0$, as
$N \to \infty$,
$$
\tilde D_{B_\kappa,2}(N) = \frac{q^N}{1 - 1/q}
\prod_P \left( 1 - \frac{\kappa_P + 1}{|P|^{\kappa_P}} + \frac{\kappa_P}{|P|^{\kappa_P + 1}} \right)
\left( N + 1 - \frac{1}{q - 1} +
\sum_P \frac{\kappa_P (\kappa_P + 1) \deg(P) (|P| - 1)}{|P|^{\kappa_P + 1} - |P| (\kappa_P + 1) +
\kappa_P} \right) + O\left( q^{(1/\kappa_{\min} + \varepsilon) N} \right),
$$
where the product and the sum run over the monic irreducible polynomials $P$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 1, second formula
(`integers-2026-A80-thm-1`). -/
public theorem_wanted bFreeDivisorSum_two_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => (bFreeDivisorSum κ 2 N : ℝ) -
        (Fintype.card F : ℝ) ^ N / (1 - 1 / (Fintype.card F : ℝ)) *
          (∏' P : {P : F[X] // P.Monic ∧ Irreducible P},
            (1 - (κ P + 1 : ℝ) / fqNorm (P : F[X]) ^ κ P +
              (κ P : ℝ) / fqNorm (P : F[X]) ^ (κ P + 1))) *
          ((N : ℝ) + 1 - 1 / ((Fintype.card F : ℝ) - 1) +
            ∑' P : {P : F[X] // P.Monic ∧ Irreducible P},
              (κ P : ℝ) * (κ P + 1) * (P : F[X]).natDegree * (fqNorm (P : F[X]) - 1) /
                (fqNorm (P : F[X]) ^ (κ P + 1) - fqNorm (P : F[X]) * (κ P + 1) + κ P)))
      =O[atTop] fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε) * N)

/-- **Asymptotic for B-free divisor sums when h is at most 2.** Let $F$ be a finite field with $q$
elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let $\kappa$ assign a natural
number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every monic irreducible $P$. Let
$h \in \{1, 2\}$ and let $\tilde D_{\kappa,h}(N)$ be the sum of $d_h(f)$ over the monic
$B_\kappa$-free $f$ of degree at most $N$, where $d_h(f)$ is the number of $h$-tuples of monic
polynomials with product $f$, and $f$ is $B_\kappa$-free when no $P^{\kappa(P)}$ with $P$ monic
irreducible divides it. Put $C_P = \binom{h + \kappa(P) - 1}{\kappa(P)}$ and
$$
M(N) = \frac{q^N N^{h-1}}{1 - 1/q}
\prod_P \Bigl(1 - |P|^{-\kappa(P)} \bigl(C_P + |P|^{-1} (1 - C_P)\bigr)\Bigr),
$$
the product running over the monic irreducible $P$. Then
$\tilde D_{\kappa,h}(N) - M(N) = O(M(N)/N)$ as $N \to \infty$.

The paper states this for every $h \ge 1$, but its main term is not correct for $h \ge 3$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 2, cases `h = 1, 2`
(`integers-2026-A80-thm-2`). -/
public theorem_wanted bFreeDivisorSum_isBigO_of_le_two {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {h : ℕ} (hh1 : 1 ≤ h)
    (hh2 : h ≤ 2) :
    (fun N : ℕ => (bFreeDivisorSum κ h N : ℝ) -
        (Fintype.card F : ℝ) ^ N * (N : ℝ) ^ (h - 1) / (1 - 1 / (Fintype.card F : ℝ)) *
          ∏' P : {P : F[X] // P.Monic ∧ Irreducible P},
            (1 - 1 / fqNorm (P : F[X]) ^ κ P *
              ((Nat.choose (h + κ P - 1) (κ P) : ℝ) +
                1 / fqNorm (P : F[X]) * (1 - (Nat.choose (h + κ P - 1) (κ P) : ℝ)))))
      =O[atTop] fun N : ℕ =>
        (Fintype.card F : ℝ) ^ N * (N : ℝ) ^ (h - 1) / (1 - 1 / (Fintype.card F : ℝ)) *
          (∏' P : {P : F[X] // P.Monic ∧ Irreducible P},
            (1 - 1 / fqNorm (P : F[X]) ^ κ P *
              ((Nat.choose (h + κ P - 1) (κ P) : ℝ) +
                1 / fqNorm (P : F[X]) * (1 - (Nat.choose (h + κ P - 1) (κ P) : ℝ))))) / N

/-- **Asymptotic count of B-free polynomials in an arithmetic progression.** Let $F$ be a finite
field with $q$ elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let $\kappa$
assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every monic
irreducible $P$; let $\kappa_{\min}$ be the minimum of $\kappa(P)$ over the monic irreducible $P$.
Let $m \ne 0$ and $a$ be polynomials in $F[T]$ with $a$ coprime to $m$, and let
$\tilde D_{\kappa,1}(N, a, m)$ be the sum of $d_1(f)$ (which is $1$ for monic $f$) over the monic
$B_\kappa$-free $f$ of degree at most $N$ with $f \equiv a \pmod m$, where $f$ is $B_\kappa$-free
when no $P^{\kappa(P)}$ with $P$ monic irreducible divides it. Then for every $\varepsilon > 0$,
$$
\tilde D_{\kappa,1}(N, a, m) -
\frac{q^N}{(1 - 1/q) \, |m|} \prod_{P \nmid m} \bigl(1 - |P|^{-\kappa(P)}\bigr) =
O\bigl(q^{(1/\kappa_{\min} + \varepsilon) N}\bigr)
$$
as $N \to \infty$, the product running over the monic irreducible $P$ not dividing $m$.

The paper's statement does not list the hypothesis $m \ne 0$; it is implicit, since $m$ is the
modulus of a progression.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 3, first formula
(`integers-2026-A80-thm-3`). -/
public theorem_wanted bFreeDivisorSumMod_one_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {a m : F[X]}
    (hm : m ≠ 0) (ham : IsCoprime a m) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => (bFreeDivisorSumMod κ 1 N a m : ℝ) -
        (Fintype.card F : ℝ) ^ N / ((1 - 1 / (Fintype.card F : ℝ)) * fqNorm m) *
          ∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - 1 / fqNorm (P : F[X]) ^ κ P))
      =O[atTop] fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε) * N)

/-- **Asymptotic for the B-free divisor function in an arithmetic progression.** Let $F$ be a
finite field with $q$ elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let
$\kappa$ assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every
monic irreducible $P$; let $\kappa_{\min}$ be the minimum of $\kappa(P)$ over the monic
irreducible $P$. Let $m \ne 0$ and $a$ be polynomials in $F[T]$ with $a$ coprime to $m$, and let
$\tilde D_{\kappa,2}(N, a, m)$ be the sum of $d_2(f)$ over the monic $B_\kappa$-free $f$ of degree
at most $N$ with $f \equiv a \pmod m$, where $d_2(f)$ is the number of pairs of monic polynomials
with product $f$, and $f$ is $B_\kappa$-free when no $P^{\kappa(P)}$ with $P$ monic irreducible
divides it. Writing $\kappa$ for $\kappa(P)$ inside sums and products over $P$, put
$$
M(N) = \frac{q^N}{(1 - 1/q) \, |m|} \prod_{P \mid m} \Bigl(1 - \frac{1}{|P|}\Bigr)
\prod_{P \nmid m} \Bigl(1 - \frac{\kappa + 1}{|P|^{\kappa}} + \frac{\kappa}{|P|^{\kappa + 1}}\Bigr)
\times \Bigl(N + 1 - \frac{1}{q - 1} + 2 \sum_{P \mid m} \frac{\deg P}{|P| - 1} +
\sum_{P \nmid m}
\frac{\kappa (\kappa + 1) \deg P \, (|P| - 1)}{|P|^{\kappa + 1} - |P| (\kappa + 1) + \kappa}\Bigr),
$$
where $P$ runs over the monic irreducible polynomials dividing, respectively not dividing, $m$.
Then for every $\varepsilon > 0$,
$\tilde D_{\kappa,2}(N, a, m) - M(N) = O\bigl(q^{(1/\kappa_{\min} + \varepsilon) N}\bigr)$ as
$N \to \infty$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 3, second formula
(`integers-2026-A80-thm-3`); `Φ` as defined after Theorem 3. -/
public theorem_wanted bFreeDivisorSumMod_two_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {a m : F[X]}
    (hm : m ≠ 0) (ham : IsCoprime a m) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => (bFreeDivisorSumMod κ 2 N a m : ℝ) -
        (Fintype.card F : ℝ) ^ N *
            (∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ m}, (1 - 1 / fqNorm P)) /
            ((1 - 1 / (Fintype.card F : ℝ)) * fqNorm m) *
          (∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - (κ P + 1 : ℝ) / fqNorm (P : F[X]) ^ κ P +
              (κ P : ℝ) / fqNorm (P : F[X]) ^ (κ P + 1))) *
          ((N : ℝ) + 1 - 1 / ((Fintype.card F : ℝ) - 1) +
            2 * (∑ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ m},
              (P.natDegree : ℝ) / (fqNorm P - 1)) +
            ∑' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
              (κ P : ℝ) * (κ P + 1) * (P : F[X]).natDegree * (fqNorm (P : F[X]) - 1) /
                (fqNorm (P : F[X]) ^ (κ P + 1) - fqNorm (P : F[X]) * (κ P + 1) + κ P)))
      =O[atTop] fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε) * N)

/-- **Asymptotic for B-free divisor sums in progressions when h is at most 2.** Let $F$ be a
finite field with $q$ elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let
$\kappa$ assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every
monic irreducible $P$. Let $m \ne 0$ and $a$ be polynomials in $F[T]$ with $a$ coprime to $m$, let
$h \in \{1, 2\}$, and let $\tilde D_{\kappa,h}(N, a, m)$ be the sum of $d_h(f)$ over the monic
$B_\kappa$-free $f$ of degree at most $N$ with $f \equiv a \pmod m$, where $d_h(f)$ is the number
of $h$-tuples of monic polynomials with product $f$, and $f$ is $B_\kappa$-free when no
$P^{\kappa(P)}$ with $P$ monic irreducible divides it. Put
$C_P = \binom{h + \kappa(P) - 1}{\kappa(P)}$ and
$$
M(N) = \frac{q^N N^{h-1}}{(h-1)!} \cdot
\frac{\bigl(\prod_{P \mid m} (1 - 1/|P|)\bigr)^{h-1}}{|m| \, (1 - 1/q)}
\prod_{P \nmid m} \Bigl(1 - |P|^{-\kappa(P)} \bigl(C_P + |P|^{-1} (1 - C_P)\bigr)\Bigr),
$$
the products running over the monic irreducible $P$ dividing, respectively not dividing, $m$.
Then $\tilde D_{\kappa,h}(N, a, m) - M(N) = O(M(N)/N)$ as $N \to \infty$.

The paper states this for every $h \ge 1$, but its main term is not correct for $h \ge 3$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 4, cases `h = 1, 2`
(`integers-2026-A80-thm-4`); `Φ` as defined after Theorem 3. -/
public theorem_wanted bFreeDivisorSumMod_isBigO_of_le_two {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {a m : F[X]}
    (hm : m ≠ 0) (ham : IsCoprime a m) {h : ℕ} (hh1 : 1 ≤ h) (hh2 : h ≤ 2) :
    (fun N : ℕ => (bFreeDivisorSumMod κ h N a m : ℝ) -
        (Fintype.card F : ℝ) ^ N * (N : ℝ) ^ (h - 1) / (h - 1).factorial *
          (∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ m}, (1 - 1 / fqNorm P)) ^ (h - 1) /
          fqNorm m / (1 - 1 / (Fintype.card F : ℝ)) *
          ∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - 1 / fqNorm (P : F[X]) ^ κ P *
              ((Nat.choose (h + κ P - 1) (κ P) : ℝ) +
                1 / fqNorm (P : F[X]) * (1 - (Nat.choose (h + κ P - 1) (κ P) : ℝ)))))
      =O[atTop] fun N : ℕ =>
        (Fintype.card F : ℝ) ^ N * (N : ℝ) ^ (h - 1) / (h - 1).factorial *
          (∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ m}, (1 - 1 / fqNorm P)) ^ (h - 1) /
          fqNorm m / (1 - 1 / (Fintype.card F : ℝ)) *
          (∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - 1 / fqNorm (P : F[X]) ^ κ P *
              ((Nat.choose (h + κ P - 1) (κ P) : ℝ) +
                1 / fqNorm (P : F[X]) * (1 - (Nat.choose (h + κ P - 1) (κ P) : ℝ))))) / N

/-- **Divisor sums over $B_\kappa$-free polynomials in short intervals.** Let $F$ be a finite field
with $q$ elements and let $\kappa$ assign to each polynomial in $F[T]$ a natural number, with
$\kappa(P) \ge 2$ for every monic irreducible $P$. Suppose that $\kappa$ is symmetric:
$\kappa(P^*) = \kappa(P)$ for every monic irreducible $P$ with $P(0) \ne 0$, where $P^*$ is the
monic scalar multiple of $T^{\deg P} P(1/T)$. Let $h \ge 1$ be an integer, let $c$ be a real
number with $c > (h + 2/\kappa_{\min})/(h + 2)$, and let $\varepsilon > 0$. Then there is a constant
$C$ such that for every sufficiently large $N$, every monic $A \in F[T]$ of degree $N$ and every
integer $\Delta$ with $cN \le \Delta \le N - 2$,
$$
\left| \tilde N_{B_\kappa,h}(A, \Delta) - q^{-(N - \Delta - 1)} \left( \tilde D_{B_\kappa,h}(N) -
\tilde D_{B_\kappa,h}(N - 1) \right) \right| \le
C q^{h (N - \Delta)/2 + (1/\kappa_{\min} + \varepsilon) N}.
$$
Here $\tilde N_{B_\kappa,h}(A, \Delta)$ is the sum of $d_h(f)$ over the $B_\kappa$-free
$f \in F[T]$ with $\deg(f - A) \le \Delta$ (where $\deg 0 = -\infty$), $d_h(f)$ is the number of
$h$-tuples of monic polynomials with product $f$, $\tilde D_{B_\kappa,h}(N)$ is the sum of $d_h(f)$
over the $B_\kappa$-free monic $f$ of degree at most $N$, and $\kappa_{\min}$ is the minimum of
$\kappa(P)$ over the monic irreducible $P$.

The paper's $\kappa(P^*)$ leaves $P^*$ unnormalized and undefined for $P = T$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 5, general formula
(`integers-2026-A80-thm-5`). -/
public theorem_wanted bFreeDivisorSum_shortInterval {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P)
    (hsymm : ∀ P : F[X], P.Monic → Irreducible P → P.coeff 0 ≠ 0 →
      κ (normalize P.reverse) = κ P)
    {h : ℕ} (hh : 1 ≤ h) {c : ℝ} (hc : (h + 2 / (kappaMin κ : ℝ)) / (h + 2) < c) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ N in atTop, ∀ A : F[X], A.Monic → A.natDegree = N → ∀ Δ : ℕ,
      c * N ≤ Δ → Δ + 2 ≤ N →
        |(∑ᶠ f ∈ {f : F[X] | (f - A).degree ≤ Δ ∧ IsBFree κ f}, (monicDivisorCount h f : ℝ)) -
            ((bFreeDivisorSum κ h N : ℝ) - bFreeDivisorSum κ h (N - 1)) /
              (Fintype.card F : ℝ) ^ (N - Δ - 1)| ≤
          C * (Fintype.card F : ℝ) ^ (h * ((N : ℝ) - Δ) / 2 + (1 / (kappaMin κ : ℝ) + ε) * N)

/-- **B-free polynomials in short intervals.** Let $F$ be a finite field with $q$ elements, write
$|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let $\kappa$ assign a natural number to each
polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every monic irreducible $P$; let $\kappa_{\min}$
be the minimum of $\kappa(P)$ over the monic irreducible $P$. Assume $\kappa$ is symmetric:
$\kappa(P^*) = \kappa(P)$ for every monic irreducible $P$ with $P(0) \ne 0$, where $P^*$ is the
monic scalar multiple of the reversed polynomial $T^{\deg P} P(1/T)$. Let
$c > (1 + 2/\kappa_{\min})/3$ and $\varepsilon > 0$. Then there is a constant $C$ such that for
all sufficiently large $N$, every monic $A \in F[T]$ of degree $N$ and every natural number
$\Delta$ with $cN \le \Delta \le N - 2$,
$$
\Bigl|\sum_f d_1(f) - q^{\Delta + 1} \prod_P \bigl(1 - |P|^{-\kappa(P)}\bigr)\Bigr| \le
C q^{(N - \Delta)/2 + (1/\kappa_{\min} + \varepsilon) N},
$$
where $f$ runs over the $B_\kappa$-free $f \in F[T]$ with $f = A$ or $\deg(f - A) \le \Delta$,
$d_1(f)$ is $1$ if $f$ is monic and $0$ otherwise, $f$ is $B_\kappa$-free when no $P^{\kappa(P)}$
with $P$ monic irreducible divides it, and $P$ runs over the monic irreducible polynomials.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 5, case `h = 1`
(`integers-2026-A80-thm-5`). -/
public theorem_wanted bFreeDivisorSum_shortInterval_one {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P)
    (hsymm : ∀ P : F[X], P.Monic → Irreducible P → P.coeff 0 ≠ 0 →
      κ (normalize P.reverse) = κ P)
    {c : ℝ} (hc : (1 + 2 / (kappaMin κ : ℝ)) / 3 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ N in atTop, ∀ A : F[X], A.Monic → A.natDegree = N → ∀ Δ : ℕ,
      c * N ≤ Δ → Δ + 2 ≤ N →
        |(∑ᶠ f ∈ {f : F[X] | (f - A).degree ≤ Δ ∧ IsBFree κ f}, (monicDivisorCount 1 f : ℝ)) -
            (Fintype.card F : ℝ) ^ (Δ + 1) *
              ∏' P : {P : F[X] // P.Monic ∧ Irreducible P}, (1 - 1 / fqNorm (P : F[X]) ^ κ P)| ≤
          C * (Fintype.card F : ℝ) ^ (((N : ℝ) - Δ) / 2 + (1 / (kappaMin κ : ℝ) + ε) * N)

/-- **The B-free divisor function in short intervals.** Let $F$ be a finite field with $q$
elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let $\kappa$ assign a natural
number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every monic irreducible $P$; let
$\kappa_{\min}$ be the minimum of $\kappa(P)$ over the monic irreducible $P$. Assume $\kappa$ is
symmetric: $\kappa(P^*) = \kappa(P)$ for every monic irreducible $P$ with $P(0) \ne 0$, where $P^*$
is the monic scalar multiple of the reversed polynomial $T^{\deg P} P(1/T)$. Let
$c > (2 + 2/\kappa_{\min})/4$ and $\varepsilon > 0$. Then there is a constant $C$ such that for
all sufficiently large $N$, every monic $A \in F[T]$ of degree $N$ and every natural number
$\Delta$ with $cN \le \Delta \le N - 2$,
$$
\Bigl|\sum_f d_2(f) - q^{\Delta + 1}
\prod_P \Bigl(1 - \frac{\kappa + 1}{|P|^{\kappa}} + \frac{\kappa}{|P|^{\kappa + 1}}\Bigr)
\Bigl(N + 1 + \sum_P
\frac{\kappa \deg P \, (\kappa + 1) (|P| - 1)}{|P|^{\kappa + 1} - |P| (\kappa + 1) + \kappa}\Bigr)
\Bigr| \le C q^{N - \Delta + (1/\kappa_{\min} + \varepsilon) N},
$$
where $f$ runs over the $B_\kappa$-free $f \in F[T]$ with $f = A$ or $\deg(f - A) \le \Delta$,
$d_2(f)$ is the number of pairs of monic polynomials with product $f$, $f$ is $B_\kappa$-free when
no $P^{\kappa(P)}$ with $P$ monic irreducible divides it, $P$ runs over the monic irreducible
polynomials, and $\kappa$ stands for $\kappa(P)$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 5, case `h = 2`
(`integers-2026-A80-thm-5`). -/
public theorem_wanted bFreeDivisorSum_shortInterval_two {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P)
    (hsymm : ∀ P : F[X], P.Monic → Irreducible P → P.coeff 0 ≠ 0 →
      κ (normalize P.reverse) = κ P)
    {c : ℝ} (hc : (2 + 2 / (kappaMin κ : ℝ)) / 4 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ N in atTop, ∀ A : F[X], A.Monic → A.natDegree = N → ∀ Δ : ℕ,
      c * N ≤ Δ → Δ + 2 ≤ N →
        |(∑ᶠ f ∈ {f : F[X] | (f - A).degree ≤ Δ ∧ IsBFree κ f}, (monicDivisorCount 2 f : ℝ)) -
            (Fintype.card F : ℝ) ^ (Δ + 1) *
              (∏' P : {P : F[X] // P.Monic ∧ Irreducible P},
                (1 - (κ P + 1 : ℝ) / fqNorm (P : F[X]) ^ κ P +
                  (κ P : ℝ) / fqNorm (P : F[X]) ^ (κ P + 1))) *
              ((N : ℝ) + 1 + ∑' P : {P : F[X] // P.Monic ∧ Irreducible P},
                (κ P : ℝ) * (P : F[X]).natDegree * (κ P + 1) * (fqNorm (P : F[X]) - 1) /
                  (fqNorm (P : F[X]) ^ (κ P + 1) - fqNorm (P : F[X]) * (κ P + 1) + κ P))| ≤
          C * (Fintype.card F : ℝ) ^ ((N : ℝ) - Δ + (1 / (kappaMin κ : ℝ) + ε) * N)

end

end MetaMathlibExt
