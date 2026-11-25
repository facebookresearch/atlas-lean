/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.HasLawExists

/-!
# Rademacher random multiplicative functions

This file constructs the classical Rademacher random multiplicative function. Independent
uniform signs are assigned to the primes, extended multiplicatively to squarefree natural
numbers, and set to zero on nonsquarefree inputs.

The arithmetic function is represented by

`μ(n)² ∏_{p ∣ n} Xₚ`,

using pointwise multiplication of arithmetic functions, not Dirichlet convolution. The module
provides the probability law, existence of an independent prime-indexed family, measurability of
the resulting evaluations, and the basic squarefree and multiplicative identities.

## References

* [B. Durkan and A. Pearce-Crump, *A sharp almost sure upper bound for partial sums of random
  multiplicative functions*][durkan2026]
* [R. Zhu and T. Zhang, *Better than square-root cancellation in Piatetski-Shapiro
  sequences*][zhu2026]
* [W. Verreault, *Almost sure upper bound for sums of random multiplicative functions and
  critical chaos*][verreault2026]

[durkan2026]: https://arxiv.org/abs/2607.29429
[zhu2026]: https://arxiv.org/abs/2608.15807
[verreault2026]: https://arxiv.org/abs/2608.21354
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ArithmeticFunction
open scoped ENNReal

namespace MetaMathlibExt.RandomMultiplicativeFunction

/-- **Rademacher measure on the integer units.** The Rademacher measure is the uniform probability
measure on the two integer units $\{-1, 1\}$. -/
noncomputable def rademacherMeasure : Measure ℤˣ :=
  Measure.uniformOfFinset Finset.univ

noncomputable instance instIsProbabilityMeasureRademacherMeasure :
    IsProbabilityMeasure rademacherMeasure := by
  rw [isProbabilityMeasure_iff]
  simp [rademacherMeasure, Measure.uniformOfFinset, ENNReal.inv_two_add_inv_two]

/-- **Each Rademacher sign has probability one half.** For each integer unit $x \in \{-1, 1\}$,
the Rademacher measure of the singleton $\{x\}$ is $1/2$. -/
theorem rademacherMeasure_singleton (x : ℤˣ) :
    rademacherMeasure {x} = (2 : ENNReal)⁻¹ := by
  have hs : MeasurableSet ({x} : Set ℤˣ) := by
    have h_coe : Measurable (fun u : ℤˣ => (u : ℤ)) :=
      measurable_iff_comap_le.2 le_rfl
    have h_eq : ({x} : Set ℤˣ) =
        (fun u : ℤˣ => (u : ℤ)) ⁻¹' ({(x : ℤ)} : Set ℤ) := by
      ext u
      simp [Units.ext_iff]
    rw [h_eq]
    exact h_coe (measurableSet_singleton _)
  rw [rademacherMeasure, Measure.uniformOfFinset, Measure.finsetSum_apply]
  simp_rw [Measure.smul_apply, Measure.dirac_apply' _ hs]
  rcases Int.units_eq_one_or x with rfl | rfl <;> simp [Set.indicator]

/-- **Rademacher family.** Let $\mu$ be a measure on a measurable space $\Omega$. A family
$(X_p)$, indexed by the primes $p$, of maps $X_p \colon \Omega \to \{-1, 1\}$ into the units of
$\mathbb{Z}$ is a Rademacher family for $\mu$ when every $X_p$ is measurable, every $X_p$ has
law the Rademacher measure (the uniform measure on $\{-1, 1\}$) under $\mu$, and the family
is mutually independent under $\mu$. -/
def IsRademacherFamily {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Nat.Primes → Ω → ℤˣ) : Prop :=
  (∀ p, Measurable (X p)) ∧ (∀ p, HasLaw (X p) rademacherMeasure μ) ∧ iIndepFun X μ

/-- **Existence of a Rademacher family.** There exist a measurable space $\Omega$, a probability
measure $\mu$ on $\Omega$ and a family $(X_p)$, indexed by the primes $p$, of maps
$X_p \colon \Omega \to \{-1, 1\}$ into the units of $\mathbb{Z}$ that is a Rademacher family
for $\mu$. -/
theorem exists_rademacherFamily :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : Nat.Primes → Ω → ℤˣ),
      IsRademacherFamily μ X ∧ IsProbabilityMeasure μ := by
  obtain ⟨Ω, hM, μ, X, hMeas, hLaw, hIndep, hProb⟩ :=
    exists_iid Nat.Primes rademacherMeasure
  exact ⟨Ω, hM, μ, X, ⟨hMeas, hLaw, hIndep⟩, hProb⟩

/-- **Prime sign of a natural number.** Let $X = (X_p)$ be a family, indexed by the primes $p$,
of maps $X_p \colon \Omega \to \{-1, 1\}$ into the units of $\mathbb{Z}$. For a natural number
$n$ and $\omega \in \Omega$, the prime sign of $n$ at $\omega$ is the integer $X_n(\omega)$ if
$n$ is prime and $1$ otherwise. -/
def primeSignNat {Ω : Type*} (X : Nat.Primes → Ω → ℤˣ) (n : ℕ) (ω : Ω) : ℤ :=
  if h : Nat.Prime n then (X ⟨n, h⟩ ω : ℤ) else 1

@[simp]
theorem primeSignNat_prime {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ}
    {p : ℕ} {ω : Ω} (hp : Nat.Prime p) :
    primeSignNat X p ω = (X ⟨p, hp⟩ ω : ℤ) := by
  simp [primeSignNat, hp]

@[simp]
theorem primeSignNat_not_prime {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ}
    {n : ℕ} {ω : Ω} (hn : ¬Nat.Prime n) :
    primeSignNat X n ω = 1 := by
  simp [primeSignNat, hn]

/-- **Measurability of the prime signs.** Let $(X_p)$ be a Rademacher family for a measure
$\mu$ on a measurable space $\Omega$. For every natural number $n$, the map
$\omega \mapsto \varepsilon_n(\omega)$ from $\Omega$ to $\mathbb{Z}$ is measurable, where the
prime sign $\varepsilon_n(\omega)$ is $X_n(\omega)$ if $n$ is prime and $1$ otherwise. -/
theorem IsRademacherFamily.measurable_primeSignNat {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Nat.Primes → Ω → ℤˣ} (hX : IsRademacherFamily μ X) (n : ℕ) :
    Measurable (primeSignNat X n) := by
  by_cases hn : Nat.Prime n
  · have h_coe : Measurable (fun u : ℤˣ => (u : ℤ)) :=
      measurable_iff_comap_le.2 le_rfl
    have h_eq : primeSignNat X n = fun ω => (X ⟨n, hn⟩ ω : ℤ) := by
      funext ω
      exact primeSignNat_prime hn
    rw [h_eq]
    exact h_coe.comp (hX.1 ⟨n, hn⟩)
  · have h_eq : primeSignNat X n = fun _ => 1 := by
      funext ω
      exact primeSignNat_not_prime hn
    rw [h_eq]
    exact measurable_const

/-- **Rademacher random multiplicative function.** Let $(X_p)_p$ be a family of maps
$X_p : \Omega \to \{-1, 1\}$ indexed by the primes, and let $\omega \in \Omega$. The Rademacher
random multiplicative function at $\omega$ is the arithmetic function
$f : \mathbb{N} \to \mathbb{Z}$ with $f(0) = 0$ and

$$f(n) = \mu(n)^2 \prod_{p \mid n} X_p(\omega)$$

for $n \ge 1$, where $\mu$ is the Möbius function and the product runs over the distinct primes
$p$ dividing $n$. -/
noncomputable def rademacherFunction {Ω : Type*} (X : Nat.Primes → Ω → ℤˣ) (ω : Ω) :
    ArithmeticFunction ℤ :=
  (moebius.pmul moebius).pmul (prodPrimeFactors fun p => primeSignNat X p ω)

/-- **Formula for the Rademacher random multiplicative function.** Let $X = (X_p)$ be a family,
indexed by the primes $p$, of maps $X_p \colon \Omega \to \{-1, 1\}$, let $\omega \in \Omega$,
and let $f$ be the Rademacher random multiplicative function of $X$ at $\omega$. For every
natural number $n \neq 0$, $f(n) = \mu(n)^2 \prod_{p \mid n} \varepsilon_p(\omega)$, where
$\mu$ is the Möbius function, the product runs over the distinct primes $p$ dividing $n$, and
$\varepsilon_p(\omega)$ is the prime sign of $p$ at $\omega$. -/
theorem rademacherFunction_apply {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ} {ω : Ω}
    {n : ℕ} (hn : n ≠ 0) :
    rademacherFunction X ω n =
      ((moebius n : ℤ) ^ 2) * ∏ p ∈ n.primeFactors, primeSignNat X p ω := by
  simp [rademacherFunction, pmul_apply, prodPrimeFactors_apply hn, pow_two]

@[simp]
theorem rademacherFunction_one {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ} {ω : Ω} :
    rademacherFunction X ω 1 = 1 := by
  have h1 : (1 : ℕ) ≠ 0 := by decide
  simp [rademacherFunction_apply h1]

/-- **The Rademacher random multiplicative function on squarefree numbers.** Let $X = (X_p)$ be
a family, indexed by the primes $p$, of maps $X_p \colon \Omega \to \{-1, 1\}$, let
$\omega \in \Omega$, and let $f$ be the Rademacher random multiplicative function of $X$ at
$\omega$. For every squarefree natural number $n$,
$f(n) = \prod_{p \mid n} \varepsilon_p(\omega)$, the product of the prime signs
$\varepsilon_p(\omega)$ at $\omega$ over the distinct primes $p$ dividing $n$. -/
theorem rademacherFunction_eq_prod_of_squarefree {Ω : Type*}
    {X : Nat.Primes → Ω → ℤˣ} {ω : Ω} {n : ℕ} (hn : Squarefree n) :
    rademacherFunction X ω n = ∏ p ∈ n.primeFactors, primeSignNat X p ω := by
  rw [rademacherFunction_apply hn.ne_zero, moebius_sq_eq_one_of_squarefree hn, one_mul]

/-- **The Rademacher random multiplicative function vanishes off squarefree numbers.** Let
$X = (X_p)$ be a family, indexed by the primes $p$, of maps $X_p \colon \Omega \to \{-1, 1\}$,
let $\omega \in \Omega$, and let $f$ be the Rademacher random multiplicative function of $X$ at
$\omega$. Then $f(n) = 0$ for every natural number $n$ that is not squarefree, including
$n = 0$. -/
theorem rademacherFunction_eq_zero_of_not_squarefree {Ω : Type*}
    {X : Nat.Primes → Ω → ℤˣ} {ω : Ω} {n : ℕ} (hn : ¬Squarefree n) :
    rademacherFunction X ω n = 0 := by
  by_cases hn0 : n = 0
  · simp [hn0]
  · simp [rademacherFunction_apply hn0, moebius_eq_zero_of_not_squarefree hn]

/-- **The Rademacher random multiplicative function is multiplicative.** Let $X = (X_p)$ be a
family, indexed by the primes $p$, of maps $X_p \colon \Omega \to \{-1, 1\}$, and let
$\omega \in \Omega$. The Rademacher random multiplicative function $f$ of $X$ at $\omega$
satisfies $f(1) = 1$ and $f(mn) = f(m) f(n)$ for all coprime natural numbers $m$ and $n$. -/
theorem isMultiplicative_rademacherFunction {Ω : Type*}
    {X : Nat.Primes → Ω → ℤˣ} {ω : Ω} :
    IsMultiplicative (rademacherFunction X ω) :=
  (isMultiplicative_moebius.pmul isMultiplicative_moebius).pmul
    (IsMultiplicative.prodPrimeFactors _)

/-- **Value of the Rademacher function at a prime.** Let $(X_p)_p$ be a family of maps
$X_p : \Omega \to \{-1, 1\}$ indexed by the primes, let $\omega \in \Omega$, and let $f$ be the
associated Rademacher random multiplicative function at $\omega$. For every prime $p$, the value
$f(p)$ is the sign assigned to $p$, that is, $f(p) = X_p(\omega)$. -/
@[simp]
theorem rademacherFunction_prime {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ} {ω : Ω}
    {p : ℕ} (hp : Nat.Prime p) :
    rademacherFunction X ω p = primeSignNat X p ω := by
  have hpf : p.primeFactors = {p} := by
    simpa using Nat.primeFactors_prime_pow (p := p) (k := 1) (by decide) hp
  rw [rademacherFunction_eq_prod_of_squarefree hp.squarefree, hpf, Finset.prod_singleton]

/-- **The Rademacher random multiplicative function vanishes at prime squares.** Let
$X = (X_p)$ be a family, indexed by the primes $p$, of maps $X_p \colon \Omega \to \{-1, 1\}$,
let $\omega \in \Omega$, and let $f$ be the Rademacher random multiplicative function of $X$ at
$\omega$. Then $f(p^2) = 0$ for every prime $p$. -/
@[simp]
theorem rademacherFunction_prime_sq {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ} {ω : Ω}
    {p : ℕ} (hp : Nat.Prime p) :
    rademacherFunction X ω (p ^ 2) = 0 := by
  apply rademacherFunction_eq_zero_of_not_squarefree
  rw [Nat.squarefree_pow_iff hp.ne_one (by decide : 2 ≠ 0)]
  simp

/-- **Measurability of the Rademacher random multiplicative function.** Let $(X_p)$ be a
Rademacher family for a measure $\mu$ on a measurable space $\Omega$, and for $\omega \in \Omega$
let $f_\omega$ be the Rademacher random multiplicative function of $(X_p)$ at $\omega$. For
every natural number $n$, the map $\omega \mapsto f_\omega(n)$ from $\Omega$ to $\mathbb{Z}$ is
measurable. -/
theorem IsRademacherFamily.measurable_rademacherFunction {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Nat.Primes → Ω → ℤˣ} (hX : IsRademacherFamily μ X) (n : ℕ) :
    Measurable (fun ω => rademacherFunction X ω n) := by
  by_cases hn : n = 0
  · subst n
    have h_eq : (fun ω => rademacherFunction X ω 0) = fun _ => (0 : ℤ) := by
      funext ω
      simp
    rw [h_eq]
    exact measurable_const
  · have hprod : Measurable (fun ω => ∏ p ∈ n.primeFactors, primeSignNat X p ω) :=
      Finset.measurable_prod n.primeFactors fun p _ => hX.measurable_primeSignNat p
    have h_eq : (fun ω => rademacherFunction X ω n) =
        fun ω => ((moebius n : ℤ) ^ 2) * ∏ p ∈ n.primeFactors, primeSignNat X p ω := by
      funext ω
      exact rademacherFunction_apply hn
    rw [h_eq]
    exact measurable_const.mul hprod

end MetaMathlibExt.RandomMultiplicativeFunction
