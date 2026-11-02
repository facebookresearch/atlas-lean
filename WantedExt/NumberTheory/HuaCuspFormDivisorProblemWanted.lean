/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion

namespace MetaMathlibExt

@[expose] public section

open UpperHalfPlane MatrixGroups ArithmeticFunction

/-- **Normalized Fourier coefficients of a cusp form.** Let $f$ be a cusp form of weight
$k \in \mathbb{Z}$ for $\mathrm{SL}_2(\mathbb{Z})$, with $q$-expansion
$f(z) = \sum_{n \ge 0} a_f(n) e(nz)$, where $e(z) = e^{2\pi i z}$. For each natural number $n$,
the normalized Fourier coefficient of $f$ is the complex number
$\lambda_f(n) = a_f(n) / n^{(k-1)/2}$, where $n^{(k-1)/2}$ is the real power.

At $n = 0$ the real power follows $0^0 = 1$ and $0^s = 0$ for $s \ne 0$, and division by $0$
gives $0$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1 (Fourier expansion of `f ∈ H_k^*`). -/
public noncomputable def cuspFormNormalizedCoeff {k : ℤ} (f : CuspForm 𝒮ℒ k) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n / (((n : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ)

/-- **Normalized cusp form coefficient at one.** Let $f$ be a cusp form of weight
$k \in \mathbb{Z}$ for $\mathrm{SL}_2(\mathbb{Z})$, with $q$-expansion
$f(z) = \sum_{n \ge 0} a_f(n) e^{2\pi i n z}$, and let $\lambda_f$ be its normalized Fourier
coefficients. Then $\lambda_f(1) = a_f(1)$, the coefficient of $e^{2\pi i z}$ in the
$q$-expansion of $f$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1. -/
public theorem cuspFormNormalizedCoeff_one {k : ℤ} (f : CuspForm 𝒮ℒ k) :
    cuspFormNormalizedCoeff f 1 = (qExpansion 1 f).coeff 1 := by
  simp [cuspFormNormalizedCoeff]

/-- **Normalized Hecke eigenform.** Let $f$ be a cusp form of weight $k \in \mathbb{Z}$ for
$\mathrm{SL}_2(\mathbb{Z})$, with normalized Fourier coefficients $\lambda_f$. Then $f$ is a
normalized Hecke eigenform when $\lambda_f(1) = 1$ and, for all positive integers $m$ and $n$,
$\lambda_f(m) \lambda_f(n) = \sum_{d \mid \gcd(m, n)} \lambda_f(mn/d^2)$, the sum running over the
positive divisors $d$ of $\gcd(m, n)$. The set of these forms is denoted $H_k^*$.

At level one this is equivalent to $f$ being a simultaneous eigenform of all Hecke operators
normalized by $a_f(1) = 1$, where $f(z) = \sum_{n \ge 0} a_f(n) e^{2\pi i n z}$ is the
$q$-expansion of $f$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1, Equation (1). -/
public def IsNormalizedHeckeEigenform {k : ℤ} (f : CuspForm 𝒮ℒ k) : Prop :=
  cuspFormNormalizedCoeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      cuspFormNormalizedCoeff f m * cuspFormNormalizedCoeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, cuspFormNormalizedCoeff f (m * n / d ^ 2)

/-- **Hecke relation at the square of a prime.** Let $f$ be a normalized Hecke eigenform of weight
$k \in \mathbb{Z}$ for $\mathrm{SL}_2(\mathbb{Z})$, with normalized Fourier coefficients
$\lambda_f$. Then $\lambda_f(p)^2 = \lambda_f(p^2) + 1$ for every prime $p$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Equation (1) with `m = n = p`. -/
public theorem IsNormalizedHeckeEigenform.normalizedCoeff_prime_sq {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {p : ℕ} (hp : p.Prime) :
    cuspFormNormalizedCoeff f p ^ 2 = cuspFormNormalizedCoeff f (p ^ 2) + 1 := by
  have h := hf.2 p p hp.pos hp.pos
  rw [Nat.gcd_self, hp.divisors, Finset.sum_insert (by simpa using hp.one_lt.ne)] at h
  have hp0 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  simp only [one_pow, Nat.div_one, Finset.sum_singleton] at h
  rw [show p * p / p ^ 2 = 1 by rw [← sq, Nat.div_self (Nat.pos_of_ne_zero hp0)], hf.1] at h
  rw [sq, h, sq]

/-- **Rankin–Selberg coefficients.** Let $f$ be a cusp form of weight $k \in \mathbb{Z}$ for
$\mathrm{SL}_2(\mathbb{Z})$, with normalized Fourier coefficients $\lambda_f$. The Rankin–Selberg
coefficients of $f$ form the arithmetic function $\lambda_{f \times f}$ with
$\lambda_{f \times f}(0) = 0$ and, for $n \ge 1$,
$\lambda_{f \times f}(n) = \sum_{l^2 m = n} \lambda_f(m)^2$, the sum running over the pairs of
positive integers $(l, m)$ with $l^2 m = n$; equivalently, $\lambda_{f \times f}(n)$ is the sum of
$\lambda_f(n/d)^2$ over the positive divisors $d$ of $n$ that are perfect squares.

These are the Dirichlet coefficients of
$L(f \times f, s) = \zeta(2s) \sum_{n \ge 1} \lambda_f(n)^2 n^{-s}$. The $w$-th power of
$\lambda_{f \times f}$ under Dirichlet convolution is denoted $\lambda_{w, f \times f}$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1 (definition of `λ_{f×f}` and
`λ_{w,f×f}`). -/
public noncomputable def rankinSelbergCoeff {k : ℤ} (f : CuspForm 𝒮ℒ k) : ArithmeticFunction ℂ :=
  ⟨fun n => ∑ d ∈ n.divisors with IsSquare d, cuspFormNormalizedCoeff f (n / d) ^ 2, by simp⟩

/-- **Rankin–Selberg coefficients as a sum over square divisors.** Let $f$ be a cusp form of
weight $k \in \mathbb{Z}$ for $\mathrm{SL}_2(\mathbb{Z})$, with normalized Fourier coefficients
$\lambda_f$ and Rankin–Selberg coefficients $\lambda_{f \times f}$. For every natural number $n$,
$\lambda_{f \times f}(n) = \sum_d \lambda_f(n/d)^2$, where $d$ runs over the positive divisors of
$n$ that are perfect squares (so the sum is empty when $n = 0$).

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1. -/
public theorem rankinSelbergCoeff_apply {k : ℤ} (f : CuspForm 𝒮ℒ k) (n : ℕ) :
    rankinSelbergCoeff f n =
      ∑ d ∈ n.divisors with IsSquare d, cuspFormNormalizedCoeff f (n / d) ^ 2 := rfl

/-- **Rankin–Selberg coefficient at one.** Let $f$ be a cusp form of weight $k \in \mathbb{Z}$ for
$\mathrm{SL}_2(\mathbb{Z})$, with normalized Fourier coefficients $\lambda_f$ and Rankin–Selberg
coefficients $\lambda_{f \times f}$. Then $\lambda_{f \times f}(1) = \lambda_f(1)^2$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1. -/
public theorem rankinSelbergCoeff_one {k : ℤ} (f : CuspForm 𝒮ℒ k) :
    rankinSelbergCoeff f 1 = cuspFormNormalizedCoeff f 1 ^ 2 := by
  rw [rankinSelbergCoeff_apply, Nat.divisors_one, Finset.filter_singleton]
  simp [show IsSquare (1 : ℕ) from ⟨1, rfl⟩]

/-- **Rankin–Selberg coefficients at primes.** Let $f$ be a cusp form of weight $k \in \mathbb{Z}$
for $\mathrm{SL}_2(\mathbb{Z})$, with normalized Fourier coefficients $\lambda_f$ and
Rankin–Selberg coefficients $\lambda_{f \times f}$. Then $\lambda_{f \times f}(p) = \lambda_f(p)^2$
for every prime $p$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1. -/
public theorem rankinSelbergCoeff_prime {k : ℤ} (f : CuspForm 𝒮ℒ k) {p : ℕ} (hp : p.Prime) :
    rankinSelbergCoeff f p = cuspFormNormalizedCoeff f p ^ 2 := by
  have hns : ¬ IsSquare p := fun h => by
    obtain ⟨r, hr⟩ := h
    have := hp.eq_one_or_self_of_dvd r ⟨r, hr⟩
    rcases this with h1 | h1
    · subst h1; simp at hr; exact hp.one_lt.ne' hr
    · rw [h1] at hr
      have : p * 1 = p * p := by simpa using hr
      have := Nat.eq_of_mul_eq_mul_left hp.pos this
      exact hp.one_lt.ne' this.symm
  rw [rankinSelbergCoeff_apply, hp.divisors, Finset.filter_insert, Finset.filter_singleton]
  simp [show IsSquare (1 : ℕ) from ⟨1, rfl⟩, hns]

/-- **Sums of squared normalized coefficients at perfect powers in arithmetic progressions.** Let
$f$ be a normalized Hecke eigenform of weight $k \in \mathbb{Z}$ for $\mathrm{SL}_2(\mathbb{Z})$,
with normalized Fourier coefficients $\lambda_f$, let $j \ge 2$ be an integer, and put
$\delta = 92/597$ if $j = 2$ and $\delta = 92/(69(j-1)(j+3) + 247)$ if $j \ge 3$. Then there are
real numbers $c_q > 0$, one for each prime $q$, with the following property: for every
$\varepsilon > 0$ there is a real constant $C$ such that for every prime $q$, every natural
number $l$ coprime to $q$ and every real $x \ge 1$ with $q \le x^{3\delta/4}$,
$\bigl|\sum_{n} \lambda_f(n^j)^2 - c_q x / \varphi(q)\bigr| \le
C q x^{1 - 3\delta/2 + \varepsilon}$, where $n$ runs over the integers $1 \le n \le x$ with
$n \equiv l \pmod q$ and $\varphi$ is Euler's totient function.

Hua quotes this result from Zou et al. [52, Theorem 1]. The constant $c_q$ is allowed to depend
on $q$, a weaker reading of the printed main term, whose constant does not depend on $q$; the
constant $C$ depends only on $f$, $j$ and $\varepsilon$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Theorem 1.1 (`integers-2024-A3-thm-1-1`). -/
public theorem_wanted sum_cuspFormNormalizedCoeff_pow_sq_arithmeticProgression {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {j : ℕ} (hj : 2 ≤ j) :
    let δ : ℝ := if j = 2 then 92 / 597 else 92 / (69 * ((j : ℝ) - 1) * ((j : ℝ) + 3) + 247)
    ∃ c : ℕ → ℝ, (∀ q : ℕ, q.Prime → 0 < c q) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ l : ℕ, Nat.Coprime l q →
        ∀ x : ℝ, 1 ≤ x → (q : ℝ) ≤ x ^ (3 / 4 * δ) →
          ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with n ≡ l [MOD q], cuspFormNormalizedCoeff f (n ^ j) ^ 2)
              - ((c q * x / (q.totient : ℝ) : ℝ) : ℂ)‖ ≤
            C * q * x ^ (1 - 3 / 2 * δ + ε)

/-- **Hua's theorem on squared Rankin–Selberg coefficients in arithmetic progressions.** Let $f$
be a level-one cusp form of weight $k$ that is a normalized Hecke eigenform, let
$\lambda_{f\times f}$ be its Rankin–Selberg coefficients, let $\varphi$ be Euler's totient
function, and put $\eta = 23/261$. There are real polynomials $P_q$, one for each prime $q$, each
of degree $1$ with positive leading coefficient, such that for every $\varepsilon > 0$ there is a
constant $C$ with

$$
\Bigl|\sum_{\substack{1 \le n \le x \\ n \equiv l \ (\mathrm{mod}\ q)}} \lambda_{f\times f}(n)^2 -
\frac{x}{\varphi(q)}\,P_q(\log x)\Bigr| \le C\,q\,x^{1 - 3\eta/2 + \varepsilon}
$$

for every prime $q$, every natural number $l$ coprime to $q$ and every real $x \ge 1$ with
$q \le x^{\eta}$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Theorem 1.2 (`integers-2024-A3-thm-1-2`). -/
public theorem_wanted sum_rankinSelbergCoeff_sq_arithmeticProgression {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) :
    ∃ P : ℕ → Polynomial ℝ, (∀ q : ℕ, q.Prime → (P q).natDegree = 1 ∧ 0 < (P q).leadingCoeff) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ l : ℕ, Nat.Coprime l q →
        ∀ x : ℝ, 1 ≤ x → (q : ℝ) ≤ x ^ ((23 : ℝ) / 261) →
          ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with n ≡ l [MOD q], rankinSelbergCoeff f n ^ 2)
              - ((x / (q.totient : ℝ) * (P q).eval (Real.log x) : ℝ) : ℂ)‖ ≤
            C * q * x ^ (1 - 3 / 2 * ((23 : ℝ) / 261) + ε)

/-- **Sums of Rankin–Selberg convolution powers in arithmetic progressions.** Let $f$ be a
normalized Hecke eigenform of weight $k \in \mathbb{Z}$ for $\mathrm{SL}_2(\mathbb{Z})$, with
Rankin–Selberg coefficients $\lambda_{f \times f}$, let $w \ge 2$ be an integer, write
$\lambda_{w, f \times f}$ for the $w$-fold Dirichlet convolution power of $\lambda_{f \times f}$,
and put $\vartheta_w = 92/(247w + 10)$. Then there are real polynomials $P_q$, one for each prime
$q$, each of degree $w - 1$ with positive leading coefficient, with the following property: for
every $\varepsilon > 0$ there is a real constant $C$ such that for every prime $q$, every natural
number $l$ coprime to $q$ and every real $x \ge 1$ with $q \le x^{\vartheta_w}$,
$\bigl|\sum_{n} \lambda_{w, f \times f}(n) - (x / \varphi(q)) P_q(\log x)\bigr| \le
C q x^{1 - 3\vartheta_w/2 + \varepsilon}$, where $n$ runs over the integers $1 \le n \le x$ with
$n \equiv l \pmod q$, $\varphi$ is Euler's totient function and $\log$ is the natural logarithm.

The printed hypothesis $q \ll x^{\vartheta_w}$ is read as $q \le x^{\vartheta_w}$, and the
polynomial is allowed to depend on $q$; the constant $C$ depends only on $f$, $w$ and
$\varepsilon$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Theorem 1.3 (`integers-2024-A3-thm-1-3`). -/
public theorem_wanted sum_rankinSelbergCoeff_pow_arithmeticProgression {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {w : ℕ} (hw : 2 ≤ w) :
    ∃ P : ℕ → Polynomial ℝ,
      (∀ q : ℕ, q.Prime → (P q).natDegree = w - 1 ∧ 0 < (P q).leadingCoeff) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ l : ℕ, Nat.Coprime l q →
        ∀ x : ℝ, 1 ≤ x → (q : ℝ) ≤ x ^ ((92 : ℝ) / (247 * w + 10)) →
          ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with n ≡ l [MOD q], (rankinSelbergCoeff f ^ w) n)
              - ((x / (q.totient : ℝ) * (P q).eval (Real.log x) : ℝ) : ℂ)‖ ≤
            C * q * x ^ (1 - 3 / 2 * ((92 : ℝ) / (247 * w + 10)) + ε)

/-- **Sums of squared Rankin–Selberg coefficients twisted by a primitive character.** Let $f$ be
a level-one cusp form of weight $k$ that is a normalized Hecke eigenform, let
$\lambda_{f\times f}$ be its Rankin–Selberg coefficients, and put $\eta = 23/261$. For every
$\varepsilon > 0$ there is a constant $C$ such that for every prime $q$, every primitive Dirichlet
character $\chi$ modulo $q$ and every real $x \ge 1$ with $q \le x^{\eta}$,

$$
\Bigl|\sum_{1 \le n \le x} \lambda_{f\times f}(n)^2\,\chi(n)\Bigr| \le
C\,q\,x^{1 - 3\eta/2 + \varepsilon}.
$$

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Proposition 3.1 (`integers-2024-A3-prop-3-1`). -/
public theorem_wanted sum_rankinSelbergCoeff_sq_mul_primitive_character {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∀ x : ℝ, 1 ≤ x → (q : ℝ) ≤ x ^ ((23 : ℝ) / 261) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, rankinSelbergCoeff f n ^ 2 * χ n‖ ≤
          C * q * x ^ (1 - 3 / 2 * ((23 : ℝ) / 261) + ε)

/-- **Sums of squared Rankin–Selberg coefficients twisted by the principal character.** Let $f$ be
a level-one cusp form of weight $k$ that is a normalized Hecke eigenform, let
$\lambda_{f\times f}$ be its Rankin–Selberg coefficients, and for a prime $q$ let $\chi_0$ be the
principal Dirichlet character modulo $q$. There are real polynomials $P_q$, one for each prime
$q$, each of degree $1$ with positive leading coefficient, such that for every $\varepsilon > 0$
there is a constant $C$ with

$$
\Bigl|\sum_{1 \le n \le x} \lambda_{f\times f}(n)^2\,\chi_0(n) - x\,P_q(\log x)\Bigr| \le
C\,x^{179/209 + \varepsilon}
$$

for every prime $q$ and every real $x \ge q$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Proposition 3.2 (`integers-2024-A3-prop-3-2`). -/
public theorem_wanted sum_rankinSelbergCoeff_sq_mul_principal_character {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) :
    ∃ P : ℕ → Polynomial ℝ, (∀ q : ℕ, q.Prime → (P q).natDegree = 1 ∧ 0 < (P q).leadingCoeff) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ x : ℝ, (q : ℝ) ≤ x →
        ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, rankinSelbergCoeff f n ^ 2 * (1 : DirichletCharacter ℂ q) n)
            - ((x * (P q).eval (Real.log x) : ℝ) : ℂ)‖ ≤
          C * x ^ ((179 : ℝ) / 209 + ε)

/-- **Sums of Rankin–Selberg convolution powers twisted by a primitive character.** Let $f$ be a
level-one cusp form of weight $k$ that is a normalized Hecke eigenform, let $\lambda_{f\times f}$
be its Rankin–Selberg coefficients, let $w \ge 2$, let $\lambda_{w,f\times f}$ be the $w$-th
power of $\lambda_{f\times f}$ under Dirichlet convolution, and put
$\vartheta_w = 92/(247w + 10)$. For every $\varepsilon > 0$ there is a constant $C$ such that for
every prime $q$, every primitive Dirichlet character $\chi$ modulo $q$ and every real $x \ge 1$
with $q \le x^{\vartheta_w}$,

$$
\Bigl|\sum_{1 \le n \le x} \lambda_{w,f\times f}(n)\,\chi(n)\Bigr| \le
C\,q\,x^{1 - 3\vartheta_w/2 + \varepsilon}.
$$

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Proposition 4.1 (`integers-2024-A3-prop-4-1`). -/
public theorem_wanted sum_rankinSelbergCoeff_pow_mul_primitive_character {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {w : ℕ} (hw : 2 ≤ w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∀ x : ℝ, 1 ≤ x → (q : ℝ) ≤ x ^ ((92 : ℝ) / (247 * w + 10)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinSelbergCoeff f ^ w) n * χ n‖ ≤
          C * q * x ^ (1 - 3 / 2 * ((92 : ℝ) / (247 * w + 10)) + ε)

/-- **Sums of Rankin–Selberg convolution powers twisted by the principal character.** Let $f$ be a
level-one cusp form of weight $k$ that is a normalized Hecke eigenform, let $\lambda_{f\times f}$
be its Rankin–Selberg coefficients, let $w \ge 2$, let $\lambda_{w,f\times f}$ be the $w$-th
power of $\lambda_{f\times f}$ under Dirichlet convolution, and for a prime $q$ let $\chi_0$ be
the principal Dirichlet character modulo $q$. There are real polynomials $P_q$, one for each
prime $q$, each of degree $w - 1$, such that for every $\varepsilon > 0$ there is a constant $C$
with

$$
\Bigl|\sum_{1 \le n \le x} \lambda_{w,f\times f}(n)\,\chi_0(n) - x\,P_q(\log x)\Bigr| \le
C\,x^{1 - 210/(317w + 115) + \varepsilon}
$$

for every prime $q$ and every real $x \ge q$.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Proposition 4.2 (`integers-2024-A3-prop-4-2`). -/
public theorem_wanted sum_rankinSelbergCoeff_pow_mul_principal_character {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {w : ℕ} (hw : 2 ≤ w) :
    ∃ P : ℕ → Polynomial ℝ, (∀ q : ℕ, q.Prime → (P q).natDegree = w - 1) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ x : ℝ, (q : ℝ) ≤ x →
        ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinSelbergCoeff f ^ w) n * (1 : DirichletCharacter ℂ q) n)
            - ((x * (P q).eval (Real.log x) : ℝ) : ℂ)‖ ≤
          C * x ^ (1 - (210 : ℝ) / (317 * w + 115) + ε)

end

end MetaMathlibExt
