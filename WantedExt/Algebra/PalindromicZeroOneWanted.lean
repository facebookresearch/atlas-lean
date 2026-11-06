/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Palindromic non-cyclotomic `0,1`-polynomials

Statements from Pradipto Banerjee and Amit Kundu, "On
an Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", *INTEGERS* 24 (2024),
Article A71
(<https://math.colgate.edu/~integers/vol24.html>).

A polynomial is *reciprocal* if `f.reverse = f`; a
*`0,1`-polynomial* has all coefficients in `{0, 1}`.
The paper's `𝒩` is the set of `0,1`-polynomials and
`𝒩_irred` its irreducible members; "reducible" is
stated as the negation of `Irreducible`. The even/odd
decomposition of Lemmas 2.1 and 2.2 and the congruence
of Theorem 1.3 were verified on exact examples
(e.g. `Φ₇`, whose square composition factors).

Not stated (see the source audit table): Lemmas 2.4
and 2.5, which use factor notation `g₁, g₂` and the
transform `u^e` set up only in the paper body, and the
root-theoretic equivalents in Theorem 1.2 (only its
polynomial reducibility equivalence is stated).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

set_option autoImplicit false

@[expose] public section

open Polynomial

namespace MathlibExt.Algebra.PalindromicZeroOneWanted

/-- **Reciprocal polynomial.** A polynomial $f(x) = a_0 + a_1 x + \dots + a_d x^d$ in
$\mathbb{Z}[x]$ of degree $d$ (with $d = 0$ for the zero polynomial) is *reciprocal*
(palindromic) if it equals its reversal $x^d f(1/x)$, that is, if $a_i = a_{d-i}$ for all
$0 \le i \le d$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
def IsReciprocalPoly (f : ℤ[X]) : Prop :=
  f.reverse = f

/-- **Characterization of reciprocal polynomials.** A polynomial $f \in \mathbb{Z}[x]$ of
degree $d$ (with $d = 0$ for the zero polynomial) is reciprocal if and only if its reversal
$x^d f(1/x)$ equals $f$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
theorem isReciprocalPoly_iff (f : ℤ[X]) :
    IsReciprocalPoly f ↔ f.reverse = f :=
  Iff.rfl

/-- **0,1-polynomial.** A polynomial $f \in \mathbb{Z}[x]$ is a *$0,1$-polynomial* if every
coefficient of $f$ is $0$ or $1$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
def IsZeroOnePoly (f : ℤ[X]) : Prop :=
  ∀ n : ℕ, f.coeff n = 0 ∨ f.coeff n = 1

/-- **Characterization of 0,1-polynomials.** A polynomial $f \in \mathbb{Z}[x]$ is a
$0,1$-polynomial if and only if, for every $n \ge 0$, the coefficient of $x^n$ in $f$ is
$0$ or $1$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
theorem isZeroOnePoly_iff (f : ℤ[X]) :
    IsZeroOnePoly f ↔ ∀ n : ℕ, f.coeff n = 0 ∨ f.coeff n = 1 :=
  Iff.rfl

/-- **Non-cyclotomic polynomial.** A polynomial $f \in \mathbb{Z}[x]$ is *non-cyclotomic* if
$f \ne \Phi_n$ for every positive integer $n$, where $\Phi_n$ denotes the $n$-th cyclotomic
polynomial.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
def IsNoncyclotomic (f : ℤ[X]) : Prop :=
  ∀ n : ℕ, 0 < n → f ≠ Polynomial.cyclotomic n ℤ

/-- **Characterization of non-cyclotomic polynomials.** A polynomial $f \in \mathbb{Z}[x]$ is
non-cyclotomic if and only if $f \ne \Phi_n$ for every positive integer $n$, where $\Phi_n$
denotes the $n$-th cyclotomic polynomial.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
theorem isNoncyclotomic_iff (f : ℤ[X]) :
    IsNoncyclotomic f ↔
      ∀ n : ℕ, 0 < n → f ≠ Polynomial.cyclotomic n ℤ :=
  Iff.rfl

/-- **Even–odd decomposition of a reciprocal polynomial.** Let $h \in \mathbb{Z}[x]$ be an
irreducible reciprocal polynomial of degree $2k$ such that $h \ne g(x^2)$ for every
$g \in \mathbb{Z}[x]$. Then there is exactly one $h_e \in \mathbb{Z}[x]$ for which there is
exactly one $h_o \in \mathbb{Z}[x]$ for which there is exactly one natural number $\ell$
such that $h_e$ and $h_o$ are reciprocal, $\ell$ is odd and positive, $\deg h_e = k$,
$\deg h_o = \max(k - \ell, 0)$, $h(x) = h_e(x^2) + x^\ell h_o(x^2)$ and
$h_e(0)\,h_o(0) \ne 0$.

Since $\ell$ is odd, $h_e(x^2)$ is the even part of $h$, and $h_o(0) \ne 0$ then determines
$\ell$ and $h_o$; so this amounts to a unique triple $(h_e, h_o, \ell)$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Lemma 2.1. -/
theorem_wanted existsUnique_evenOdd_reciprocal (h : ℤ[X]) (k : ℕ)
    (hirr : Irreducible h) (hrec : IsReciprocalPoly h)
    (hdeg : h.natDegree = 2 * k)
    (hnsq : ¬ ∃ g : ℤ[X], h = g.comp (X ^ 2)) :
    ∃! he : ℤ[X], ∃! ho : ℤ[X], ∃! l : ℕ,
      IsReciprocalPoly he ∧ IsReciprocalPoly ho ∧ Odd l ∧ 0 < l ∧
        he.natDegree = k ∧ ho.natDegree = k - l ∧
        h = he.comp (X ^ 2) + X ^ l * ho.comp (X ^ 2) ∧
        he.eval 0 * ho.eval 0 ≠ 0

/-- **Even–odd decomposition of a reciprocal 0,1-polynomial.** Let $f \in \mathbb{Z}[x]$ be
an irreducible reciprocal $0,1$-polynomial of degree $2m$ such that $f(x^2)$ is not
irreducible. Then there is exactly one $f_e \in \mathbb{Z}[x]$ for which there is exactly
one $f_o \in \mathbb{Z}[x]$ for which there is exactly one natural number $\ell$ such that
$f_e$ and $f_o$ are reciprocal $0,1$-polynomials, $\ell$ is odd and positive,
$\deg f_e = m$, $\deg f_o = \max(m - \ell, 0)$, $f(x) = f_e(x^2) + x^\ell f_o(x^2)$ and
$f_e(0)\,f_o(0) \ne 0$.

Since $\ell$ is odd, $f_e(x^2)$ is the even part of $f$, and $f_o(0) \ne 0$ then determines
$\ell$ and $f_o$; so this amounts to a unique triple $(f_e, f_o, \ell)$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Lemma 2.2. -/
theorem_wanted existsUnique_evenOdd_zeroOne (f : ℤ[X]) (m : ℕ)
    (h01 : IsZeroOnePoly f) (hirr : Irreducible f)
    (hrec : IsReciprocalPoly f) (hdeg : f.natDegree = 2 * m)
    (hred : ¬ Irreducible (f.comp (X ^ 2))) :
    ∃! fe : ℤ[X], ∃! fo : ℤ[X], ∃! l : ℕ,
      IsZeroOnePoly fe ∧ IsZeroOnePoly fo ∧
        IsReciprocalPoly fe ∧ IsReciprocalPoly fo ∧
        Odd l ∧ 0 < l ∧
        fe.natDegree = m ∧ fo.natDegree = m - l ∧
        f = fe.comp (X ^ 2) + X ^ l * fo.comp (X ^ 2) ∧
        fe.eval 0 * fo.eval 0 ≠ 0

/-- **Position of the first odd exponent.** Let $f \in \mathbb{Z}[x]$ be an irreducible,
reciprocal, non-cyclotomic $0,1$-polynomial of degree $2m$ such that $f(x^2)$ is not
irreducible. Let $f_e, f_o \in \mathbb{Z}[x]$ and let $\ell$ be a positive odd integer with
$f(x) = f_e(x^2) + x^\ell f_o(x^2)$, $\deg f_e = m$ and $\deg f_o = \max(m - \ell, 0)$, where
the degree of the zero polynomial is taken to be $0$. Then the coefficient of $x^e$ in $f$ is
$0$ for every $1 \le e < \ell$, the coefficient of $x^\ell$ in $f$ is nonzero, and $2\ell < m$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Lemma 2.3. -/
theorem_wanted l_eq_min_support_and_lt (f fe fo : ℤ[X]) (m l : ℕ)
    (h01 : IsZeroOnePoly f) (hirr : Irreducible f)
    (hrec : IsReciprocalPoly f) (hnc : IsNoncyclotomic f)
    (hdeg : f.natDegree = 2 * m)
    (hdecomp : f = fe.comp (X ^ 2) + X ^ l * fo.comp (X ^ 2))
    (hfe : fe.natDegree = m) (hfo : fo.natDegree = m - l)
    (hl : Odd l) (hl0 : 0 < l)
    (hred : ¬ Irreducible (f.comp (X ^ 2))) :
    (∀ e : ℕ, 1 ≤ e → e < l → f.coeff e = 0) ∧
      f.coeff l ≠ 0 ∧ 2 * l < m

/-- **Irreducibility under repeated squaring of the variable.** Let $f \in \mathbb{Z}[x]$ be
an irreducible, reciprocal, non-cyclotomic $0,1$-polynomial with fewer than $15$ nonzero
coefficients. Then $f(x^{2^n})$ is irreducible in $\mathbb{Z}[x]$ for every natural
number $n$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Theorem 1.1. -/
theorem_wanted irreducible_comp_pow_two_pow_of_card_lt (f : ℤ[X])
    (h01 : IsZeroOnePoly f) (hirr : Irreducible f)
    (hrec : IsReciprocalPoly f) (hnc : IsNoncyclotomic f)
    (hcard : f.support.card < 15) (n : ℕ) :
    Irreducible (f.comp (X ^ (2 ^ n)))

/-- **Capelli's theorem for $f(x^r)$.** Let $f \in \mathbb{Z}[x]$ be irreducible in
$\mathbb{Z}[x]$ and let $r \ge 2$ be an integer. Then $f(x^r)$ is reducible if and only if
either $f(x^p)$ is reducible for some prime $p$ dividing $r$, or $4$ divides $r$ and
$f(x^4)$ is reducible. Here reducible means not irreducible in $\mathbb{Z}[x]$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Theorem 1.2 (Capelli;
the root-theoretic equivalents stated there are
omitted). -/
theorem_wanted not_irreducible_comp_pow_iff (f : ℤ[X]) (r : ℕ)
    (hirr : Irreducible f) (hr : 2 ≤ r) :
    ¬ Irreducible (f.comp (X ^ r)) ↔
      (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ ¬ Irreducible (f.comp (X ^ p))) ∨
        (4 ∣ r ∧ ¬ Irreducible (f.comp (X ^ 4)))

/-- **Square compositions of $0,1$-polynomials modulo $4$.** Let $f \in \mathbb{Z}[x]$ be
irreducible in $\mathbb{Z}[x]$, with every coefficient equal to $0$ or $1$ and with constant
term $f(0) = 1$. If $f(x^2)$ is not irreducible in $\mathbb{Z}[x]$, then
$f(x^2) \equiv f(x)\,f(-x) \pmod 4$ as polynomials, that is, the two polynomials have the
same image in $(\mathbb{Z}/4\mathbb{Z})[x]$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Theorem 1.3. -/
theorem_wanted map_comp_sq_eq_mul (f : ℤ[X])
    (h01 : IsZeroOnePoly f) (hirr : Irreducible f) (hf0 : f.coeff 0 = 1)
    (hred : ¬ Irreducible (f.comp (X ^ 2))) :
    (f.comp (X ^ 2)).map (Int.castRingHom (ZMod 4)) =
      (f * f.comp (-X)).map (Int.castRingHom (ZMod 4))

/-- **Reducibility of $f(x^4)$ and $f(x^2)$ for $0,1$-polynomials.** Let
$f \in \mathbb{Z}[x]$ be irreducible in $\mathbb{Z}[x]$ and of positive degree, with every
coefficient equal to $0$ or $1$ and with constant term $f(0) = 1$. Then $f(x^4)$ is not
irreducible in $\mathbb{Z}[x]$ if and only if $f(x^2)$ is not irreducible in $\mathbb{Z}[x]$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Theorem 1.4. -/
theorem_wanted not_irreducible_comp_four_iff (f : ℤ[X])
    (h01 : IsZeroOnePoly f) (hirr : Irreducible f) (hf0 : f.coeff 0 = 1)
    (hdeg : 0 < f.natDegree) :
    ¬ Irreducible (f.comp (X ^ 4)) ↔ ¬ Irreducible (f.comp (X ^ 2))

end MathlibExt.Algebra.PalindromicZeroOneWanted
