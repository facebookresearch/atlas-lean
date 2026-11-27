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
decomposition of Lemmas 1 and 2 and the congruence
of Theorem 1.3 were verified on exact examples
(e.g. `Φ₇`, whose square composition factors).

Lemmas 4 and 5 are stated from the journal PDF, with
the setup of `g₁, g₂` (Section 3) as hypotheses and
the reciprocal `ũ(x) = x^{deg u} u(1/x)` as
`Polynomial.reverse`. Not stated: the root-theoretic
equivalents in Theorem 1.2 (only its polynomial
reducibility equivalence is stated).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import MathlibExt.Algebra.Polynomial.ReciprocalEvenOddDecomposition
public import MathlibExt.Algebra.Polynomial.ReciprocalZeroOneFirstOddExponent
public import MathlibExt.Algebra.Polynomial.ZeroOneSquareComposition

set_option autoImplicit false

@[expose] public section

open Polynomial

namespace MathlibExt.Algebra.PalindromicZeroOneWanted

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
Non-cyclotomic 0,1-Polynomials", INTEGERS 24 (2024),
Article A71, Lemma 2. -/
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

/-- **Lemma 4**: in the setting of Section 3, let
`f(x^2) = g(x) g(-x)` with
`g(x) = g_e(x^2) + x^ℓ g_o(x^2)`, `ℓ` odd and `g_e, g_o`
reciprocal, and let `{g₁, g₂} = {g_e, g_o}` with
`deg g₁` odd. If `g₂(1) ≡ 0 (mod 4)` then
`f(-1) ≡ 0 (mod 16)`. The paper also assumes
`f(1) ≡ ±4 (mod 16)` and that `f` is an irreducible
reciprocal `0,1`-polynomial; the proof does not use
these, and they are dropped.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", INTEGERS 24 (2024),
Article A71, Lemma 4. -/
theorem_wanted eval_neg_one_modEq_zero_sixteen (f g ge go g₁ g₂ : ℤ[X]) (ℓ : ℕ)
    (hfg : f.comp (X ^ 2) = g * g.comp (-X))
    (hg : g = ge.comp (X ^ 2) + X ^ ℓ * go.comp (X ^ 2)) (hℓ : Odd ℓ)
    (hge : IsReciprocalPoly ge) (hgo : IsReciprocalPoly go)
    (h12 : (g₁ = ge ∧ g₂ = go) ∨ (g₁ = go ∧ g₂ = ge)) (hodd : Odd g₁.natDegree)
    (h4 : g₂.eval 1 ≡ 0 [ZMOD 4]) :
    f.eval (-1) ≡ 0 [ZMOD 16]

/-- **Lemma 5** (corrected reading of the parity
clause): let `h(x) ∈ ℤ[x]` be reciprocal of degree
`n > 0` and `d = ⌊n/2⌋`. There are unique `u(x) ∈ ℤ[x]`
with `deg u < n/2` and integers `M > n/2` and `a` with
`h(x) = x^M ũ(x) + a x^d + u(x)`, where
`ũ(x) = x^{deg u} u(1/x)` (`Polynomial.reverse`); `a = 0`
if `n` is odd; and `a = 0` if `h(1)` is even and `h` is
a `0,1`-polynomial. Over `ℤ[x]` the parity clause fails:
`h = x^2 + 2x + 1` has `u = 1`, `M = 2`, `a = 2` with
`h(1) = 4`; the paper applies it only to
`0,1`-polynomials. "Reciprocal" is `h̃ = h` (the plus
sign), which the proof's symmetric coefficients use.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", INTEGERS 24 (2024),
Article A71, Lemma 5. -/
theorem_wanted existsUnique_reciprocal_split (h : ℤ[X]) (hrec : IsReciprocalPoly h)
    (hn : 0 < h.natDegree) :
    let P : ℤ[X] × ℕ × ℤ → Prop := fun t =>
      2 * t.1.natDegree < h.natDegree ∧ h.natDegree < 2 * t.2.1 ∧
        h = X ^ t.2.1 * t.1.reverse + C t.2.2 * X ^ (h.natDegree / 2) + t.1
    (∃! t, P t) ∧ (∀ t, P t → Odd h.natDegree → t.2.2 = 0) ∧
      (∀ t, P t → IsZeroOnePoly h → Even (h.eval 1) → t.2.2 = 0)

end MathlibExt.Algebra.PalindromicZeroOneWanted
