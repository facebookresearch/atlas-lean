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

set_option autoImplicit false

@[expose] public section

open Polynomial

namespace MathlibExt.Algebra.PalindromicZeroOneWanted

/-- A polynomial is *reciprocal* (palindromic) if it
equals its coefficient reversal.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
def IsReciprocalPoly (f : ℤ[X]) : Prop :=
  f.reverse = f

/-- Characterization of `IsReciprocalPoly`.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
theorem isReciprocalPoly_iff (f : ℤ[X]) :
    IsReciprocalPoly f ↔ f.reverse = f :=
  Iff.rfl

/-- A *`0,1`-polynomial* has all coefficients in
`{0, 1}`.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
def IsZeroOnePoly (f : ℤ[X]) : Prop :=
  ∀ n : ℕ, f.coeff n = 0 ∨ f.coeff n = 1

/-- Characterization of `IsZeroOnePoly`.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
theorem isZeroOnePoly_iff (f : ℤ[X]) :
    IsZeroOnePoly f ↔ ∀ n : ℕ, f.coeff n = 0 ∨ f.coeff n = 1 :=
  Iff.rfl

/-- A polynomial is *non-cyclotomic* if it is not a
cyclotomic polynomial.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
def IsNoncyclotomic (f : ℤ[X]) : Prop :=
  ∀ n : ℕ, 0 < n → f ≠ Polynomial.cyclotomic n ℤ

/-- Characterization of `IsNoncyclotomic`.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
theorem isNoncyclotomic_iff (f : ℤ[X]) :
    IsNoncyclotomic f ↔
      ∀ n : ℕ, 0 < n → f ≠ Polynomial.cyclotomic n ℤ :=
  Iff.rfl

/-- **Lemma 2.1**: let `h(x) ∈ ℤ[x]` be an irreducible
reciprocal polynomial of degree `2k` which is not a
polynomial in `x^2`. Then there exist unique reciprocal
polynomials `h_e, h_o ∈ ℤ[x]` and a unique positive odd
integer `ℓ` such that `deg h_e = k`, `deg h_o = k - ℓ`,
`h(x) = h_e(x^2) + x^ℓ h_o(x^2)` and
`h_e(0) h_o(0) ≠ 0`.

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

/-- **Lemma 2.2**: let `f(x) ∈ 𝒩_irred` be reciprocal
of degree `2m` with `f(x^2)` reducible. Then there exist
unique reciprocal `0,1`-polynomials `f_e, f_o` and a
unique positive odd integer `ℓ` such that
`deg f_e = m`, `deg f_o = m - ℓ`,
`f(x) = f_e(x^2) + x^ℓ f_o(x^2)` and
`f_e(0) f_o(0) ≠ 0`.

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

/-- **Lemma 2.3**: let `f(x) ∈ 𝒩_irred` be reciprocal
and non-cyclotomic of degree `2m`, and let
`f(x) = f_e(x^2) + x^ℓ f_o(x^2)` be as in Lemma 2.2. If
`f(x^2)` is reducible, then `ℓ` is the smallest positive
exponent appearing in `f(x)` and `ℓ < m / 2`.

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

/-- **Theorem 1.1**: if `f(x) ∈ 𝒩_irred` is reciprocal,
non-cyclotomic, and has fewer than `15` terms, then
`f(x^{2^n})` is irreducible for every `n`.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Theorem 1.1. -/
theorem_wanted irreducible_comp_pow_two_pow_of_card_lt (f : ℤ[X])
    (h01 : IsZeroOnePoly f) (hirr : Irreducible f)
    (hrec : IsReciprocalPoly f) (hnc : IsNoncyclotomic f)
    (hcard : f.support.card < 15) (n : ℕ) :
    Irreducible (f.comp (X ^ (2 ^ n)))

/-- **Theorem 1.2**: let `f(x) ∈ ℤ[x]` be irreducible
and `r ≥ 2`. Then `f(x^r)` is reducible if and only if
either `f(x^p)` is reducible for some prime `p`
dividing `r`, or `4 ∣ r` and `f(x^4)` is reducible.

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

/-- **Theorem 1.3**: let `f(x) ∈ 𝒩_irred`. If `f(x^2)`
is reducible then `f(x^2) ≡ f(x) f(-x) (mod 4)` as
polynomials.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Theorem 1.3. -/
theorem_wanted map_comp_sq_eq_mul (f : ℤ[X])
    (h01 : IsZeroOnePoly f) (hirr : Irreducible f) (hf0 : f.coeff 0 = 1)
    (hred : ¬ Irreducible (f.comp (X ^ 2))) :
    (f.comp (X ^ 2)).map (Int.castRingHom (ZMod 4)) =
      (f * f.comp (-X)).map (Int.castRingHom (ZMod 4))

/-- **Theorem 1.4**: if `f(x) ∈ 𝒩_irred` is of positive
degree, then `f(x^4)` is reducible if and only if
`f(x^2)` is reducible.

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
