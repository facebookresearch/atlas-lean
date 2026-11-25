/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Algebra.Polynomial.Reverse

@[expose] public section

open Polynomial

namespace MathlibExt.NumberTheory.LehmerConstant

/-!
# Lehmer's Mahler measure constant

For an integer polynomial `f`, its Mahler measure is
`M(f) = |a| * ∏ᵢ max (1, |αᵢ|)`, where `a` is the leading coefficient and
the `αᵢ` are the complex roots of `f` counted with multiplicity. This is
`Polynomial.mapMahlerMeasure (Int.castRingHom ℂ)` in Mathlib, whose root
product formula is `Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots`.

Lehmer's constant (catalogue constant C40a) is the infimum of the Mahler
measures strictly larger than `1` among integer polynomials:
`L = inf {M(f) | f ∈ ℤ[X], 1 < M(f)}`. Lehmer's 1933 question asks whether
Mahler measures accumulate at `1`, equivalently whether `L = 1`; this file
proves that equivalence together with the elementary bounds `1 ≤ L ≤ 2`.
The sharp catalogue upper bound from Lehmer's example polynomial and
Smyth's nonreciprocal lower bound are registered as proof requests in the
wanted file.

Source: Optimization Problems, constants/40a.md, frozen at
teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; SHA-256
`d89b66d6b78a2de211675ee1e2deb67f427fc66a3d051adad8a740a28397e3e6`.
-/

/-- **Mahler measure of an integer polynomial.** The Mahler measure of $f \in \mathbb{Z}[X]$
is the Mahler measure of its image in $\mathbb{C}[X]$. It equals
$|a| \prod_i \max(1, |\alpha_i|)$, where $a$ is the leading coefficient of $f$ and the
$\alpha_i$ are the complex roots of $f$ counted with multiplicity. -/
noncomputable def intMahlerMeasure (f : Polynomial ℤ) : ℝ :=
  f.mapMahlerMeasure (Int.castRingHom ℂ)

theorem intMahlerMeasure_nonneg (f : Polynomial ℤ) :
    0 ≤ intMahlerMeasure f :=
  Polynomial.mahlerMeasure_nonneg _

/-- **Nonzero integer polynomials have Mahler measure at least one.** If
$f \in \mathbb{Z}[X]$ is a nonzero polynomial, then its Mahler measure satisfies $M(f) \ge 1$.

Indeed, $M(f) = |a| \prod_i \max(1, |\alpha_i|)$, where the leading coefficient $a$ of $f$ is a
nonzero integer and the $\alpha_i$ are the complex roots of $f$ counted with multiplicity, so
every factor is at least $1$. -/
theorem one_le_intMahlerMeasure {f : Polynomial ℤ} (hf : f ≠ 0) :
    1 ≤ intMahlerMeasure f := by
  have hlc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  calc
    (1 : ℝ) ≤ ‖f.leadingCoeff‖ := by
      rw [Int.norm_eq_abs]
      exact_mod_cast Int.one_le_abs hlc
    _ ≤ intMahlerMeasure f :=
      Polynomial.leadingCoeff_le_mapMahlerMeasure _ _ Complex.isometry_intCast

theorem intMahlerMeasure_mul (f g : Polynomial ℤ) :
    intMahlerMeasure (f * g) = intMahlerMeasure f * intMahlerMeasure g := by
  simp only [intMahlerMeasure, Polynomial.mapMahlerMeasure, Polynomial.map_mul,
    Polynomial.mahlerMeasure_mul]

theorem intMahlerMeasure_C (a : ℤ) :
    intMahlerMeasure (C a) = ‖(a : ℝ)‖ := by
  rw [intMahlerMeasure, Polynomial.mapMahlerMeasure, Polynomial.map_C,
    Polynomial.mahlerMeasure_const]
  simp

/-- **Mahler measure of a monic linear integer polynomial.** For every integer $a$, the
Mahler measure of the integer polynomial $X - a$ is $\max(1, |a|)$. -/
theorem intMahlerMeasure_X_sub_C (a : ℤ) :
    intMahlerMeasure (X - C a) = max 1 ‖(a : ℝ)‖ := by
  rw [intMahlerMeasure, Polynomial.mapMahlerMeasure, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.mahlerMeasure_X_sub_C]
  simp

theorem intMahlerMeasure_X : intMahlerMeasure (X : Polynomial ℤ) = 1 := by
  have h : (X : Polynomial ℤ) = X - C (0 : ℤ) := by simp
  rw [h, intMahlerMeasure_X_sub_C]
  simp

/-- **Mahler measure of $X - 1$.** The integer polynomial $X - 1$ has Mahler measure $1$.

Since $1$ is not strictly larger than $1$, this value is excluded from the set whose
infimum is Lehmer's constant. -/
theorem intMahlerMeasure_X_sub_one :
    intMahlerMeasure (X - C (1 : ℤ)) = 1 := by
  rw [intMahlerMeasure_X_sub_C]
  simp

/-- **Mahler measure of $X - 2$.** The integer polynomial $X - 2$ has Mahler measure $2$.

Since $2 > 1$, this value lies in the set whose infimum is Lehmer's constant. -/
theorem intMahlerMeasure_X_sub_two :
    intMahlerMeasure (X - C (2 : ℤ)) = 2 := by
  rw [intMahlerMeasure_X_sub_C]
  norm_num

/-- **Mahler measures above one.** This is the set of real numbers of the form $M(f)$, where
$f \in \mathbb{Z}[X]$ is an integer polynomial whose Mahler measure $M(f)$ is strictly larger
than $1$. -/
def mahlerMeasuresAboveOne : Set ℝ :=
  {y | ∃ f : Polynomial ℤ, 1 < intMahlerMeasure f ∧ y = intMahlerMeasure f}

/-- **Lehmer's constant.** Writing $M(f)$ for the Mahler measure of an integer polynomial $f$,
Lehmer's constant is
$C_{40a} = \inf \{M(f) : f \in \mathbb{Z}[X],\ M(f) > 1\}$,
the infimum of the Mahler measures of integer polynomials that are strictly larger than $1$. -/
noncomputable def lehmerConstant : ℝ :=
  sInf mahlerMeasuresAboveOne

theorem mahlerMeasuresAboveOne_nonempty : mahlerMeasuresAboveOne.Nonempty :=
  ⟨2, X - C (2 : ℤ), by rw [intMahlerMeasure_X_sub_two]; norm_num,
    intMahlerMeasure_X_sub_two.symm⟩

theorem mahlerMeasuresAboveOne_bddBelow : BddBelow mahlerMeasuresAboveOne :=
  ⟨1, by
    rintro y ⟨f, hf, rfl⟩
    exact le_of_lt hf⟩

/-- **Lehmer's constant bounds every Mahler measure above $1$.** For every integer polynomial
$f$ whose Mahler measure is strictly larger than $1$, Lehmer's constant is at most the Mahler
measure of $f$. -/
theorem lehmerConstant_le_intMahlerMeasure {f : Polynomial ℤ}
    (hf : 1 < intMahlerMeasure f) : lehmerConstant ≤ intMahlerMeasure f :=
  csInf_le mahlerMeasuresAboveOne_bddBelow ⟨f, hf, rfl⟩

/-- **Lehmer's constant is at least one.** Lehmer's constant $L$, the infimum of the Mahler
measures strictly larger than $1$ of polynomials in $\mathbb{Z}[X]$, satisfies $1 \le L$.

This is the lower bound recorded in the catalogue for the constant $C_{40a}$. -/
theorem one_le_lehmerConstant : 1 ≤ lehmerConstant :=
  le_csInf mahlerMeasuresAboveOne_nonempty (by
    rintro y ⟨f, hf, rfl⟩
    exact le_of_lt hf)

/-- **Lehmer's constant is at most $2$.** Lehmer's constant $C_{40a}$ satisfies
$C_{40a} \le 2$.

The witness is the integer polynomial $X - 2$, whose Mahler measure is $2$. -/
theorem lehmerConstant_le_two : lehmerConstant ≤ 2 := by
  rw [← intMahlerMeasure_X_sub_two]
  exact lehmerConstant_le_intMahlerMeasure (by
    rw [intMahlerMeasure_X_sub_two]; norm_num)

/-- **Lehmer's question.** The proposition that there are integer polynomials with
Mahler measure arbitrarily close to $1$ from above: for every real $\varepsilon > 0$ there is a
polynomial $f \in \mathbb{Z}[X]$ whose Mahler measure $M(f)$ satisfies $1 < M(f) < 1 + \varepsilon$.

Lehmer asked in 1933 whether this proposition holds. -/
def LehmerQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ f : Polynomial ℤ,
    1 < intMahlerMeasure f ∧ intMahlerMeasure f < 1 + ε

/-- **Lehmer's question in terms of Lehmer's constant.** Lehmer's constant equals $1$ if and
only if Lehmer's question has a positive answer, that is, for every $\varepsilon > 0$ there is
an integer polynomial whose Mahler measure lies strictly between $1$ and $1 + \varepsilon$. -/
theorem lehmerConstant_eq_one_iff : lehmerConstant = 1 ↔ LehmerQuestion := by
  constructor
  · intro hL ε hε
    obtain ⟨y, ⟨f, hf, rfl⟩, hy⟩ := exists_lt_of_csInf_lt
      mahlerMeasuresAboveOne_nonempty (show lehmerConstant < 1 + ε by linarith)
    exact ⟨f, hf, hy⟩
  · intro hQ
    apply le_antisymm _ one_le_lehmerConstant
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, hf1, hf2⟩ := hQ ε hε
    linarith [lehmerConstant_le_intMahlerMeasure hf1]

/-- **Lehmer's polynomial.** Lehmer's polynomial is the integer polynomial
$X^{10} + X^9 - X^7 - X^6 - X^5 - X^4 - X^3 + X + 1$.

Lehmer found it in 1933. Its Mahler measure $1.176280\ldots$ is still the smallest known
Mahler measure larger than $1$. -/
noncomputable def lehmerPolynomial : Polynomial ℤ :=
  X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

/-- **Smyth's polynomial.** Smyth's polynomial is $X^3 - X - 1 \in \mathbb{Z}[X]$.

Its Mahler measure is the plastic number $\theta_0 = 1.324717\ldots$, the real root of
$X^3 - X - 1$. Smyth proved in 1971 that every polynomial $f \in \mathbb{Z}[X]$ with
$f(0) \neq 0$ that is nonreciprocal (reversing its coefficients gives neither $f$ nor $-f$)
has Mahler measure at least $\theta_0$. -/
noncomputable def smythPolynomial : Polynomial ℤ :=
  X ^ 3 - X - 1

/-- **Reciprocal polynomial.** An integer polynomial $f$ is reciprocal when reversing its
coefficients gives $f$ or $-f$, that is, when $X^d f(1/X) = f$ or $X^d f(1/X) = -f$, where $d$
is the degree of $f$, taken to be $0$ when $f = 0$. -/
def IsReciprocal (f : Polynomial ℤ) : Prop :=
  f.reverse = f ∨ f.reverse = -f

theorem isReciprocal_one : IsReciprocal (1 : Polynomial ℤ) := by
  left
  simp [Polynomial.reverse]

end MathlibExt.NumberTheory.LehmerConstant
