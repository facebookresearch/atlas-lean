/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.SquareModEight

/-!
# Angle bisectors and congruence obstructions for `|x² - d y²| = z`

These results appear in Takashi Hirotsu, *General Pell's
Equations and Angle Bisectors between Planar Lines with Rational
Slopes*, INTEGERS 24 (2024), Article A111.

Squaring the equality of distances to two lines gives an equation for their bisector slope.
For slopes on the same negative Pell conic, rational solutions admit a quotient formula.

Squares are `0` or `1` modulo `4`, so for `d ≡ 1 (mod 4)` the value
`x² - d y²` is `0`, `1`, or `3` modulo `4`, and so is its negation.
Modulo `8`, squares are `0`, `1`, or `4`. If `x² ≡ 5 y² (mod 8)`, both squares are even.

Multiplying `x + y √d` by a solution `a + b √d` of `a² - d b² = -1` negates the value of
`x² - d y²` and keeps the first coordinate coprime to `d` times the second, so strictly primitive
solutions of `x² - d y² = z` give strictly primitive solutions of `x² - d y² = -z`.
Products of strictly primitive solutions whose absolute norms are powers of distinct primes
are strictly primitive as well.

The fundamental solution of the negative Pell equation and the coordinates of its powers
(`MetaMathlibExt.negPellF`, `MetaMathlibExt.negPellG`) satisfy the norm identity
$f_n^2 - d g_n^2 = (-1)^n$ and the comparison $g_n \le f_n$
(`MetaMathlibExt.negPellG_le_negPellF`).

## References

- Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
  Rational Slopes*, INTEGERS 24 (2024), Article A111, pp. 1–26. The negative Pell identities
  used here are Proposition 5, equations (23) and (24), and Proposition 6(a), equations (27)
  and (28).
- Thomas Koshy, *Pell and Pell–Lucas Numbers with Applications*, Springer, 2014, §2.4, cited
  by Hirotsu for Proposition 5.
- Paulo Ribenboim, *The New Book of Prime Number Records*, Springer, 1996, Chapter 2, IV,
  cited by Hirotsu for the more general Lucas-sequence formulas behind Proposition 6.
-/

@[expose] public section

namespace MetaMathlibExt

-- The first bisector distance equality suffices for this implication.
set_option linter.unusedVariables false in
/-- **Angle bisectors satisfy the bisector equation.** Let $a, b, c$ be real numbers with
$|a| \ne |b|$ and $c \ne 0$, and suppose that the lines $y = cx$ and $y = -c^{-1} x$ both bisect
the angles between the lines $y = ax$ and $y = bx$, that is,
$$
\frac{|a - c|}{\sqrt{a^2 + 1}} = \frac{|b - c|}{\sqrt{b^2 + 1}} \quad\text{and}\quad
\frac{|a + c^{-1}|}{\sqrt{a^2 + 1}} = \frac{|b + c^{-1}|}{\sqrt{b^2 + 1}}.
$$
Then $(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$.

A line $y = sx$ bisects the angles between $y = ax$ and $y = bx$ exactly when the point $(1, s)$
is equidistant from both lines, that is, when $|a - s| / \sqrt{a^2 + 1} = |b - s| / \sqrt{b^2 + 1}$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 1(a)
(`integers-2024-A111-prop-1`). -/
theorem bisector_slope_equation (a b c : ℝ) (hab : |a| ≠ |b|) (hc : c ≠ 0)
    (hbis : |a - c| / √(a ^ 2 + 1) = |b - c| / √(b ^ 2 + 1))
    (hbis' : |a + c⁻¹| / √(a ^ 2 + 1) = |b + c⁻¹| / √(b ^ 2 + 1)) :
    (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1) := by
  have h := (div_eq_div_iff (by positivity) (by positivity)).mp hbis
  apply_fun (fun x : ℝ ↦ x ^ 2) at h
  simpa (disch := positivity) only [mul_pow, sq_abs, Real.sq_sqrt] using h

/-- **Symmetries of the bisector equation.** Let $a, b, c$ be real numbers with
$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$. Then the triples $(-a, -b, -c)$ and $(b, a, c)$
satisfy the same equation, and so does $(a, b, -c^{-1})$ when $c \ne 0$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 2(a)
(`integers-2024-A111-prop-2`). -/
theorem bisector_equation_symm (a b c : ℝ)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) :
    (c ≠ 0 → (a - -c⁻¹) ^ 2 * (b ^ 2 + 1) = (b - -c⁻¹) ^ 2 * (a ^ 2 + 1)) ∧
      (-a - -c) ^ 2 * ((-b) ^ 2 + 1) = (-b - -c) ^ 2 * ((-a) ^ 2 + 1) ∧
      (b - c) ^ 2 * (a ^ 2 + 1) = (a - c) ^ 2 * (b ^ 2 + 1) := by
  refine ⟨?_, ?_, h.symm⟩
  · intro hc
    -- After clearing denominators, the difference is the negative of the original difference.
    field_simp [hc]
    linear_combination -h
  · linear_combination h

-- Squarefreeness is part of the source statement. The sign choice uses only the Pell equations.
set_option linter.unusedVariables false in
/-- **Rational solutions of the bisector equation for square-free $d > 1$.** Let $d > 1$ be a
square-free integer and let $a, b, c$ be rational numbers with $|a| \ne |b|$ and
$$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1).$$
Suppose there are rational numbers $u, v$ with $a^2 - d u^2 = -1$ and $b^2 - d v^2 = -1$. Then
there are rational numbers $a_2, b_2$ with $a^2 - d a_2^2 = -1$ and $b^2 - d b_2^2 = -1$ such
that either $a_2 + b_2 \ne 0$ and $c = (a b_2 + a_2 b) / (a_2 + b_2)$, or $a b_2 + a_2 b \ne 0$
and $c = -(a_2 + b_2) / (a b_2 + a_2 b)$.

In terms of $\alpha = a + a_2 \sqrt{d}$ and $\beta = b + b_2 \sqrt{d}$, which have norm $-1$, and
the conjugation $'$ of $\mathbb{Q}(\sqrt{d})$, the first quotient is
$(\alpha\beta - (\alpha\beta)') / (\alpha + \beta - (\alpha + \beta)')$.

Source: the theorem's second part (the factorization of $\alpha, \beta$ through $\eta$, $\xi_p$
and $S(d)$) is not formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1(ii), first
sentence (`integers-2024-A111-thm-1`). -/
theorem bisector_equation_rat_solution_negPell (d : ℤ) (hd : 1 < d)
    (hsq : Squarefree d) (a b c : ℚ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1))
    (ha : ∃ a₂ : ℚ, a ^ 2 - d * a₂ ^ 2 = -1) (hb : ∃ b₂ : ℚ, b ^ 2 - d * b₂ ^ 2 = -1) :
    ∃ a₂ b₂ : ℚ, a ^ 2 - d * a₂ ^ 2 = -1 ∧ b ^ 2 - d * b₂ ^ 2 = -1 ∧
      ((a₂ + b₂ ≠ 0 ∧ c = (a * b₂ + a₂ * b) / (a₂ + b₂)) ∨
        (a * b₂ + a₂ * b ≠ 0 ∧ c = -(a₂ + b₂) / (a * b₂ + a₂ * b))) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have hd₀ : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hs : ((a - c) * v) ^ 2 = ((b - c) * u) ^ 2 := by
    apply mul_left_cancel₀ hd₀
    linear_combination h - (a - c) ^ 2 * hv + (b - c) ^ 2 * hu
  -- Choose the sign of the second coordinate paired with `a` so the two products cancel.
  obtain ⟨u', hu', hsign⟩ : ∃ u' : ℚ, a ^ 2 - d * u' ^ 2 = -1 ∧
      (a - c) * v = -((b - c) * u') := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with heq | heq
    · exact ⟨-u, by simpa using hu, by simpa using heq⟩
    · exact ⟨u, hu, heq⟩
  have hden : u' + v ≠ 0 := by
    intro hz
    apply hab
    apply (sq_eq_sq_iff_abs_eq_abs a b).mp
    linear_combination hu' - hv + (d : ℚ) * (u' - v) * hz
  refine ⟨u', v, hu', hv, Or.inl ⟨hden, (eq_div_iff hden).2 ?_⟩⟩
  linear_combination -hsign

/-- **Bisector-equation solutions from two solutions of $x^2 - d y^2 = -1$.** Let $d$ be an integer
and let $a, a_2, b, b_2$ be rational numbers with $a^2 - d a_2^2 = -1$ and $b^2 - d b_2^2 = -1$.
If $a_2 + b_2 \ne 0$, then $c = (a b_2 + a_2 b) / (a_2 + b_2)$ satisfies
$$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1),$$
and if $a b_2 + a_2 b \ne 0$, then $c = -(a_2 + b_2) / (a b_2 + a_2 b)$ satisfies it as well.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1, converse
for (3) (`integers-2024-A111-thm-1`). -/
theorem bisector_equation_form_three (d : ℤ) (a a₂ b b₂ : ℚ)
    (ha : a ^ 2 - d * a₂ ^ 2 = -1) (hb : b ^ 2 - d * b₂ ^ 2 = -1) :
    (a₂ + b₂ ≠ 0 → let c := (a * b₂ + a₂ * b) / (a₂ + b₂)
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) ∧
    (a * b₂ + a₂ * b ≠ 0 → let c := -(a₂ + b₂) / (a * b₂ + a₂ * b)
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) := by
  have h : a₂ ^ 2 * (b ^ 2 + 1) = b₂ ^ 2 * (a ^ 2 + 1) := by
    linear_combination a₂ ^ 2 * hb - b₂ ^ 2 * ha
  constructor
  · intro hden
    dsimp only
    field_simp [hden]
    linear_combination (a - b) ^ 2 * h
  · intro hden
    dsimp only
    field_simp [hden]
    linear_combination -(a - b) ^ 2 * h

/-- If `d ≡ 1 (mod 4)` and `z ≡ 2 (mod 4)`, then `|x² - d y²| = z`
has no integral solutions.

The source's `z > 1` is not needed. The second sentence of part (a)
(on `S(d)` and `l_2`) is not formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle
Bisectors between Planar Lines with Rational Slopes*, INTEGERS 24
(2024), Article A111, Lemma 1(a), first sentence
(`integers-2024-A111-lem-1`).
Proves `Wanted` entry `abs_sq_sub_mul_sq_ne_of_two_mod_four`. -/
theorem abs_sq_sub_mul_sq_ne_of_two_mod_four (d z : ℤ) (hd : d % 4 = 1)
    (hz : z % 4 = 2) (x y : ℤ) : |x ^ 2 - d * y ^ 2| ≠ z := by
  have hsq : ∀ t : ℤ, t ^ 2 % 4 = 0 ∨ t ^ 2 % 4 = 1 := by
    intro t
    rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3)
        with ht | ht | ht | ht <;>
      simp [pow_two, Int.mul_emod, ht]
  have hdy : d * y ^ 2 % 4 = y ^ 2 % 4 := by
    rw [Int.mul_emod, hd, one_mul, Int.emod_emod_of_dvd _ (dvd_refl 4)]
  rcases abs_cases (x ^ 2 - d * y ^ 2) with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rcases hsq x with hx | hx <;> rcases hsq y with hy | hy <;> omega

/-- **Solutions of |x² − dy²| = z are even when d ≡ 5 and z ≡ 0 (mod 8).** Let $d$ and $z$ be
integers with $d \equiv 5 \pmod 8$ and $z \equiv 0 \pmod 8$. If integers $x$ and $y$ satisfy
$|x^2 - dy^2| = z$, then $x$ and $y$ are both even.

The paper also assumes $z > 1$; this is not needed.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Lemma 1(d) (`integers-2024-A111-lem-1`). -/
theorem even_of_abs_sq_sub_mul_sq_zero_mod_eight (d z : ℤ) (hd : d % 8 = 5)
    (hz : z % 8 = 0) (x y : ℤ) (h : |x ^ 2 - d * y ^ 2| = z) : Even x ∧ Even y := by
  have hmod : d * y ^ 2 % 8 = x ^ 2 % 8 := by
    apply Int.modEq_iff_dvd.mpr
    rw [← dvd_abs, h]
    exact Int.dvd_of_emod_eq_zero hz
  rw [Int.mul_emod, hd] at hmod
  suffices hxy : Even (x ^ 2) ∧ Even (y ^ 2) by simpa [Int.even_pow] using hxy
  simp only [Int.even_iff]
  have hx := Int.sq_emod_eight x
  have hy := Int.sq_emod_eight y
  omega

/-- **Solutions of |x² − dy²| = z are even when d ≡ 1 and z ≡ 4 (mod 8).** Let $d$ and $z$ be
integers with $d \equiv 1 \pmod 8$ and $z \equiv 4 \pmod 8$. If integers $x$ and $y$ satisfy
$|x^2 - dy^2| = z$, then $x$ and $y$ are both even.

The paper also assumes $z > 1$; this is not needed. The second sentence of part (c) of the
paper's lemma, on the fundamental unit, is not formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Lemma 1(c), first sentence
(`integers-2024-A111-lem-1`). -/
theorem even_of_abs_sq_sub_mul_sq_four_mod_eight (d z : ℤ) (hd : d % 8 = 1)
    (hz : z % 8 = 4) (x y : ℤ) (h : |x ^ 2 - d * y ^ 2| = z) : Even x ∧ Even y := by
  -- The two possible signs have the same residue modulo eight.
  have emod_eq_four (n : ℤ) (hn : |n| = z) : n % 8 = 4 := by
    rcases abs_cases n with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rw [hs] at hn <;> omega
  have hmod := emod_eq_four _ h
  rw [Int.sub_emod, Int.mul_emod d, hd, one_mul, Int.emod_emod] at hmod
  -- Of the square residues 0, 1 and 4, only 0 and 4 differ by 4 modulo eight.
  suffices hxy : Even (x ^ 2) ∧ Even (y ^ 2) by simpa [Int.even_pow] using hxy
  simp only [Int.even_iff]
  have h₂ : (2 : ℤ) ∣ 8 := by decide
  rw [← Int.emod_emod_of_dvd (x ^ 2) h₂, ← Int.emod_emod_of_dvd (y ^ 2) h₂]
  rcases Int.sq_emod_eight x with hx | hx | hx <;>
    rcases Int.sq_emod_eight y with hy | hy | hy <;> norm_num [hx, hy] at hmod <;>
    norm_num [hx, hy]

-- The hypotheses `1 < d`, `Squarefree d` and `z ≠ 0` from the source are not needed.
set_option linter.unusedVariables false in
/-- **Negating the value of a strictly primitive solution.** Let $d > 1$ be a square-free integer
such that $x^2 - d y^2 = -1$ has an integral solution, and let $z \ne 0$ be an integer. If
$x^2 - d y^2 = z$ has an integral solution with $x$ and $d y$ coprime, then so does
$x^2 - d y^2 = -z$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 4
(`integers-2024-A111-prop-4`). -/
theorem strictlyPrimitive_neg (d : ℤ) (hd : 1 < d) (hsq : Squarefree d) (z : ℤ)
    (hz : z ≠ 0) (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1)
    (h : ∃ x y : ℤ, IsCoprime x (d * y) ∧ x ^ 2 - d * y ^ 2 = z) :
    ∃ x y : ℤ, IsCoprime x (d * y) ∧ x ^ 2 - d * y ^ 2 = -z := by
  obtain ⟨a, b, hab⟩ := hneg
  obtain ⟨x, y, ⟨u, v, huv⟩, rfl⟩ := h
  -- Take `(x + y √d) (a + b √d)`. Since `a² - d b² = -1`, the Bézout identity
  -- `u x + v (d y) = 1` turns into one for the new first coordinate and `d` times the second.
  refine ⟨x * a + d * y * b, x * b + y * a, ⟨-u * a + v * d * b, u * b - v * a, ?_⟩, ?_⟩
  · linear_combination (-(a ^ 2 - d * b ^ 2)) * huv - hab
  · linear_combination (x ^ 2 - d * y ^ 2) * hab

-- Multiplying by the conjugate of `b` recovers the coordinates of `a` scaled by `b.norm`.
-- The Bézout identity for `a` then expresses `b.norm` in terms of the product's coordinates.
private theorem dvd_norm_of_dvd_mul_coords {d k : ℤ} {a b : ℤ√d}
    (ha : IsCoprime a.re (d * a.im)) (hre : k ∣ (a * b).re) (him : k ∣ d * (a * b).im) :
    k ∣ b.norm := by
  obtain ⟨u, v, huv⟩ := ha
  calc
    k ∣ (u * b.re - v * d * b.im) * (a * b).re +
        (v * b.re - u * b.im) * (d * (a * b).im) :=
      dvd_add (dvd_mul_of_dvd_right hre _) (dvd_mul_of_dvd_right him _)
    _ = b.norm := by
      rw [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.norm_def]
      linear_combination (b.re * b.re - d * b.im * b.im) * huv

private theorem strictlyPrimitive_mul_of_coprime_norms {d : ℤ} {a b : ℤ√d}
    (ha : IsCoprime a.re (d * a.im)) (hb : IsCoprime b.re (d * b.im))
    (hn : IsCoprime a.norm b.norm) : IsCoprime (a * b).re (d * (a * b).im) := by
  apply IsRelPrime.isCoprime
  intro k hre him
  apply hn.isUnit_of_dvd' _ (dvd_norm_of_dvd_mul_coords ha hre him)
  rw [mul_comm a b] at hre him
  exact dvd_norm_of_dvd_mul_coords hb hre him

-- The coordinate argument works for all integers `d`.
set_option linter.unusedVariables false in
/-- **Products of strictly primitive solutions.** Let $d > 1$ be a square-free integer. Write
elements of $\mathbb{Z}[\sqrt{d}]$ as $u + v\sqrt{d}$ with integers $u, v$, and let
$N(u + v\sqrt{d}) = u^2 - d v^2$ be the norm. Let $p_1, \dots, p_r$ be distinct primes and
$n_1, \dots, n_r$ natural numbers, and suppose that each $a_i = u_i + v_i\sqrt{d}$ satisfies
$|N(a_i)| = p_i^{n_i}$ with $u_i$ and $d v_i$ coprime. Then $a = a_1 \cdots a_r = u + v\sqrt{d}$
satisfies $|N(a)| = p_1^{n_1} \cdots p_r^{n_r}$ with $u$ and $d v$ coprime; that is, $a$ gives a
strictly primitive solution of $|x^2 - d y^2| = p_1^{n_1} \cdots p_r^{n_r}$.

The sign $\pm$ in the source's equation (13) is dropped; negation preserves both conclusions.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 3(a)
(`integers-2024-A111-prop-3`). -/
theorem strictlyPrimitive_prod (d : ℤ) (hd : 1 < d) (hsq : Squarefree d) {r : ℕ}
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (n : Fin r → ℕ)
    (a : Fin r → ℤ√d) (ha : ∀ i, IsCoprime (a i).re (d * (a i).im))
    (hN : ∀ i, |(a i).norm| = (p i : ℤ) ^ n i) :
    IsCoprime (∏ i, a i).re (d * (∏ i, a i).im) ∧ |(∏ i, a i).norm| = ∏ i, (p i : ℤ) ^ n i := by
  suffices ∀ s : Finset (Fin r), IsCoprime (∏ i ∈ s, a i).re (d * (∏ i ∈ s, a i).im) ∧
      |(∏ i ∈ s, a i).norm| = ∏ i ∈ s, (p i : ℤ) ^ n i from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp [isCoprime_one_left]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Zsqrtd.norm_mul, abs_mul, hN, ih.2]
    refine ⟨strictlyPrimitive_mul_of_coprime_norms (ha i) ih.1 ?_, rfl⟩
    rw [← IsCoprime.abs_abs_iff, hN, ih.2]
    refine IsCoprime.prod_right fun j hj ↦ IsCoprime.pow ?_
    exact ((Nat.coprime_primes (hp i) (hp j)).mpr (hinj.ne fun h ↦ hi (h ▸ hj))).isCoprime
open Classical in
/-- **Second coordinate of the fundamental negative Pell solution.** For a natural number $d$,
$Y$ is the least positive integer $y$ such that $x^2 - d y^2 = -1$ for some integer $x$, and
$Y = 0$ when there is no such $y$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)-(24)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellFundY (d : ℕ) : ℕ :=
  if h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2 then Nat.find h else 0

/-- **First coordinate of the fundamental negative Pell solution.** For a natural number $d$, let
$Y$ be the least positive integer $y$ such that $x^2 - d y^2 = -1$ for some integer $x$, or $0$
if there is no such $y$. Then $X = \lfloor \sqrt{d Y^2 - 1} \rfloor$, where $d Y^2 - 1$ is read
as $0$ when $d Y^2 = 0$. So $X$ is the nonnegative integer with $X^2 - d Y^2 = -1$ when a solution
exists, and $X = 0$ otherwise.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)-(24)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellFundX (d : ℕ) : ℕ :=
  Nat.sqrt (d * negPellFundY d ^ 2 - 1)

open Classical in
/-- **The fundamental negative Pell solution solves the equation.** Let $d$ be a natural number
such that $x^2 - d y^2 = -1$ has a solution in a natural number $x$ and a positive integer $y$.
Then the fundamental solution $(X, Y)$, the one with the least positive $y$, satisfies $Y > 0$
and $X^2 + 1 = d Y^2$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (24)
(`integers-2024-A111-prop-5`). -/
theorem negPellFund_spec {d : ℕ} (h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2) :
    0 < negPellFundY d ∧ negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2 := by
  have hY : negPellFundY d = Nat.find h := by simp [negPellFundY, h]
  obtain ⟨hpos, x, hx⟩ := Nat.find_spec h
  rw [← hY] at hpos hx
  refine ⟨hpos, ?_⟩
  have : d * negPellFundY d ^ 2 - 1 = x ^ 2 := by omega
  simp only [negPellFundX, this, Nat.sqrt_eq']
  exact hx

open Classical in
/-- **Minimality of the fundamental negative Pell solution.** Let $d$ be a natural number and let
$Y$ be the second coordinate of its fundamental negative Pell solution. If $y$ is a positive
integer such that $x^2 - d y^2 = -1$ for some natural number $x$, then $Y \le y$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (24)
(`integers-2024-A111-prop-5`). -/
theorem negPellFundY_le {d y : ℕ} (hy : 0 < y) (hx : ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2) :
    negPellFundY d ≤ y := by
  have h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2 := ⟨y, hy, hx⟩
  have hY : negPellFundY d = Nat.find h := by simp [negPellFundY, h]
  rw [hY]
  exact Nat.find_min' h ⟨hy, hx⟩

open Classical in
/-- **The fundamental solution of the negative Pell equation for d = 2.** The least positive
integer $y$ such that $x^2 - 2 y^2 = -1$ for some integer $x$ is $Y = 1$, and the corresponding
first coordinate is $X = 1$; that is, the fundamental solution for $d = 2$ is $(1, 1)$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)-(24)
(`integers-2024-A111-prop-5`). -/
theorem negPellFund_two : negPellFundY 2 = 1 ∧ negPellFundX 2 = 1 := by
  have h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = 2 * y ^ 2 := ⟨1, by norm_num, 1, by norm_num⟩
  have hY : negPellFundY 2 = 1 := by
    simp only [negPellFundY, h, dite_true]
    rw [Nat.find_eq_iff]
    exact ⟨⟨by norm_num, 1, by norm_num⟩, fun n hn ⟨hn0, _⟩ => by omega⟩
  refine ⟨hY, ?_⟩
  simp [negPellFundX, hY]

/-- **First coordinates of the powers of the fundamental negative Pell solution.** For a natural
number $d$, let $Y$ be the least positive integer $y$ such that $x^2 - d y^2 = -1$ for some
integer $x$, let $X$ be the nonnegative integer with $X^2 - d Y^2 = -1$, and set $X = Y = 0$
when there is no such $y$. In the ring $\mathbb{Z}[\sqrt{d}]$ of formal expressions
$a + b \sqrt{d}$ with $a, b \in \mathbb{Z}$ and $(\sqrt{d})^2 = d$, put
$\varepsilon = X + Y \sqrt{d}$. For $n \ge 0$, $f_n$ is the integer such that
$\varepsilon^n = f_n + g_n \sqrt{d}$ for some integer $g_n$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellF (d n : ℕ) : ℤ :=
  ((⟨negPellFundX d, negPellFundY d⟩ : ℤ√(d : ℤ)) ^ n).re

/-- **Second coordinates of the powers of the fundamental negative Pell solution.** For a natural
number $d$, let $Y$ be the least positive integer $y$ such that $x^2 - d y^2 = -1$ for some
integer $x$, let $X$ be the nonnegative integer with $X^2 - d Y^2 = -1$, and set $X = Y = 0$
when there is no such $y$. In the ring $\mathbb{Z}[\sqrt{d}]$ of formal expressions
$a + b \sqrt{d}$ with $a, b \in \mathbb{Z}$ and $(\sqrt{d})^2 = d$, put
$\varepsilon = X + Y \sqrt{d}$. For $n \ge 0$, $g_n$ is the integer such that
$\varepsilon^n = f_n + g_n \sqrt{d}$ for some integer $f_n$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellG (d n : ℕ) : ℤ :=
  ((⟨negPellFundX d, negPellFundY d⟩ : ℤ√(d : ℤ)) ^ n).im

/-- **Initial values of the negative Pell sequences.** For every natural number $d$, the
sequences $f_n$ and $g_n$ of the negative Pell equation $x^2 - d y^2 = -1$ satisfy $f_0 = 1$ and
$g_0 = 0$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
@[simp]
theorem negPellF_zero_negPellG_zero (d : ℕ) : negPellF d 0 = 1 ∧ negPellG d 0 = 0 := by
  simp [negPellF, negPellG]

/-- **Recurrence for the negative Pell sequences.** Let $d$ be a natural number, let $(X, Y)$ be the
solution of $x^2 - d y^2 = -1$ in natural numbers with least positive $Y$ (with $X = Y = 0$ if
there is none), and define integers $f_n, g_n$ by $(X + Y\sqrt{d})^n = f_n + g_n\sqrt{d}$,
computed formally with $(\sqrt{d})^2 = d$. Then for every $n \ge 0$,
$$f_{n+1} = f_n X + d g_n Y, \qquad g_{n+1} = f_n Y + g_n X.$$

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
theorem negPell_succ (d n : ℕ) :
    negPellF d (n + 1) = negPellF d n * negPellFundX d + d * negPellG d n * negPellFundY d ∧
      negPellG d (n + 1) = negPellF d n * negPellFundY d + negPellG d n * negPellFundX d := by
  simp [negPellF, negPellG, pow_succ]

/-- **Addition of indices in the negative Pell sequences.** For every natural number $d$ and
natural indices $i, j$, the coordinates of the power at index $i+j$ are obtained by multiplying
those at $i$ and $j$ in $\mathbb{Z}[\sqrt d]$. The identities apply even when the negative Pell
sequences use the zero base because no solution exists.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 6(a), equations (27) and (28). -/
theorem negPell_add (d i j : ℕ) :
    negPellF d (i + j) = negPellF d i * negPellF d j + d * negPellG d i * negPellG d j ∧
      negPellG d (i + j) = negPellF d i * negPellG d j + negPellG d i * negPellF d j := by
  constructor <;> simp only [negPellF, negPellG, pow_add, Zsqrtd.re_mul, Zsqrtd.im_mul]

/-- **The negative Pell sequences for d = 2 at n = 1.** Let $(X, Y)$ be the solution of
$x^2 - 2y^2 = -1$ in natural numbers with the least positive $Y$, and for each $n$ let $f_n$ and
$g_n$ be the integers with $(X + Y\sqrt 2)^n = f_n + g_n \sqrt 2$. Then $f_1 = g_1 = 1$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
theorem negPellF_two_one : negPellF 2 1 = 1 ∧ negPellG 2 1 = 1 := by
  simp [negPellF, negPellG, negPellFund_two]

namespace negPellG_le_negPellF

private theorem fund_spec {d : ℕ} (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) :
    0 < negPellFundY d ∧ negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2 := by
  obtain ⟨x, y, hxy⟩ := hneg
  have hy0 : y ≠ 0 := by
    rintro rfl
    have hx : x ^ 2 = -1 := by simpa using hxy
    linarith [sq_nonneg x]
  have h1 : x ^ 2 + 1 = (d : ℤ) * y ^ 2 := by linarith
  have hnat : (x.natAbs : ℤ) ^ 2 + 1 = (d : ℤ) * (y.natAbs : ℤ) ^ 2 := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]
    exact h1
  have hnat' : x.natAbs ^ 2 + 1 = d * y.natAbs ^ 2 := by exact_mod_cast hnat
  exact negPellFund_spec ⟨y.natAbs, Int.natAbs_pos.mpr hy0, x.natAbs, hnat'⟩

/-- The fundamental solution is positive and solves the equation, given an
integral solution. -/
private theorem fund {d : ℕ} (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) :
    0 < negPellFundY d ∧ 0 < negPellFundX d ∧
      negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2 := by
  have hspec := fund_spec hneg
  refine ⟨hspec.1, ?_, hspec.2⟩
  rcases Nat.eq_zero_or_pos (negPellFundX d) with h0 | hpos
  · exfalso
    rw [h0, show (0 : ℕ) ^ 2 + 1 = 1 from by norm_num] at hspec
    have hge : 2 ≤ d * negPellFundY d ^ 2 :=
      calc 2 = 2 * 1 := by norm_num
      _ ≤ d * negPellFundY d ^ 2 :=
        Nat.mul_le_mul (by omega : 2 ≤ d)
          ((Nat.succ_le_of_lt hspec.1).trans (Nat.le_self_pow two_ne_zero _))
    omega
  · exact hpos

/-- The negative Pell sequences are nonnegative. -/
private theorem nonneg (d n : ℕ) : 0 ≤ negPellF d n ∧ 0 ≤ negPellG d n := by
  induction n with
  | zero => simp [negPellF_zero_negPellG_zero]
  | succ n ih =>
    obtain ⟨hF, hG⟩ := negPell_succ d n
    rw [hF, hG]
    refine ⟨?_, ?_⟩
    · exact add_nonneg (mul_nonneg ih.1 (Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ih.2) (Nat.cast_nonneg _))
    · exact add_nonneg (mul_nonneg ih.1 (Nat.cast_nonneg _))
        (mul_nonneg ih.2 (Nat.cast_nonneg _))

/-- The norm identity for the negative Pell sequences. -/
private theorem norm {d : ℕ}
    (hX : negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2) (n : ℕ) :
    negPellF d n ^ 2 - d * negPellG d n ^ 2 = (-1) ^ n := by
  set ε : ℤ√(d : ℤ) := ⟨negPellFundX d, negPellFundY d⟩ with hε
  have hnormε : ε.norm = -1 := by
    rw [hε, Zsqrtd.norm_def]
    have hcast : (negPellFundX d : ℤ) ^ 2 + 1 =
        (d : ℤ) * (negPellFundY d : ℤ) ^ 2 := by
      exact_mod_cast hX
    push_cast
    linarith [hcast]
  have hpow : ∀ m : ℕ, (ε ^ m).norm = (-1 : ℤ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Zsqrtd.norm_mul, ih, hnormε]; ring
  have h := hpow n
  rw [Zsqrtd.norm_def] at h
  simp only [negPellF, negPellG, hε] at h ⊢
  rw [← h]
  ring

/-- From index `2` on, the first coordinates are at least `3`. -/
private theorem growth {d : ℕ} (hd : 1 < d)
    (hfund : 0 < negPellFundY d ∧ 0 < negPellFundX d ∧
      negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2) (n : ℕ) (hn : 2 ≤ n) :
    3 ≤ negPellF d n := by
  obtain ⟨hY, hX, hXeq⟩ := hfund
  have hbase : 3 ≤ negPellF d 2 := by
    have h1 := negPell_succ d 1
    have hf1 : negPellF d 1 = (negPellFundX d : ℤ) := by
      simpa using (negPell_succ d 0).1
    have hg1 : negPellG d 1 = (negPellFundY d : ℤ) := by
      simpa using (negPell_succ d 0).2
    rw [h1.1, hf1, hg1]
    have hcast : (negPellFundX d : ℤ) ^ 2 + 1 =
        (d : ℤ) * (negPellFundY d : ℤ) ^ 2 := by
      exact_mod_cast hXeq
    have hY1 : (1 : ℤ) ≤ (negPellFundY d : ℤ) := by exact_mod_cast hY
    have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    nlinarith [hcast, hY1, hd2, sq_nonneg (negPellFundY d : ℤ),
      mul_nonneg (show (0 : ℤ) ≤ (d : ℤ) - 2 by linarith)
        (show (0 : ℤ) ≤ (negPellFundY d : ℤ) ^ 2 - 1 by nlinarith)]
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ m _ ih =>
    have hrec := (negPell_succ d m).1
    rw [hrec]
    have hX1 : (1 : ℤ) ≤ (negPellFundX d : ℤ) := by exact_mod_cast hX
    have hterm : 0 ≤ (d : ℤ) * negPellG d m * negPellFundY d :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (nonneg d m).2) (Nat.cast_nonneg _)
    calc (3 : ℤ) ≤ negPellF d m := ih
    _ = negPellF d m * 1 := (mul_one _).symm
    _ ≤ negPellF d m * negPellFundX d :=
        mul_le_mul_of_nonneg_left hX1 (nonneg d m).1
    _ ≤ negPellF d m * negPellFundX d + (d : ℤ) * negPellG d m * negPellFundY d := by
        linarith [hterm]

end negPellG_le_negPellF

/-- **Signed norm of a negative Pell power.** If $d$ is a natural number and
$x^2 - d y^2 = -1$ has an integer solution, the coordinates of the $n$-th power of the
fundamental solution satisfy $f_n^2 - d g_n^2 = (-1)^n$ for every natural number $n$.
The fundamental solution has the least positive second coordinate and a nonnegative first
coordinate. The identity also holds at $d = 1$, where the fundamental solution is $(0, 1)$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, equation (24). -/
theorem negPell_norm_of_solvable (d : ℕ)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (n : ℕ) :
    negPellF d n ^ 2 - d * negPellG d n ^ 2 = (-1) ^ n :=
  negPellG_le_negPellF.norm (negPellG_le_negPellF.fund_spec hneg).2 n

/-- **Comparison of the negative Pell sequences.** Let $d > 1$ be a natural number such that
$x^2 - d y^2 = -1$ has an integer solution, let $(X, Y)$ be its fundamental solution (the one with
$X, Y > 0$ and $Y$ least), and write $(X + Y \sqrt{d})^n = f_n + g_n \sqrt{d}$. Then for every
$n \ge 0$, $g_n \le f_n$, with equality if and only if $d = 2$ and $n = 1$.

Only the first sentence of the source's corollary is stated here: its second sentence, printed as
$f_1 \ge d - 1$ with a displaced square root sign, fails when read literally at $d = 5$, where
$f_1 = 2$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Corollary 2, first sentence
(`integers-2024-A111-cor-2`). -/
theorem negPellG_le_negPellF (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (n : ℕ) :
    negPellG d n ≤ negPellF d n ∧ (negPellF d n = negPellG d n ↔ d = 2 ∧ n = 1) := by
  have hfund := negPellG_le_negPellF.fund hd hneg
  have hnonneg := fun m => negPellG_le_negPellF.nonneg d m
  have hnorm := negPellG_le_negPellF.norm hfund.2.2
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hpow : (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
    rcases Nat.even_or_odd n with h | h
    · left; exact Even.neg_one_pow h
    · right; exact Odd.neg_one_pow h
  constructor
  · by_contra hlt
    push Not at hlt
    have hn := hnorm n
    rcases hpow with h | h <;> rw [h] at hn <;>
      nlinarith [hn, hnonneg n, hlt, hd2, sq_nonneg (negPellF d n),
        sq_nonneg (negPellG d n),
        mul_nonneg (show (0 : ℤ) ≤ negPellG d n - negPellF d n - 1 by omega)
          (show (0 : ℤ) ≤ negPellG d n + negPellF d n by linarith [hnonneg n]),
        mul_nonneg (show (0 : ℤ) ≤ (d : ℤ) - 2 by linarith)
          (sq_nonneg (negPellG d n))]
  · constructor
    · intro heq
      have hnormn := hnorm n
      rw [← heq] at hnormn
      have hF0 : negPellF d n ≠ 0 := by
        intro h0
        rw [h0] at hnormn
        rcases hpow with h | h <;> rw [h] at hnormn <;> norm_num at hnormn
      have hprod : ((d : ℤ) - 1) * negPellF d n ^ 2 = 1 := by
        rcases hpow with h | h <;> rw [h] at hnormn <;>
          nlinarith [hnormn, hd2, sq_nonneg (negPellF d n)]
      have hF2 : (1 : ℤ) ≤ negPellF d n ^ 2 := by
        have hpos : 0 < negPellF d n ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hF0))
        omega
      have hdle : (d : ℤ) ≤ 2 := by
        nlinarith [hprod, hF2,
          mul_nonneg (show (0 : ℤ) ≤ (d : ℤ) - 2 by linarith)
            (show (0 : ℤ) ≤ negPellF d n ^ 2 - 1 by linarith)]
      have hd_eq : d = 2 := by
        have hcast : (d : ℤ) = 2 := by omega
        exact_mod_cast hcast
      subst hd_eq
      have hFval : negPellF 2 n = 1 := by
        have hsq1 : negPellF 2 n ^ 2 = 1 := by simpa using hprod
        rcases sq_eq_one_iff.mp hsq1 with h | h
        · exact h
        · linarith [(hnonneg n).1]
      have hn0 : n ≠ 0 := by
        rintro rfl
        have hG0 := (negPellF_zero_negPellG_zero 2).2
        rw [hFval, hG0] at heq
        norm_num at heq
      have hnlt : n < 2 := by
        by_contra hge
        push Not at hge
        have hg := negPellG_le_negPellF.growth (by norm_num : 1 < 2) hfund n hge
        linarith [hg, hFval]
      omega
    · rintro ⟨rfl, rfl⟩
      exact (negPellF_two_one).1.trans (negPellF_two_one).2.symm

end MetaMathlibExt
