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

Squares are `0` or `1` modulo `4`, so for `d ≡ 1 (mod 4)` the value
`x² - d y²` is `0`, `1`, or `3` modulo `4`, and so is its negation.
Modulo `8`, squares are `0`, `1`, or `4`. If `x² ≡ 5 y² (mod 8)`, both squares are even.

Multiplying `x + y √d` by a solution `a + b √d` of `a² - d b² = -1` negates the value of
`x² - d y²` and keeps the first coordinate coprime to `d` times the second, so strictly primitive
solutions of `x² - d y² = z` give strictly primitive solutions of `x² - d y² = -z`.
Products of strictly primitive solutions whose absolute norms are powers of distinct primes
are strictly primitive as well.
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

end MetaMathlibExt
