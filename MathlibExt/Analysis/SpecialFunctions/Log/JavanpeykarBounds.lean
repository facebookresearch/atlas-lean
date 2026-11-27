/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.NumberTheory.Height.NumberField

/-!
# Elementary inequalities in Javanpeykar's bounds for Belyi curves

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), 89–140, bounds the Faltings height, the discriminant, Faltings' delta invariant
and the self-intersection of the dualising sheaf of a curve over `ℚ̄` polynomially in its Belyi
degree. Besides the Arakelov geometry, the proof combines its estimates through a few elementary
real and rational inequalities. This file proves them, for every value of the parameters:

* `Javanpeykar.half_add_min_le_sub_mul_log_max_one`: Lemma 2.4.3, p. 101;
* `Javanpeykar.numerical_bound_le_ten_mul_cube`: the bound by `10 g ^ 3` in the proof of
  Proposition 2.4.8, p. 103;
* `Javanpeykar.constants_of_the_bounds`: the combination of the constants in the proof of
  Theorem 2.4.1, p. 103, for `g ≥ 2`;
* `Javanpeykar.smallRational` and `Javanpeykar.smallRational_spec`: the rational numbers `aₙ` of
  the proof of Theorem 4.5.2, p. 122;
* `Javanpeykar.three_mul_log_two_mul_sq_mul_sq_le`: the inequality
  `3 log(2 d²) d² ≤ 2 d⁵ / g` of the proof of Theorem 4.5.2, p. 123;
* `Javanpeykar.constants_of_theorem_1_1_1`: the five constants of Theorem 1.1.1, p. 90, from the
  proof in §4.6, p. 123.

The naive height of a rational number is Mathlib's `Height.logHeight₁`, which on `ℚ` is
`log max(|p|, q)` for `p / q` in lowest terms (`Rat.logHeight₁_eq_log_max`).
-/

@[expose] public section

namespace Javanpeykar

open Real

/-- `log (2π) < 2`, from `π < 3.15` and `e > 2.7182818283`. -/
theorem log_two_mul_pi_lt_two : Real.log (2 * π) < 2 := by
  have hpi : π < 3.15 := Real.pi_lt_d2
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [Real.log_lt_iff_lt_exp (by positivity), h2]
  nlinarith

/-- **Javanpeykar, Lemma 2.4.3.** Let `a > 0` and `b ≤ 1` be real numbers. Then for every real
number `x ≥ b`,
`x - a log max(1, x) ≥ x / 2 + min(b / 2, a - a log(2a))`.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), Lemma 2.4.3, p. 101. The proof here does not use `b ≤ 1`. -/
theorem half_add_min_le_sub_mul_log_max_one {a b : ℝ} (ha : 0 < a) (_hb : b ≤ 1) {x : ℝ}
    (hx : b ≤ x) :
    x / 2 + min (b / 2) (a - a * Real.log (2 * a)) ≤ x - a * Real.log (max 1 x) := by
  rcases le_total x 1 with hx1 | hx1
  · rw [max_eq_left hx1, Real.log_one, mul_zero, sub_zero]
    have := min_le_left (b / 2) (a - a * Real.log (2 * a))
    linarith
  · rw [max_eq_right hx1]
    have hx0 : 0 < x := by linarith
    have h2a : 0 < 2 * a := by linarith
    -- `log (x / (2a)) ≤ x / (2a) - 1`, multiplied by `a`.
    have hlog := Real.log_le_sub_one_of_pos (div_pos hx0 h2a)
    rw [Real.log_div hx0.ne' h2a.ne'] at hlog
    have hmul : a * (Real.log x - Real.log (2 * a)) ≤ a * (x / (2 * a) - 1) :=
      mul_le_mul_of_nonneg_left hlog ha.le
    have hsimp : a * (x / (2 * a) - 1) = x / 2 - a := by
      field_simp
    have := min_le_right (b / 2) (a - a * Real.log (2 * a))
    nlinarith

/-- **The numerical bound by `10 g³`.** For every integer `g ≥ 1`,
`(4g³ + 5g + 1) log 2 + max((g / 2) log(2π), (g / 4) log(g / 2) - g / 4) ≤ 10 g³`.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Proposition 2.4.8, p. 103, where it is used for `g ≥ 2`. -/
theorem numerical_bound_le_ten_mul_cube (g : ℕ) (hg : 1 ≤ g) :
    (4 * (g : ℝ) ^ 3 + 5 * g + 1) * Real.log 2 +
        max ((g : ℝ) / 2 * Real.log (2 * π)) ((g : ℝ) / 4 * Real.log ((g : ℝ) / 2) - g / 4) ≤
      10 * (g : ℝ) ^ 3 := by
  have hx : (1 : ℝ) ≤ g := by exact_mod_cast hg
  set x : ℝ := (g : ℝ) with hxdef
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlpi := log_two_mul_pi_lt_two
  have hlog : Real.log (x / 2) ≤ x / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hx3 : x ^ 2 ≤ x ^ 3 := by nlinarith
  have h1 : (4 * x ^ 3 + 5 * x + 1) * Real.log 2 ≤ (4 * x ^ 3 + 5 * x + 1) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hl2.le (by positivity)
  have hm1 : x / 2 * Real.log (2 * π) ≤ x := by nlinarith
  have hm2 : x / 4 * Real.log (x / 2) - x / 4 ≤ x ^ 3 := by
    have : x / 4 * Real.log (x / 2) ≤ x / 4 * (x / 2 - 1) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    nlinarith
  have hm : max (x / 2 * Real.log (2 * π)) (x / 4 * Real.log (x / 2) - x / 4) ≤ x ^ 3 :=
    max_le (by linarith) hm2
  nlinarith

/-- **The constants of the bounds by a non-Weierstrass point.** Let `g ≥ 2` be an integer and
`e, δ, Δ, h_F, h, w` real numbers such that `e ≤ 4g(g - 1) h`,
`-g log(2π) ≤ (2g - 1)(g + 1) / (4(g - 1)) e + δ / 4 + 20 g³`,
`12 h_F = e + Δ + δ - 4g log(2π)`, `e ≥ 0`, `Δ ≥ 0` and `h_F ≤ g(g + 1) h / 2 + w`. Then
`δ ≥ -90 g³ - 4g(2g - 1)(g + 1) h`, `δ ≤ 6g(g + 1) h + 12 w + 4g log(2π)` and
`Δ ≤ 2g(g + 1)(4g + 1) h + 12 w + 93 g³`.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Theorem 2.4.1, p. 103, combining Proposition 2.4.8 (p. 102), Faltings'
bounds for `e`, the Noether formula (Lemma 2.4.7, p. 102) and the bound for `h_F` by `h(b)` and
`log ‖Wr‖_Ar(b)`. -/
theorem constants_of_the_bounds (g : ℕ) (hg : 2 ≤ g) (e δ Δ hF h w : ℝ)
    (he_le : e ≤ 4 * g * (g - 1) * h)
    (hlow : -((g : ℝ) * Real.log (2 * π)) ≤
      (2 * g - 1) * (g + 1) / (4 * (g - 1)) * e + 1 / 4 * δ + 20 * (g : ℝ) ^ 3)
    (hnoether : 12 * hF = e + Δ + δ - 4 * g * Real.log (2 * π))
    (he : 0 ≤ e) (hΔ : 0 ≤ Δ) (hhF : hF ≤ 1 / 2 * g * (g + 1) * h + w) :
    -90 * (g : ℝ) ^ 3 - 4 * g * (2 * g - 1) * (g + 1) * h ≤ δ ∧
      δ ≤ 6 * g * (g + 1) * h + 12 * w + 4 * g * Real.log (2 * π) ∧
      Δ ≤ 2 * g * (g + 1) * (4 * g + 1) * h + 12 * w + 93 * (g : ℝ) ^ 3 := by
  have hG : (2 : ℝ) ≤ g := by exact_mod_cast hg
  set G : ℝ := (g : ℝ) with hGdef
  have hlpi := log_two_mul_pi_lt_two
  have hG1 : 0 < G - 1 := by linarith
  have hc : 0 ≤ (2 * G - 1) * (G + 1) / (4 * (G - 1)) := by
    apply div_nonneg <;> nlinarith
  have hce : (2 * G - 1) * (G + 1) / (4 * (G - 1)) * e ≤
      (2 * G - 1) * (G + 1) / (4 * (G - 1)) * (4 * G * (G - 1) * h) :=
    mul_le_mul_of_nonneg_left he_le hc
  have hceq : (2 * G - 1) * (G + 1) / (4 * (G - 1)) * (4 * G * (G - 1) * h) =
      G * (2 * G - 1) * (G + 1) * h := by
    field_simp
  have hGlog : 4 * G * Real.log (2 * π) ≤ 8 * G := by nlinarith
  have hG2 : 4 ≤ G ^ 2 := by nlinarith
  have hcube : 8 * G ≤ 3 * G ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hG2 (by linarith : (0 : ℝ) ≤ G)]
  have hlow' : -90 * G ^ 3 - 4 * G * (2 * G - 1) * (G + 1) * h ≤ δ := by
    nlinarith
  refine ⟨hlow', ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- The rational numbers of the proof of Javanpeykar's Theorem 4.5.2: `a₁ = 1 / 2` and
`aₙ = n / (2n - 1)` for `n ≥ 2` (the value at `n = 0` is irrelevant).

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Theorem 4.5.2, p. 122. -/
def smallRational (n : ℕ) : ℚ :=
  if n = 1 then 1 / 2 else (n : ℚ) / (2 * (n : ℚ) - 1)

/-- `a₁ = 1 / 2`. -/
theorem smallRational_one : smallRational 1 = 1 / 2 := by
  simp [smallRational]

/-- `aₙ = n / (2n - 1)` for `n ≥ 2`. -/
theorem smallRational_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    smallRational n = (n : ℚ) / (2 * (n : ℚ) - 1) := by
  simp [smallRational, show n ≠ 1 by omega]

/-- For `n ≥ 2`, `n / (2n - 1)` is in lowest terms: its numerator is `n`. -/
theorem smallRational_num_of_two_le {n : ℕ} (hn : 2 ≤ n) : (smallRational n).num = n := by
  rw [smallRational_of_two_le hn]
  have hcop : (n : ℤ).natAbs.Coprime (2 * (n : ℤ) - 1).natAbs := by
    have h : IsCoprime (n : ℤ) (2 * (n : ℤ) - 1) := ⟨2, -1, by ring⟩
    exact Int.isCoprime_iff_gcd_eq_one.mp h
  have hpos : (0 : ℤ) < 2 * (n : ℤ) - 1 := by omega
  have := Rat.num_div_eq_of_coprime hpos hcop
  push_cast at this
  exact this

/-- For `n ≥ 2`, `n / (2n - 1)` is in lowest terms: its denominator is `2n - 1`. -/
theorem smallRational_den_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    ((smallRational n).den : ℤ) = 2 * (n : ℤ) - 1 := by
  rw [smallRational_of_two_le hn]
  have hcop : (n : ℤ).natAbs.Coprime (2 * (n : ℤ) - 1).natAbs := by
    have h : IsCoprime (n : ℤ) (2 * (n : ℤ) - 1) := ⟨2, -1, by ring⟩
    exact Int.isCoprime_iff_gcd_eq_one.mp h
  have hpos : (0 : ℤ) < 2 * (n : ℤ) - 1 := by omega
  have := Rat.den_div_eq_of_coprime hpos hcop
  push_cast at this
  exact this

/-- `1 / 2 ≤ aₙ ≤ 2 / 3` for `n ≥ 1`. -/
theorem smallRational_mem_Icc {n : ℕ} (hn : 1 ≤ n) :
    1 / 2 ≤ smallRational n ∧ smallRational n ≤ 2 / 3 := by
  rcases eq_or_lt_of_le hn with rfl | hn2
  · rw [smallRational_one]; norm_num
  · rw [smallRational_of_two_le hn2]
    have hq : (2 : ℚ) ≤ n := by exact_mod_cast hn2
    have hd : (0 : ℚ) < 2 * n - 1 := by linarith
    constructor
    · rw [le_div_iff₀ hd]; linarith
    · rw [div_le_iff₀ hd]; linarith

/-- `h_naive(aₙ) ≤ log(2n)` for `n ≥ 1`. -/
theorem logHeight₁_smallRational_le {n : ℕ} (hn : 1 ≤ n) :
    Height.logHeight₁ (smallRational n) ≤ Real.log (2 * n) := by
  rw [Rat.logHeight₁_eq_log_max]
  have hmax : max (smallRational n).num.natAbs (smallRational n).den ≤ 2 * n := by
    rcases eq_or_lt_of_le hn with rfl | hn2
    · rw [smallRational_one]
      have h1 : ((1 / 2 : ℚ)).num = 1 := by norm_num
      have h2 : ((1 / 2 : ℚ)).den = 2 := by norm_num
      rw [h1, h2]; decide
    · have hnum := smallRational_num_of_two_le hn2
      have hden := smallRational_den_of_two_le hn2
      rw [hnum, Int.natAbs_natCast]
      apply max_le (by omega)
      omega
  have hpos : (0 : ℝ) < (max (smallRational n).num.natAbs (smallRational n).den : ℕ) := by
    have := (smallRational n).den_pos
    exact_mod_cast lt_of_lt_of_le this (le_max_right _ _)
  apply Real.log_le_log hpos
  exact_mod_cast hmax

/-- The `aₙ` with `n ≥ 1` are pairwise distinct. -/
theorem smallRational_injOn : Set.InjOn smallRational (Set.Ici 1) := by
  intro m hm n hn hmn
  simp only [Set.mem_Ici] at hm hn
  have key : ∀ k : ℕ, 2 ≤ k → smallRational k ≠ 1 / 2 := by
    intro k hk h
    rw [smallRational_of_two_le hk] at h
    have hq : (2 : ℚ) ≤ k := by exact_mod_cast hk
    have hd : (2 * (k : ℚ) - 1) ≠ 0 := by linarith
    rw [div_eq_div_iff hd (by norm_num)] at h
    linarith
  rcases eq_or_lt_of_le hm with rfl | hm2 <;> rcases eq_or_lt_of_le hn with rfl | hn2
  · rfl
  · exact absurd (smallRational_one ▸ hmn).symm (key n hn2)
  · exact absurd (smallRational_one ▸ hmn) (key m hm2)
  · rw [smallRational_of_two_le hm2, smallRational_of_two_le hn2] at hmn
    have hqm : (2 : ℚ) ≤ m := by exact_mod_cast hm2
    have hqn : (2 : ℚ) ≤ n := by exact_mod_cast hn2
    have hdm : (2 * (m : ℚ) - 1) ≠ 0 := by linarith
    have hdn : (2 * (n : ℚ) - 1) ≠ 0 := by linarith
    rw [div_eq_div_iff hdm hdn] at hmn
    have : (m : ℚ) = n := by linarith
    exact_mod_cast this

/-- **The rational numbers `aₙ`.** Let `a₁ = 1 / 2` and `aₙ = n / (2n - 1)` for `n ≥ 2`. Then for
every `n ≥ 1`, `1 / 2 ≤ aₙ ≤ 2 / 3` and `h_naive(aₙ) ≤ log(2n)`, where
`h_naive(p / q) = log max(|p|, |q|)` for coprime integers `p, q` with `q > 0` (here
`Height.logHeight₁`, see `Rat.logHeight₁_eq_log_max`). Moreover the `aₙ` are pairwise distinct.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Theorem 4.5.2, p. 122, with `h_naive` as defined before
Theorem 4.5.1, p. 120. -/
theorem smallRational_spec :
    (∀ n : ℕ, 1 ≤ n → 1 / 2 ≤ smallRational n ∧ smallRational n ≤ 2 / 3 ∧
      Height.logHeight₁ (smallRational n) ≤ Real.log (2 * n)) ∧
    Set.InjOn smallRational (Set.Ici 1) :=
  ⟨fun _ hn => ⟨(smallRational_mem_Icc hn).1, (smallRational_mem_Icc hn).2,
    logHeight₁_smallRational_le hn⟩, smallRational_injOn⟩

/-- **The inequality for the height bound.** Let `d ≥ 2` and `1 ≤ g ≤ d` be integers. Then
`3 log(2 d²) d² ≤ 2 d⁵ / g`.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Theorem 4.5.2, p. 123, with `d = deg π`. -/
theorem three_mul_log_two_mul_sq_mul_sq_le (d g : ℕ) (hd : 2 ≤ d) (hg : 1 ≤ g) (hgd : g ≤ d) :
    3 * Real.log (2 * (d : ℝ) ^ 2) * (d : ℝ) ^ 2 ≤ 2 * (d : ℝ) ^ 5 / g := by
  have hD : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hG : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hGD : (g : ℝ) ≤ d := by exact_mod_cast hgd
  set D : ℝ := (d : ℝ) with hDdef
  set G : ℝ := (g : ℝ) with hGdef
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- `log (2 D²) = 3 log 2 + 2 log (D / 2) ≤ 3 log 2 + D - 2`.
  have hsplit : 2 * D ^ 2 = 2 ^ 3 * (D / 2) ^ 2 := by ring
  have hlog : Real.log (2 * D ^ 2) = 3 * Real.log 2 + 2 * Real.log (D / 2) := by
    rw [hsplit, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hhalf : Real.log (D / 2) ≤ D / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hle : 3 * Real.log (2 * D ^ 2) ≤ 2 * D ^ 2 := by
    rw [hlog]; nlinarith
  have h4 : 3 * Real.log (2 * D ^ 2) * D ^ 2 ≤ 2 * D ^ 4 := by
    have := mul_le_mul_of_nonneg_right hle (sq_nonneg D)
    nlinarith
  have h5 : 2 * D ^ 4 ≤ 2 * D ^ 5 / G := by
    rw [le_div_iff₀ (by positivity)]
    have : 0 ≤ D ^ 4 := by positivity
    nlinarith
  linarith

/-- **The constants of Javanpeykar's Theorem 1.1.1.** Let `1 ≤ g ≤ d` be integers and `h, w`
real numbers with `h ≤ 6378033 d⁵ / g` and `w ≤ 6378028 g d⁵`. Then
`4g(g - 1) h ≤ 3 · 10⁷ (g - 1) d⁵`,
`2g(g + 1)(4g + 1) h + 12 w + 93 g³ ≤ 5 · 10⁸ g² d⁵`,
`-90 g³ - 4g(2g - 1)(g + 1) h ≥ -10⁸ g² d⁵`,
`6g(g + 1) h + 12 w + 4g log(2π) ≤ 2 · 10⁸ g d⁵` and
`g(g + 1) h / 2 + w ≤ 13 · 10⁶ g d⁵`.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), Theorem 1.1.1, p. 90, and its proof in §4.6, p. 123, with `d = deg_B(X)`,
`h = h(b)` and `w = log ‖Wr‖_Ar(b)` substituted into the bounds of Theorem 2.4.1, pp. 99–100. -/
theorem constants_of_theorem_1_1_1 (g d : ℕ) (hg : 1 ≤ g) (hgd : g ≤ d) (h w : ℝ)
    (hh : h ≤ 6378033 * (d : ℝ) ^ 5 / g) (hw : w ≤ 6378028 * g * (d : ℝ) ^ 5) :
    4 * g * (g - 1) * h ≤ 3 * 10 ^ 7 * (g - 1) * (d : ℝ) ^ 5 ∧
      2 * g * (g + 1) * (4 * g + 1) * h + 12 * w + 93 * (g : ℝ) ^ 3 ≤
        5 * 10 ^ 8 * (g : ℝ) ^ 2 * (d : ℝ) ^ 5 ∧
      -(10 : ℝ) ^ 8 * (g : ℝ) ^ 2 * (d : ℝ) ^ 5 ≤
        -90 * (g : ℝ) ^ 3 - 4 * g * (2 * g - 1) * (g + 1) * h ∧
      6 * g * (g + 1) * h + 12 * w + 4 * g * Real.log (2 * π) ≤
        2 * 10 ^ 8 * g * (d : ℝ) ^ 5 ∧
      1 / 2 * g * (g + 1) * h + w ≤ 13 * 10 ^ 6 * g * (d : ℝ) ^ 5 := by
  have hG : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hGd : (g : ℝ) ≤ d := by exact_mod_cast hgd
  have hlpi := log_two_mul_pi_lt_two
  have hlpi0 : 0 < Real.log (2 * π) :=
    Real.log_pos (by nlinarith [Real.pi_gt_three])
  set G : ℝ := (g : ℝ) with hGdef
  have hd1 : (1 : ℝ) ≤ d := le_trans hG hGd
  -- `D = d⁵ ≥ d ≥ g`.
  have hDd : (d : ℝ) ≤ (d : ℝ) ^ 5 := by
    have : (d : ℝ) ^ 1 ≤ (d : ℝ) ^ 5 := pow_le_pow_right₀ hd1 (by norm_num)
    simpa using this
  set D : ℝ := (d : ℝ) ^ 5 with hDdef
  have hGD : G ≤ D := le_trans hGd hDd
  have hD0 : 0 ≤ D := by linarith
  -- `G h ≤ 6378033 D`.
  have hGh : G * h ≤ 6378033 * D := by
    have := mul_le_mul_of_nonneg_left hh (by linarith : (0 : ℝ) ≤ G)
    rwa [mul_div_cancel₀ _ (by linarith : G ≠ 0)] at this
  have hG1 : 0 ≤ G - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `4G(G - 1)h = 4(G - 1)(Gh) ≤ 25512132 (G - 1) D`.
    have h1 := mul_le_mul_of_nonneg_left hGh hG1
    nlinarith [mul_nonneg hG1 hD0]
  · have h1 := mul_le_mul_of_nonneg_left hGh (by positivity : (0 : ℝ) ≤ 2 * (G + 1) * (4 * G + 1))
    have h2 : 0 ≤ (6 * G + 1) * (G - 1) * D := by positivity
    have h3 : 0 ≤ G * (G - 1) * D := by positivity
    have h4 : 0 ≤ G ^ 2 * (D - G) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hGh (by nlinarith : (0 : ℝ) ≤ 4 * (2 * G - 1) * (G + 1))
    have h2 : 0 ≤ (G + 1) * (G - 1) * D := by positivity
    have h4 : 0 ≤ G ^ 2 * (D - G) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hGh (by positivity : (0 : ℝ) ≤ 6 * (G + 1))
    have h2 : 0 ≤ (G - 1) * D := by positivity
    have h3 : 0 ≤ G * (D - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hGh (by positivity : (0 : ℝ) ≤ 1 / 2 * (G + 1))
    have h2 : 0 ≤ (G - 1) * D := by positivity
    nlinarith

end Javanpeykar
