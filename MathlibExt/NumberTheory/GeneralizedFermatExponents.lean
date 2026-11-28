/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Generalized Fermat equations with exponents 3s, 6t and 2w

We define solvability in nonzero integers and classify when the equation with exponents
`3 * s`, `6 * t` and `2 * w` has solutions, proving infinitude in the solvable cases.
-/

namespace MetaMathlibExt

/-- **Solvable generalized Fermat equation.** For natural numbers $m$, $n$, $r$, the equation
$x^m + y^n = z^r$ is called solvable when there are nonzero integers $x$, $y$, $z$ with
$x^m + y^n = z^r$.

Source: Richard F. Ryan, *Under What Conditions on the Exponents Does `x^m + y^n = z^r` Have
Solutions?*, INTEGERS 24 (2024), Article A48, Section 1, equation (1). -/
@[expose] public def GeneralizedFermatSolvable (m n r : ℕ) : Prop :=
  ∃ x y z : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ^ m + y ^ n = z ^ r

namespace generalizedFermat_three_six_two_mul

private theorem val_add_eq_left {p : ℕ} [Fact p.Prime] {x y : ℚ} (hx : x ≠ 0)
    (h : y ≠ 0 → padicValRat p x < padicValRat p y) :
    x + y ≠ 0 ∧ padicValRat p (x + y) = padicValRat p x := by
  by_cases hy : y = 0
  · simpa [hy] using hx
  have hne : x + y ≠ 0 := by
    intro he
    have hy' : y = -x := by linarith
    simpa [hy'] using h hy
  exact ⟨hne, padicValRat.add_eq_of_lt hne hx hy (h hy)⟩

private theorem val_prime {p q : ℕ} [Fact p.Prime] (hq : q.Prime) :
    padicValRat p (q : ℚ) = if p = q then 1 else 0 := by
  have : Fact q.Prime := ⟨hq⟩
  split_ifs with h
  · subst q
    exact padicValRat.self (Fact.out : p.Prime).one_lt
  · rw [← padicValRat_of_nat, multiplicity_primes h]
    rfl

-- Away from 3, the valuation of the quadratic factor is twice that of x when x has
-- negative valuation, and zero when x has positive valuation.
private theorem val_square_class {x y : ℚ} {a b : ℤ} (hx : x ≠ 0) (hy : y ≠ 0)
    (ha : a ≠ 0) (hb : b = 3 ∨ b = -3)
    (he : y ^ 2 = x * (x ^ 2 + a * x + b)) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    Even (padicValRat p x) := by
  have : Fact p.Prime := ⟨hp⟩
  have hxx := pow_ne_zero 2 hx
  have hb0 : (b : ℚ) ≠ 0 := by rcases hb with rfl | rfl <;> norm_num
  have hq : x ^ 2 + a * x + b ≠ 0 := right_ne_zero_of_mul (he ▸ pow_ne_zero 2 hy)
  have ha' : 0 ≤ padicValRat p (a : ℚ) := by rw [padicValRat.of_int]; positivity
  have hb' : padicValRat p (b : ℚ) = 0 := by
    rcases hb with rfl | rfl <;> simpa [hp3] using val_prime (p := p) Nat.prime_three
  have he' := congrArg (padicValRat p) he
  rw [padicValRat.pow, padicValRat.mul hx hq] at he'
  have hmul := padicValRat.mul (p := p) (by exact_mod_cast ha : (a : ℚ) ≠ 0) hx
  rcases lt_trichotomy (padicValRat p x) 0 with hn | hz | hp'
  · obtain ⟨hn₁, h₁⟩ := val_add_eq_left (p := p) (y := (a : ℚ) * x) hxx (by
      intro _
      rw [padicValRat.pow, hmul]
      omega)
    have h₂ := (val_add_eq_left (p := p) (y := (b : ℚ)) hn₁ (by
      intro _
      rw [h₁, padicValRat.pow, hb']
      omega)).2
    rw [h₂, h₁, padicValRat.pow] at he'
    exact ⟨padicValRat p y - padicValRat p x, by omega⟩
  · simp [hz]
  · obtain ⟨hn₁, h₁⟩ := val_add_eq_left (p := p) (y := (a : ℚ) * x) hb0 (by
      intro _
      rw [hb', hmul]
      omega)
    have h₂ := (val_add_eq_left (p := p) (y := x ^ 2) hn₁ (by
      intro _
      rw [h₁, hb', padicValRat.pow]
      omega)).2
    rw [show x ^ 2 + a * x + b = (b : ℚ) + a * x + x ^ 2 by ring, h₂, h₁, hb'] at he'
    exact ⟨padicValRat p y, by omega⟩

private theorem square_or_three_mul_square {x : ℚ} (hx : 0 < x)
    (h : ∀ p : ℕ, p.Prime → p ≠ 3 → Even (padicValRat p x)) :
    IsSquare x ∨ IsSquare (x / 3) := by
  by_cases h3 : Even (padicValRat 3 x)
  · refine Or.inl (Rat.isSquare_iff_even_factorization.mpr ⟨hx.le, fun p hp ↦ ?_⟩)
    by_cases hp3 : p = 3
    · simpa [hp3] using h3
    · exact h p hp hp3
  · refine Or.inr (Rat.isSquare_iff_even_factorization.mpr ⟨by positivity, fun p hp ↦ ?_⟩)
    have : Fact p.Prime := ⟨hp⟩
    rw [padicValRat.div hx.ne' (by norm_num)]
    change Even (padicValRat p x - padicValRat p ((3 : ℕ) : ℚ))
    rw [val_prime (p := p) Nat.prime_three]
    by_cases hp3 : p = 3
    · subst p
      simp only [ite_true]
      obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp h3
      exact ⟨k, by omega⟩
    · simpa [hp3] using h p hp hp3

-- For a negative square x on the dual curve, reduction modulo 9 would force the
-- numerator and denominator of its square root to share a factor of 3.
private theorem no_negative_square_on_dual {u y : ℚ} (hu : u ≠ 0)
    (he : y ^ 2 = (-u ^ 2) * ((-u ^ 2) ^ 2 + 6 * (-u ^ 2) - 3)) : False := by
  have hrat : IsSquare (((-u.num ^ 4 + 6 * u.num ^ 2 * (u.den : ℤ) ^ 2 +
      3 * (u.den : ℤ) ^ 4 : ℤ) : ℚ)) := by
    refine ⟨y / u * (u.den : ℚ) ^ 2, ?_⟩
    have hden : (u.den : ℚ) ≠ 0 := by exact_mod_cast u.den_nz
    have hu' : (u.num : ℚ) = u * u.den := by
      have hre : (u.num : ℚ) / ((u.den : ℤ) : ℚ) = u := by
        rw [← Rat.divInt_eq_div, Rat.num_divInt_den]
      exact (div_eq_iff hden).mp hre
    push_cast
    rw [hu']
    calc
      _ = (u.den : ℚ) ^ 4 * (-u ^ 4 + 6 * u ^ 2 + 3) := by ring
      _ = (y / u * (u.den : ℚ) ^ 2) * (y / u * (u.den : ℚ) ^ 2) := by
        field_simp
        linear_combination -he
  obtain ⟨c, hc⟩ := Rat.isSquare_intCast_iff.mp hrat
  have hmod : ∀ a b c : ZMod 9, -a ^ 4 + 6 * a ^ 2 * b ^ 2 + 3 * b ^ 4 = c * c →
      3 * a = 0 ∧ 3 * b = 0 := by decide
  have hcast := congrArg (fun n : ℤ ↦ (n : ZMod 9)) hc
  push_cast at hcast
  have h := hmod (u.num : ZMod 9) (u.den : ZMod 9) (c : ZMod 9) hcast
  have hz {n : ℤ} (hn : 3 * (n : ZMod 9) = 0) : (3 : ℤ) ∣ n := by
    have h' : ((3 * n : ℤ) : ZMod 9) = 0 := by simpa only [Int.cast_mul, Int.cast_ofNat] using hn
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
    exact ⟨k, by omega⟩
  have hnum : 3 ∣ u.num.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (hz h.1))
  have hden : 3 ∣ u.den := Int.natCast_dvd_natCast.mp (hz (by exact_mod_cast h.2))
  have := u.reduced.gcd_eq_one
  have hd := Nat.dvd_gcd hnum hden
  rw [this] at hd
  norm_num at hd

private def OnCurve (a b x y : ℚ) : Prop := y ^ 2 = x * (x ^ 2 + a * x + b)

private theorem invert_x {a b x y : ℚ} (hx : x ≠ 0) (he : OnCurve a b x y) :
    OnCurve a b (b / x) (b * y / x ^ 2) := by
  unfold OnCurve at *
  field_simp
  linear_combination b ^ 2 * he

private theorem square_class_dual {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (he : OnCurve 6 (-3) x y) : IsSquare x ∨ IsSquare (x / (-3)) := by
  have hval (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) : Even (padicValRat p x) :=
    val_square_class (a := 6) (b := -3) hx hy (by norm_num) (Or.inr rfl)
      (by simpa [OnCurve, sub_eq_add_neg] using he) hp hp3
  have hneg {r s : ℚ} (hr : r ≠ 0) (hs : IsSquare (-r)) (hE : OnCurve 6 (-3) r s) : False := by
    obtain ⟨u, hu⟩ := hs
    have hru : r = -u ^ 2 := by rw [pow_two]; linarith
    have hu0 : u ≠ 0 := by rintro rfl; simp [hru] at hr
    exact no_negative_square_on_dual hu0 (by simpa [OnCurve, hru, sub_eq_add_neg] using hE)
  rcases hx.lt_or_gt with hn | hp
  · rcases square_or_three_mul_square (neg_pos.mpr hn) (by simpa using hval) with h | h
    · exact (hneg hx h he).elim
    · exact Or.inr (by simpa [div_neg, neg_div] using h)
  · rcases square_or_three_mul_square hp hval with h | ⟨u, hu⟩
    · exact Or.inl h
    have hu0 : u ≠ 0 := by rintro rfl; simp [hx] at hu
    have hxu : x = 3 * u ^ 2 := by
      rw [div_eq_iff (by norm_num : (3 : ℚ) ≠ 0), ← pow_two] at hu
      linarith
    have hh : IsSquare (-((-3 : ℚ) / x)) := by
      refine ⟨u⁻¹, ?_⟩
      rw [hxu]
      field_simp
    exact (hneg (div_ne_zero (by norm_num) hx) hh (invert_x hx he)).elim

-- Invert the 2-isogeny at a square x-coordinate by solving its defining quadratic.
private theorem lift_x {a b d y : ℚ} (hb : b ≠ 0) (hd : d ≠ 0)
    (he : OnCurve (-2 * a) (a ^ 2 - 4 * b) (d ^ 2) y) :
    ∃ r : ℚ, r ≠ 0 ∧ OnCurve a b r (d * r) ∧ r + a + b / r = d ^ 2 := by
  unfold OnCurve at he
  have hdisc : (d ^ 2 - a) ^ 2 - (y / d) ^ 2 = 4 * b := by
    field_simp
    linear_combination -he
  let r := (d ^ 2 - a + y / d) / 2
  have hprod : r * ((d ^ 2 - a - y / d) / 2) = b := by
    dsimp [r]
    linear_combination hdisc / 4
  have hr : r ≠ 0 := left_ne_zero_of_mul (hprod ▸ hb)
  have hquad : r ^ 2 + (a - d ^ 2) * r + b = 0 := by
    rw [← hprod]
    dsimp [r]
    ring
  refine ⟨r, hr, ?_, ?_⟩
  · unfold OnCurve
    linear_combination -r * hquad
  · field_simp
    linear_combination hquad

private theorem curve_y_ne_zero {x y : ℚ} (hx : 0 < x) (he : OnCurve (-3) 3 x y) : y ≠ 0 := by
  have hq : 0 < x ^ 2 - 3 * x + 3 := by nlinarith [sq_nonneg (2 * x - 3)]
  have hp := mul_pos hx hq
  unfold OnCurve at he
  intro hy
  rw [hy] at he
  nlinarith

private theorem curve_x_pos {x y : ℚ} (hx : x ≠ 0) (he : OnCurve (-3) 3 x y) : 0 < x := by
  have hq : 0 < x ^ 2 - 3 * x + 3 := by nlinarith [sq_nonneg (2 * x - 3)]
  by_contra! h
  have hp := mul_neg_of_neg_of_pos (lt_of_le_of_ne h hx) hq
  unfold OnCurve at he
  nlinarith [sq_nonneg y]

-- On each curve, translation by the rational 2-torsion point exchanges the two
-- square classes. After two lifts, the composite map has the duplication formula.
private theorem descends {x y : ℚ} (hx : 0 < x) (he : OnCurve (-3) 3 x y) :
    ∃ r z : ℚ, 0 < r ∧ OnCurve (-3) 3 r z ∧
      let f := (r ^ 2 - 3) ^ 2 / (4 * r * (r ^ 2 - 3 * r + 3))
      x = f ∨ 3 / x = f := by
  have hval (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) : Even (padicValRat p x) :=
    val_square_class (a := -3) (b := 3) hx.ne' (curve_y_ne_zero hx he) (by norm_num) (Or.inl rfl)
      (by simpa [OnCurve, sub_eq_add_neg] using he) hp hp3
  have hlift {X Y : ℚ} (hX : 0 < X) (hE : OnCurve (-3) 3 X Y) (hs : IsSquare X) :
      ∃ r z : ℚ, 0 < r ∧ OnCurve (-3) 3 r z ∧
        X = (r ^ 2 - 3) ^ 2 / (4 * r * (r ^ 2 - 3 * r + 3)) := by
    obtain ⟨d, hd⟩ := hs
    rw [← pow_two] at hd
    have hd0 : d ≠ 0 := by rintro rfl; simp [hd] at hX
    have hscale : (2 * d) ^ 2 = 4 * X := by rw [hd]; ring
    have hscaled : OnCurve (-2 * 6) (6 ^ 2 - 4 * (-3)) ((2 * d) ^ 2) (8 * Y) := by
      unfold OnCurve at *
      rw [hscale]
      linear_combination 64 * hE
    obtain ⟨q, hq, hQ, hXq⟩ := lift_x (a := 6) (b := -3) (by norm_num)
      (mul_ne_zero (by norm_num) hd0) hscaled
    have hXq' : q + 6 - 3 / q = 4 * X := by
      rw [hscale] at hXq
      simpa [sub_eq_add_neg, neg_div] using hXq
    have hYq : 2 * d * q ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hd0) hq
    have hnorm : ∃ Q V : ℚ, Q ≠ 0 ∧ OnCurve 6 (-3) Q V ∧ IsSquare Q ∧
        Q + 6 - 3 / Q = 4 * X := by
      rcases square_class_dual hq hYq hQ with hs | ⟨e, he⟩
      · exact ⟨q, _, hq, hQ, hs, hXq'⟩
      · have he0 : e ≠ 0 := by rintro rfl; simp [hq] at he
        have hq' : q = -3 * e ^ 2 := by
          rw [div_eq_iff (by norm_num : (-3 : ℚ) ≠ 0), ← pow_two] at he
          linarith
        refine ⟨-3 / q, _, div_ne_zero (by norm_num) hq, invert_x hq hQ, ⟨e⁻¹, ?_⟩, ?_⟩
        · rw [hq']
          field_simp
        · convert hXq' using 1
          field_simp
          ring
    obtain ⟨Q, V, hQ0, hdual, ⟨e, he⟩, hXQ⟩ := hnorm
    rw [← pow_two] at he
    have he0 : e ≠ 0 := by rintro rfl; simp [he] at hQ0
    have heq : OnCurve (-2 * (-3)) ((-3) ^ 2 - 4 * 3) (e ^ 2) V := by
      rw [← he]
      norm_num
      exact hdual
    obtain ⟨r, hr, hR, hR'⟩ := lift_x (a := -3) (b := 3) (by norm_num) he0 heq
    refine ⟨r, e * r, curve_x_pos hr hR, hR, ?_⟩
    have hvalQ : Q = (r ^ 2 - 3 * r + 3) / r := by
      rw [he, ← hR']
      field_simp
      ring
    have hn : r ^ 2 - 3 * r + 3 ≠ 0 := by nlinarith [sq_nonneg (2 * r - 3)]
    have hform : Q + 6 - 3 / Q = (r ^ 2 - 3) ^ 2 / (r * (r ^ 2 - 3 * r + 3)) := by
      rw [hvalQ]
      generalize hF : r ^ 2 - 3 * r + 3 = F at hn ⊢
      field_simp [hr, hn]
      rw [← hF]
      ring
    rw [hform] at hXQ
    calc
      X = ((r ^ 2 - 3) ^ 2 / (r * (r ^ 2 - 3 * r + 3))) / 4 :=
        (eq_div_iff (by norm_num)).2 (by linarith only [hXQ])
      _ = _ := by rw [mul_assoc, mul_comm (4 : ℚ), div_div]
  rcases square_or_three_mul_square hx hval with h | ⟨d, hd⟩
  · obtain ⟨r, z, hr, hR, h⟩ := hlift hx he h
    exact ⟨r, z, hr, hR, Or.inl h⟩
  · have hd0 : d ≠ 0 := by rintro rfl; simp [hx.ne'] at hd
    have hxd : x = 3 * d ^ 2 := by
      rw [div_eq_iff (by norm_num : (3 : ℚ) ≠ 0), ← pow_two] at hd
      linarith
    have hs : IsSquare (3 / x) := by refine ⟨d⁻¹, ?_⟩; rw [hxd]; field_simp
    obtain ⟨r, z, hr, hR, h⟩ := hlift (by positivity) (invert_x hx.ne' he) hs
    exact ⟨r, z, hr, hR, Or.inr h⟩

private def height (q : ℚ) : ℕ := max q.num.natAbs q.den

private theorem height_of_fraction {q : ℚ} {a b : ℤ} (hb : b ≠ 0)
    (hq : q = (a : ℚ) / (b : ℚ)) :
    ∃ g : ℤ, g ≠ 0 ∧ g ∣ a ∧ g ∣ b ∧ max a.natAbs b.natAbs = g.natAbs * height q := by
  rw [← Rat.divInt_eq_div] at hq
  obtain ⟨g, ha, hb'⟩ := Rat.num_den_mk hb hq
  have hg : g ≠ 0 := left_ne_zero_of_mul (hb' ▸ hb)
  refine ⟨g, hg, ⟨_, ha⟩, ⟨_, hb'⟩, ?_⟩
  rw [ha, hb']
  simp only [height, Int.natAbs_mul, Int.natAbs_natCast]
  exact (mul_max_of_nonneg _ _ (Nat.zero_le _)).symm

private theorem height_invert {x : ℚ} (hx : x ≠ 0) : height (3 / x) ≤ 3 * height x := by
  have hnum : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hq : 3 / x = ((3 * (x.den : ℤ) : ℤ) : ℚ) / (x.num : ℚ) := by
    conv_lhs => rw [← Rat.num_divInt_den x, Rat.divInt_eq_div]
    push_cast
    rw [div_div_eq_mul_div]
  obtain ⟨g, hg, -, -, hh⟩ := height_of_fraction hnum hq
  calc
    height (3 / x) ≤ g.natAbs * height (3 / x) := by
      exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hg)
    _ = max (3 * x.den) x.num.natAbs := by
      simpa [Int.natAbs_mul] using hh.symm
    _ ≤ 3 * height x := max_le
      (Nat.mul_le_mul_left _ (le_max_right _ _))
      ((le_max_left _ _).trans (Nat.le_mul_of_pos_left _ (by decide)))

private theorem height_before_cancellation (A B : ℤ) (ha : 0 < A) (hb : 0 < B) :
    max A B ^ 4 ≤
      4 * max ((A ^ 2 - 3 * B ^ 2) ^ 2) (4 * A * B * (A ^ 2 - 3 * A * B + 3 * B ^ 2)) := by
  have hQ : A ^ 2 ≤ 4 * (A ^ 2 - 3 * A * B + 3 * B ^ 2) := by
    nlinarith [sq_nonneg (A - 2 * B)]
  by_cases h : A ≤ B
  · rw [max_eq_right h]
    have hf : B ^ 2 ≤ -(A ^ 2 - 3 * B ^ 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ B + A by positivity)]
    have hh := pow_le_pow_left₀ (sq_nonneg B) hf 2
    nlinarith [le_max_left ((A ^ 2 - 3 * B ^ 2) ^ 2) (4 * A * B * (A ^ 2 - 3 * A * B + 3 * B ^ 2))]
  rw [max_eq_left (le_of_not_ge h)]
  by_cases h' : 3 * B ≤ A
  · have hf : A ^ 2 ≤ 2 * (A ^ 2 - 3 * B ^ 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h') (show 0 ≤ A + 3 * B by positivity)]
    have hh := pow_le_pow_left₀ (sq_nonneg A) hf 2
    have hmax := le_max_left ((A ^ 2 - 3 * B ^ 2) ^ 2) (4 * A * B * (A ^ 2 - 3 * A * B + 3 * B ^ 2))
    nlinarith
  · have hq : 0 ≤ A ^ 2 - 3 * A * B + 3 * B ^ 2 := by nlinarith [sq_nonneg A]
    have h₁ : A ^ 4 ≤ 3 * (A ^ 3 * B) := by
      have := mul_le_mul_of_nonneg_right (le_of_not_ge h') (show 0 ≤ A ^ 3 by positivity)
      nlinarith only [this]
    have h₂ := mul_le_mul_of_nonneg_left hQ (show 0 ≤ A * B by positivity)
    have h₃ := le_max_right ((A ^ 2 - 3 * B ^ 2) ^ 2) (4 * A * B * (A ^ 2 - 3 * A * B + 3 * B ^ 2))
    nlinarith [show 0 ≤ 4 * A * B * (A ^ 2 - 3 * A * B + 3 * B ^ 2) by positivity]

private theorem cancellation_dvd {A B g : ℤ} (hab : IsCoprime A B)
    (hF : g ∣ (A ^ 2 - 3 * B ^ 2) ^ 2) (hD : g ∣ 4 * A * B * (A ^ 2 - 3 * A * B + 3 * B ^ 2)) :
    g ∣ 1296 := by
  let F := A ^ 2 - 3 * B ^ 2
  let D := 4 * A * B * (A ^ 2 - 3 * A * B + 3 * B ^ 2)
  let T := 2 * A + 3 * B
  let C := 4 * B * (A - 3 * B) * T + 48 * B ^ 3
  -- This identity bounds the cancellation using only coprimality with B.
  have he : 36 * B ^ 5 = D * T - F * C := by dsimp [F, D, T, C]; ring
  have hg : g ∣ (36 * B ^ 5) ^ 2 := by
    rw [he, show (D * T - F * C) ^ 2 = D * (D * T ^ 2 - 2 * T * F * C) + F ^ 2 * C ^ 2 by ring]
    exact dvd_add (dvd_mul_of_dvd_left hD _) (dvd_mul_of_dvd_left hF _)
  have hcop : IsCoprime B F := by
    convert (hab.symm.pow_right (n := 2)).add_mul_right_right (-3 * B) using 1
    dsimp [F]
    ring
  have hcop' : IsCoprime g (B ^ 10) :=
    (hcop.symm.pow (m := 2) (n := 10)).of_isCoprime_of_dvd_left hF
  apply hcop'.dvd_of_dvd_mul_right
  convert hg using 1
  ring

private theorem duplication_height {r : ℚ} (hr : 0 < r) :
    height r ^ 4 ≤ 5184 * height ((r ^ 2 - 3) ^ 2 / (4 * r * (r ^ 2 - 3 * r + 3))) := by
  let A := r.num
  let B : ℤ := r.den
  let F : ℤ := (A ^ 2 - 3 * B ^ 2) ^ 2
  let D : ℤ := 4 * A * B * (A ^ 2 - 3 * A * B + 3 * B ^ 2)
  have ha : 0 < A := Rat.num_pos.mpr hr
  have hb : 0 < B := by dsimp [B]; positivity
  have hQ : 0 < A ^ 2 - 3 * A * B + 3 * B ^ 2 := by
    nlinarith [sq_nonneg (2 * A - 3 * B), sq_pos_of_pos hb]
  have hD : 0 < D := by dsimp [D]; positivity
  have hF : 0 ≤ F := sq_nonneg _
  have hq : (r ^ 2 - 3) ^ 2 / (4 * r * (r ^ 2 - 3 * r + 3)) = (F : ℚ) / (D : ℚ) := by
    have hre : r = (A : ℚ) / (B : ℚ) := by
      dsimp [A, B]
      rw [← Rat.divInt_eq_div, Rat.num_divInt_den]
    have hb0 : (B : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have hQ0 : (A : ℚ) ^ 2 - 3 * (A : ℚ) * (B : ℚ) + 3 * (B : ℚ) ^ 2 ≠ 0 := by
      exact_mod_cast hQ.ne'
    have ha0 : (A : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    conv_lhs => rw [hre]
    dsimp [F, D]
    push_cast
    field_simp [hb0, hQ0, ha0]
  obtain ⟨g, -, hgF, hgD, hsize⟩ := height_of_fraction hD.ne' hq
  have hg' := cancellation_dvd (Rat.isCoprime_num_den r) hgF hgD
  have hg1296 : g.natAbs ≤ 1296 := by
    have hd : g.natAbs ∣ 1296 := by simpa using (Int.natAbs_dvd_natAbs.mpr hg')
    exact Nat.le_of_dvd (by decide) hd
  have hlarge : height r ^ 4 ≤ 4 * max F.natAbs D.natAbs := by
    have hcast : ((height r : ℕ) : ℤ) = max A B := by
      simp [height, A, B, Nat.cast_max, Int.natAbs_of_nonneg ha.le]
    exact_mod_cast (show ((height r : ℕ) : ℤ) ^ 4 ≤ 4 * max (F.natAbs : ℤ) (D.natAbs : ℤ) by
      rw [hcast, Int.natAbs_of_nonneg hF, Int.natAbs_of_nonneg hD.le]
      exact height_before_cancellation A B ha hb)
  rw [hsize, ← mul_assoc] at hlarge
  exact hlarge.trans (Nat.mul_le_mul_right _ (by omega))

private def curveNumerator (a b : ℕ) : ℕ :=
  ((a : ℤ) * b * ((a : ℤ) ^ 2 - 3 * a * b + 3 * (b : ℤ) ^ 2)).natAbs

-- Below the descent threshold, the numerator of the homogenized equation can be
-- checked for squareness for every possible numerator and denominator.
private theorem small_height_points {r z : ℚ} (hr : 0 < r) (he : OnCurve (-3) 3 r z)
    (hh : height r < 25) : r = 1 ∨ r = 3 := by
  have hfinite : ∀ a b : Fin 25, 0 < a.val → 0 < b.val →
      let n := curveNumerator a.val b.val
      n.sqrt * n.sqrt = n → a.val = b.val ∨ a.val = 3 * b.val := by decide +kernel
  let A : Fin 25 := ⟨r.num.natAbs, lt_of_le_of_lt (le_max_left _ _) hh⟩
  let B : Fin 25 := ⟨r.den, lt_of_le_of_lt (le_max_right _ _) hh⟩
  have hA : 0 < r.num := Rat.num_pos.mpr hr
  have hB : 0 < r.den := r.den_pos
  have hA0 : 0 < A.val := Int.natAbs_pos.mpr hA.ne'
  have hAc : (A.val : ℤ) = r.num := Int.natAbs_of_nonneg hA.le
  have hBc : (B.val : ℤ) = r.den := rfl
  have hB0 : (B.val : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  have hre : r = (A.val : ℚ) / (B.val : ℚ) := by
    have h' : r = (r.num : ℚ) / ((r.den : ℤ) : ℚ) := by
      rw [← Rat.divInt_eq_div, Rat.num_divInt_den]
    simpa [← hAc, ← hBc] using h'
  let C : ℤ := (A.val : ℤ) * B.val *
    ((A.val : ℤ) ^ 2 - 3 * A.val * B.val + 3 * (B.val : ℤ) ^ 2)
  have hsq : IsSquare (C : ℚ) := by
    refine ⟨z * (B.val : ℚ) ^ 2, ?_⟩
    unfold OnCurve at he
    rw [hre] at he
    field_simp [hB0] at he
    dsimp [C]
    push_cast
    linear_combination -(B.val : ℚ) * he
  obtain ⟨k, hk⟩ := Rat.isSquare_intCast_iff.mp hsq
  have hk' : IsSquare C.natAbs := ⟨k.natAbs, by simpa [Int.natAbs_mul] using congrArg Int.natAbs hk⟩
  have hc := (Nat.exists_mul_self C.natAbs).mp (by
    obtain ⟨j, hj⟩ := hk'
    exact ⟨j, hj.symm⟩)
  rcases hfinite A B hA0 hB hc with hab | hab
  · left
    rw [hre, hab, div_self hB0]
  · right
    rw [hre]
    apply (div_eq_iff hB0).2
    exact_mod_cast hab

private theorem curve_x {x y : ℚ} (hx : 0 < x) (he : OnCurve (-3) 3 x y) : x = 1 ∨ x = 3 := by
  revert y
  induction x using (measure height).wf.induction with
  | h x ih =>
    intro y he
    obtain ⟨r, z, hr, hR, h⟩ := descends hx he
    dsimp at h
    have hd := duplication_height hr
    have hineq : height r ^ 4 ≤ 15552 * height x := by
      rcases h with h | h
      · exact (h ▸ hd).trans (Nat.mul_le_mul_right _ (by decide))
      · have hi := Nat.mul_le_mul_left 5184 (height_invert hx.ne')
        rw [← h] at hd
        exact hd.trans (by simpa [← mul_assoc] using hi)
    have hr' : r = 1 ∨ r = 3 := by
      by_cases hb : height r < 25
      · exact small_height_points hr hR hb
      · have hlt : height r < height x := by
          by_contra! hle
          have hsmall := hineq.trans (Nat.mul_le_mul_left _ hle)
          rw [pow_succ] at hsmall
          have hsmall' := Nat.le_of_mul_le_mul_right hsmall (by omega : 0 < height r)
          have hlarge := Nat.pow_le_pow_left (Nat.le_of_not_gt hb) 3
          omega
        exact ih r hlt hr hR
    have h1 : x = 1 ∨ 3 / x = 1 := by
      rcases hr' with rfl | rfl <;> norm_num at h ⊢ <;> exact h
    exact h1.imp id (fun h3 ↦ by simpa using ((div_eq_iff hx.ne').mp h3).symm)

end generalizedFermat_three_six_two_mul

open generalizedFermat_three_six_two_mul in
/-- **Nonzero rational points on the Mordell curve $y^2 = x^3 + 1$.** If $x$ and $y$ are
nonzero rationals with $y^2 = x^3 + 1$, then $x = 2$.

Source: Keith Conrad, *Examples of Mordell's Equation*, Example 3.6, footnote 4
(<https://kconrad.math.uconn.edu/blurbs/gradnumthy/mordelleqn1.pdf>). -/
public theorem eq_two_of_sq_eq_cube_add_one {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (he : y ^ 2 = x ^ 3 + 1) : x = 2 := by
  have hcurve : OnCurve (-3) 3 (x + 1) y := by
    unfold OnCurve
    linear_combination he
  have hxp : x + 1 ≠ 0 := by
    intro h0
    have hh : x = -1 := by linarith
    rw [hh] at he
    norm_num at he
    exact hy he
  rcases curve_x (curve_x_pos hxp hcurve) hcurve with h | h
  · exact (hx (by linarith)).elim
  · linarith

namespace generalizedFermat_three_six_two_mul

private theorem exponents_of_solution {s t w : ℕ} {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (he : x ^ (3 * s) + y ^ (6 * t) = z ^ (2 * w)) :
    Nat.Coprime s t ∧ Nat.Coprime s w ∧ Nat.Coprime t w ∧ Odd s ∧ ¬ 3 ∣ w := by
  let X := (x : ℚ) ^ s / ((y : ℚ) ^ t) ^ 2
  let Y := (z : ℚ) ^ w / ((y : ℚ) ^ t) ^ 3
  have hx' : (x : ℚ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hz' : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  have hX : X ≠ 0 := div_ne_zero (pow_ne_zero _ hx') (pow_ne_zero _ (pow_ne_zero _ hy'))
  have hY : Y ≠ 0 := div_ne_zero (pow_ne_zero _ hz') (pow_ne_zero _ (pow_ne_zero _ hy'))
  have hE : Y ^ 2 = X ^ 3 + 1 := by
    dsimp [X, Y]
    have hcast : (x : ℚ) ^ (s * 3) + (y : ℚ) ^ (t * 6) = (z : ℚ) ^ (w * 2) := by
      exact_mod_cast (by simpa [Nat.mul_comm] using he : x ^ (s * 3) + y ^ (t * 6) = z ^ (w * 2))
    simp only [pow_mul] at hcast
    field_simp [hy']
    linear_combination -hcast
  -- A nonzero solution gives the x-coordinate 2 and y-coordinate ±3 on the curve.
  have hX2 := eq_two_of_sq_eq_cube_add_one hX hY hE
  have hY9 : Y ^ 2 = (3 : ℚ) ^ 2 := by rw [hE, hX2]; norm_num
  have val_x (p : ℕ) [Fact p.Prime] : (s : ℤ) * padicValRat p (x : ℚ) =
      (if p = 2 then 1 else 0) + 2 * t * padicValRat p (y : ℚ) := by
    have h := congrArg (padicValRat p) hX2
    change padicValRat p ((x : ℚ) ^ s / ((y : ℚ) ^ t) ^ 2) = padicValRat p ((2 : ℕ) : ℚ) at h
    rw [padicValRat.div (pow_ne_zero _ hx') (pow_ne_zero _ (pow_ne_zero _ hy')),
      val_prime Nat.prime_two] at h
    simp only [padicValRat.pow, Nat.cast_ofNat] at h
    linarith
  have val_z (p : ℕ) [Fact p.Prime] : (w : ℤ) * padicValRat p (z : ℚ) =
      (if p = 3 then 1 else 0) + 3 * t * padicValRat p (y : ℚ) := by
    have h := congrArg (padicValRat p) hY9
    change padicValRat p (((z : ℚ) ^ w / ((y : ℚ) ^ t) ^ 3) ^ 2) =
      padicValRat p (((3 : ℕ) : ℚ) ^ 2) at h
    rw [padicValRat.pow,
      padicValRat.div (pow_ne_zero _ hz') (pow_ne_zero _ (pow_ne_zero _ hy'))] at h
    simp only [padicValRat.pow] at h
    rw [val_prime (p := p) Nat.prime_three] at h
    simp only [Nat.cast_ofNat] at h
    linarith
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx2 := val_x 2
  have hz2 := val_z 2
  have hx3 := val_x 3
  have hz3 := val_z 3
  rw [ite_eq_left rfl] at hx2 hz3
  simp only [ite_eq_right (by decide : (2 : ℕ) ≠ 3), ite_eq_right (by decide : (3 : ℕ) ≠ 2),
    zero_add] at hz2 hx3
  -- The two primes give Bézout identities for all three pairs of exponents.
  refine ⟨?_, ?_, ?_, Nat.coprime_two_left.mp ?_,
    Nat.prime_three.coprime_iff_not_dvd.mp ?_⟩
  all_goals rw [← Nat.isCoprime_iff_coprime]
  · exact ⟨padicValRat 2 (x : ℚ), -2 * padicValRat 2 (y : ℚ), by linear_combination hx2⟩
  · refine ⟨3 * (padicValRat 2 (x : ℚ) + padicValRat 3 (x : ℚ)),
      -2 * (padicValRat 2 (z : ℚ) + padicValRat 3 (z : ℚ)), ?_⟩
    linear_combination 3 * hx2 - 2 * hz2 + 3 * hx3 - 2 * hz3
  · exact ⟨-3 * padicValRat 3 (y : ℚ), padicValRat 3 (z : ℚ), by linear_combination hz3⟩
  · exact ⟨-(t : ℤ) * padicValRat 2 (y : ℚ), padicValRat 2 (x : ℚ), by linear_combination hx2⟩
  · exact ⟨-(t : ℤ) * padicValRat 3 (y : ℚ), padicValRat 3 (z : ℚ), by linear_combination hz3⟩

private theorem exists_dvd_mul_add_one {m n : ℕ} (hm : 0 < m) (h : n.Coprime m) :
    ∃ a : ℕ, m ∣ n * a + 1 := by
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_of_coprime (m - 1) h hm.ne'
  have hmod : n * a ≡ m - 1 [MOD m] := ha
  have hmod' := hmod.add_right 1
  rw [Nat.sub_add_cancel hm] at hmod'
  exact ⟨a, Nat.modEq_zero_iff_dvd.mp (hmod'.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))⟩

private theorem positive_solution {s t w : ℕ} (hs : 0 < s) (hw : 0 < w)
    (hst : Nat.Coprime s t) (hsw : Nat.Coprime s w) (htw : Nat.Coprime t w) (hodd : Odd s)
    (hthree : ¬ 3 ∣ w) :
    ∃ x y z : ℤ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ (3 * s) + y ^ (6 * t) = z ^ (2 * w) := by
  have hs2 : Nat.Coprime 2 s := Nat.coprime_two_left.mpr hodd
  have hw3 : Nat.Coprime 3 w := Nat.prime_three.coprime_iff_not_dvd.mpr hthree
  -- Choose the powers of 2 and 3 in k so that 2k², k and 3k³ have the required roots.
  obtain ⟨a, ha⟩ := exists_dvd_mul_add_one hs (hs2.mul_left (hst.symm.mul_left hsw.symm))
  obtain ⟨b, hb⟩ := exists_dvd_mul_add_one hw (hw3.mul_left (hsw.mul_left htw))
  let A := t * w * a
  let B := s * t * b
  have ha' : s ∣ A * 2 + 1 := by convert ha using 2; dsimp [A]; ring
  have hb' : w ∣ B * 3 + 1 := by convert hb using 2; dsimp [B]; ring
  have hBs : s ∣ B * 2 := ⟨t * b * 2, by dsimp [B]; ring⟩
  have hAw : w ∣ A * 3 := ⟨t * a * 3, by dsimp [A]; ring⟩
  let k : ℤ := 2 ^ A * 3 ^ B
  let x : ℤ := 2 ^ ((A * 2 + 1) / s) * 3 ^ ((B * 2) / s)
  let y : ℤ := 2 ^ (w * a) * 3 ^ (s * b)
  let z : ℤ := 2 ^ ((A * 3) / w) * 3 ^ ((B * 3 + 1) / w)
  have hx : x ^ s = 2 * k ^ 2 := by
    dsimp [x, k]
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.div_mul_cancel ha', Nat.div_mul_cancel hBs,
      pow_succ, mul_pow, pow_mul, pow_mul]
    ring
  have hy : y ^ t = k := by
    dsimp [y, k, A, B]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have hz : z ^ w = 3 * k ^ 3 := by
    dsimp [z, k]
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.div_mul_cancel hAw, Nat.div_mul_cancel hb',
      pow_succ, mul_pow, pow_mul, pow_mul]
    ring
  refine ⟨x, y, z, by dsimp [x]; positivity, by dsimp [y]; positivity,
    by dsimp [z]; positivity, ?_⟩
  rw [Nat.mul_comm 3, Nat.mul_comm 6, Nat.mul_comm 2, pow_mul, pow_mul, pow_mul, hx, hy, hz]
  ring

private theorem infinite_of_positive_solution {s t w : ℕ} (ht : 0 < t) (hw : 0 < w)
    {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (he : x ^ (3 * s) + y ^ (6 * t) = z ^ (2 * w)) :
    {xyz : ℤ × ℤ × ℤ | xyz.1 ≠ 0 ∧ xyz.2.1 ≠ 0 ∧ xyz.2.2 ≠ 0 ∧
      xyz.1 ^ (3 * s) + xyz.2.1 ^ (6 * t) = xyz.2.2 ^ (2 * w)}.Infinite := by
  let f : ℕ → ℤ × ℤ × ℤ := fun n ↦
    (x * ((n : ℤ) + 1) ^ (2 * t * w), y * ((n : ℤ) + 1) ^ (s * w),
      z * ((n : ℤ) + 1) ^ (3 * s * t))
  have hm : StrictMono fun n : ℕ ↦ (f n).1 := by
    intro a b hab
    dsimp [f]
    apply mul_lt_mul_of_pos_left _ hx
    exact pow_lt_pow_left₀ (by exact_mod_cast (Nat.add_lt_add_right hab 1)) (by positivity)
      (by positivity : 2 * t * w ≠ 0)
  have hi : Function.Injective f := fun a b h ↦ hm.injective (congrArg Prod.fst h)
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n, rfl⟩
  change _ ∧ _ ∧ _ ∧ _
  dsimp [f]
  refine ⟨ne_of_gt (by positivity), ne_of_gt (by positivity), ne_of_gt (by positivity), ?_⟩
  simp only [mul_pow, ← pow_mul]
  rw [show (2 * t * w) * (3 * s) = (s * w) * (6 * t) by ring,
    show (3 * s * t) * (2 * w) = (s * w) * (6 * t) by ring, ← add_mul, he]

end generalizedFermat_three_six_two_mul

/-- **Generalized Fermat equations with exponents 3s, 6t and 2w.** Let $s, t, w$ be positive
integers. If $s, t, w$ are pairwise coprime, $s$ is odd and $3 \nmid w$, then the equation
$x^{3s} + y^{6t} = z^{2w}$ has infinitely many solutions $(x, y, z)$ in nonzero integers;
otherwise it has no solution in nonzero integers.

Source: Richard F. Ryan, *Under What Conditions on the Exponents Does `x^m + y^n = z^r` Have
Solutions?*, INTEGERS 24 (2024), Article A48, Lemma 1 (`integers-2024-A48-lem-1`). -/
public theorem generalizedFermat_three_six_two_mul {s t w : ℕ} (hs : 0 < s) (ht : 0 < t)
    (hw : 0 < w) :
    (Nat.Coprime s t ∧ Nat.Coprime s w ∧ Nat.Coprime t w ∧ Odd s ∧ ¬ 3 ∣ w →
      {xyz : ℤ × ℤ × ℤ | xyz.1 ≠ 0 ∧ xyz.2.1 ≠ 0 ∧ xyz.2.2 ≠ 0 ∧
        xyz.1 ^ (3 * s) + xyz.2.1 ^ (6 * t) = xyz.2.2 ^ (2 * w)}.Infinite) ∧
    (¬ (Nat.Coprime s t ∧ Nat.Coprime s w ∧ Nat.Coprime t w ∧ Odd s ∧ ¬ 3 ∣ w) →
      ¬ GeneralizedFermatSolvable (3 * s) (6 * t) (2 * w)) := by
  constructor
  · rintro ⟨hst, hsw, htw, hodd, hthree⟩
    obtain ⟨x, y, z, hx, hy, hz, he⟩ :=
      generalizedFermat_three_six_two_mul.positive_solution hs hw hst hsw htw hodd hthree
    exact generalizedFermat_three_six_two_mul.infinite_of_positive_solution ht hw hx hy hz he
  · rintro h ⟨x, y, z, hx, hy, hz, he⟩
    exact h (generalizedFermat_three_six_two_mul.exponents_of_solution hx hy hz he)

end MetaMathlibExt
