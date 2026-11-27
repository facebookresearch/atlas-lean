/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.ConsecutiveSquares

import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Pell
import Mathlib.RingTheory.Int.Basic

/-!
# Infinite families for the sum of consecutive squares equation

This module proves `MetaMathlibExt.soCS_infinite_family_plane`: the plane through a solution of
the sum of consecutive squares problem and the diagonal contains infinitely many integer
solutions of the equation whose spans have the parity of the given span.

## Proof outline

Write `p = b - a` and `q = c - b` for the solution `(a, b, c)`. In the plane, the equation becomes
a generalized Pell equation with discriminant `3 (12 p² q² - (p - q)⁴)`. As in the source, the
family comes from multiplying the given solution by powers of a unit of the Pell equation; here
these are the powers congruent to `1` modulo `6 (p - q)`, which keep the coordinates integral. The
Pell coordinate stays odd, so for either parity of the span the coordinates of each triple are
pairwise distinct.

The source deduces that the discriminant is not a square from the rational points of an elliptic
curve (arXiv:2411.08398v2, Corollary 2.3). Here an elementary descent proves it instead. A square
discriminant would give a solution of `W² = u⁴ - 18u²v² - 27v⁴` with `u = p + q` and
`v = (p - q) / 3 ≠ 0`. Such a solution gives a solution of `V² = α⁴ + 9α²β² + 27β⁴` with
`|αβ| = |v|`, which in turn gives a solution of the first quartic with a smaller nonzero `|v|`.
-/

namespace MetaMathlibExt
namespace soCS_infinite_family_plane

open QuadraticAlgebra
open scoped nonZeroDivisors

-- A positive Pell unit has infinite order, and its reduction modulo m has finite order.
private theorem pellOrbit (d : ℤ) {m : ℕ} [NeZero m] (hd : 0 < d) (hn : ¬ IsSquare d)
    (s : QuadraticAlgebra ℤ d 0) (hs : s.norm ≠ 0) :
    ∃ f : ℕ → QuadraticAlgebra ℤ d 0, Function.Injective f ∧
      ∀ n, (f n).norm = s.norm ∧ (f n).re ≡ s.re [ZMOD m] ∧ (f n).im ≡ s.im [ZMOD m] := by
  obtain ⟨u, hx, hy⟩ := Pell.Solution₁.exists_pos_of_not_isSquare hd hn
  have hu : Function.Injective (fun n : ℕ => u ^ n) := by
    apply injective_pow_iff_not_isOfFinOrder.mpr
    intro h
    obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hpos := u.y_pow_succ_pos (zero_lt_one.trans hx) hy k
    simp [he] at hpos
  let embed : Pell.Solution₁ d →* QuadraticAlgebra ℤ d 0 :=
    { toFun := fun v => ⟨v.x, v.y⟩
      map_one' := by ext <;> simp
      map_mul' := by
        intro v w
        ext <;> simp [mul_assoc] }
  have hembed : Function.Injective embed := fun _ _ h =>
    Pell.Solution₁.ext (congrArg QuadraticAlgebra.re h) (congrArg QuadraticAlgebra.im h)
  have hnorm : (embed u).norm = 1 := by
    simpa [embed, QuadraticAlgebra.norm_def, sq, mul_assoc] using u.prop
  obtain ⟨v, hv⟩ := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hnorm ▸ isUnit_one)
  let reduce := QuadraticAlgebra.mapRingHom (Int.castRingHom (ZMod m)) d (0 : ℤ)
  let : Finite (QuadraticAlgebra (ZMod m) ((Int.castRingHom (ZMod m)) d)
      ((Int.castRingHom (ZMod m)) 0)) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd _ _).symm
  let w := Units.map reduce.toMonoidHom v
  let k := orderOf w
  have hk : 0 < k := orderOf_pos w
  have hperiod (n : ℕ) : reduce (embed (u ^ (k * n))) = 1 := by
    rw [map_pow, ← hv, map_pow]
    exact congrArg Units.val (show w ^ (k * n) = 1 by
      rw [pow_mul, pow_orderOf_eq_one w, one_pow])
  have hs' : s ∈ (QuadraticAlgebra ℤ d 0)⁰ :=
    QuadraticAlgebra.norm_mem_nonZeroDivisors_iff.mp (mem_nonZeroDivisors_of_ne_zero hs)
  refine ⟨fun n => s * embed (u ^ (k * n)), ?_, ?_⟩
  · intro n j h
    have he := (mul_cancel_left_mem_nonZeroDivisors hs').mp h
    exact Nat.eq_of_mul_eq_mul_left hk (hu (hembed he))
  · intro n
    have hr : reduce (s * embed (u ^ (k * n))) = reduce s := by
      rw [map_mul, hperiod, mul_one]
    refine ⟨?_, (ZMod.intCast_eq_intCast_iff _ _ m).mp (congrArg QuadraticAlgebra.re hr),
      (ZMod.intCast_eq_intCast_iff _ _ m).mp (congrArg QuadraticAlgebra.im hr)⟩
    simp [map_mul, map_pow, hnorm]

private def discriminant (p q : ℤ) : ℤ :=
  3 * (12 * p ^ 2 * q ^ 2 - (p - q) ^ 4)

private theorem discriminant_pos {p q : ℤ} (hq : 0 < q) (hpq : q < p) (hp : p < 4 * q) :
    0 < discriminant p q := by
  have hp₀ : 0 < p := hq.trans hpq
  have hbound : (p - q) ^ 2 < 3 * p * q := by
    nlinarith only [mul_lt_mul_of_pos_left hp hp₀, mul_lt_mul_of_pos_left hpq hq]
  have hsq := pow_lt_pow_left₀ hbound (sq_nonneg (p - q)) (by decide : 2 ≠ 0)
  unfold discriminant
  nlinarith only [hsq, sq_nonneg (p * q)]

/-! ### The discriminant is not a square -/

-- Coprime positive integers whose product is three times a square.
private theorem sq_factors {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hab : IsCoprime a b)
    (h : a * b = 3 * c ^ 2) :
    (∃ x y : ℤ, 0 ≤ x ∧ 0 ≤ y ∧ a = 3 * x ^ 2 ∧ b = y ^ 2) ∨
      ∃ x y : ℤ, 0 ≤ x ∧ 0 ≤ y ∧ a = x ^ 2 ∧ b = 3 * y ^ 2 := by
  have sq : ∀ {m n k : ℤ}, 0 < m → IsCoprime m n → m * n = k ^ 2 →
      ∃ x : ℤ, 0 ≤ x ∧ m = x ^ 2 := by
    intro m n k hm hmn hk
    obtain ⟨x, hx | hx⟩ := Int.sq_of_isCoprime hmn hk
    · exact ⟨|x|, abs_nonneg x, by rw [hx, sq_abs]⟩
    · nlinarith [sq_nonneg x]
  rcases Int.prime_three.dvd_or_dvd ⟨c ^ 2, h⟩ with ⟨a', rfl⟩ | ⟨b', rfl⟩
  · have h' : a' * b = c ^ 2 := by linarith
    have hcop : IsCoprime a' b := hab.of_mul_left_right
    obtain ⟨x, hx, rfl⟩ := sq (by linarith) hcop h'
    obtain ⟨y, hy, rfl⟩ := sq hb hcop.symm (by rw [mul_comm]; exact h')
    exact Or.inl ⟨x, y, hx, hy, rfl, rfl⟩
  · have h' : a * b' = c ^ 2 := by linarith
    have hcop : IsCoprime a b' := hab.of_mul_right_right
    obtain ⟨x, hx, rfl⟩ := sq ha hcop h'
    obtain ⟨y, hy, rfl⟩ := sq (by linarith) hcop.symm (by rw [mul_comm]; exact h')
    exact Or.inr ⟨x, y, hx, hy, rfl, rfl⟩

private theorem not_three_dvd_both {m n : ℤ} (hmn : IsCoprime m n) (hm : (3 : ℤ) ∣ m)
    (hn : (3 : ℤ) ∣ n) : False := by
  have := Int.isUnit_iff.mp (hmn.isUnit_of_dvd' hm hn)
  omega

-- Coprime positive integers whose product is 27 times a fourth power.
private theorem fourth_power_factors {a b c : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hab : IsCoprime a b) (h : a * b = 27 * c ^ 4) :
    ∃ x y : ℤ, ((a = 27 * x ^ 4 ∧ b = y ^ 4) ∨ (a = x ^ 4 ∧ b = 27 * y ^ 4)) ∧
      c ^ 2 = x ^ 2 * y ^ 2 ∧ IsCoprime x y := by
  have hc : 0 ≤ 3 * c ^ 2 := by positivity
  have inner : ∀ {x y : ℤ}, 0 < x → 0 < y → IsCoprime x y → x * y = 3 * c ^ 2 →
      (∃ g d : ℤ, x = 3 * g ^ 2 ∧ y = d ^ 2 ∧ IsCoprime g d ∧ c ^ 2 = g ^ 2 * d ^ 2) ∨
        ∃ g d : ℤ, x = g ^ 2 ∧ y = 3 * d ^ 2 ∧ IsCoprime g d ∧ c ^ 2 = g ^ 2 * d ^ 2 := by
    intro x y hx hy hxy hprod
    rcases sq_factors hx hy hxy hprod with ⟨g, d, -, -, rfl, rfl⟩ | ⟨g, d, -, -, rfl, rfl⟩
    · exact Or.inl ⟨g, d, rfl, rfl,
        (IsCoprime.pow_iff two_pos two_pos).mp hxy.of_mul_left_right, by linarith⟩
    · exact Or.inr ⟨g, d, rfl, rfl,
        (IsCoprime.pow_iff two_pos two_pos).mp hxy.of_mul_right_right, by linarith⟩
  have h3 : a * b = 3 * (3 * c ^ 2) ^ 2 := by rw [h]; ring
  rcases sq_factors ha hb hab h3 with ⟨x, y, hx, hy, rfl, rfl⟩ | ⟨x, y, hx, hy, rfl, rfl⟩
  · have hxy : IsCoprime x y := (IsCoprime.pow_iff two_pos two_pos).mp hab.of_mul_left_right
    have hprod : x * y = 3 * c ^ 2 :=
      (pow_left_inj₀ (mul_nonneg hx hy) hc two_ne_zero).mp (by linarith)
    have hx0 : 0 < x := lt_of_le_of_ne hx (by rintro rfl; simp at ha)
    have hy0 : 0 < y := lt_of_le_of_ne hy (by rintro rfl; simp at hb)
    rcases inner hx0 hy0 hxy hprod with ⟨g, d, rfl, rfl, hgd, hc2⟩ | ⟨g, d, rfl, rfl, hgd, hc2⟩
    · exact ⟨g, d, Or.inl ⟨by ring, by ring⟩, hc2, hgd⟩
    · exact (not_three_dvd_both hab ⟨g ^ 4, by ring⟩ ⟨3 * d ^ 4, by ring⟩).elim
  · have hxy : IsCoprime x y := (IsCoprime.pow_iff two_pos two_pos).mp hab.of_mul_right_right
    have hprod : x * y = 3 * c ^ 2 :=
      (pow_left_inj₀ (mul_nonneg hx hy) hc two_ne_zero).mp (by linarith)
    have hx0 : 0 < x := lt_of_le_of_ne hx (by rintro rfl; simp at ha)
    have hy0 : 0 < y := lt_of_le_of_ne hy (by rintro rfl; simp at hb)
    rcases inner hx0 hy0 hxy hprod with ⟨g, d, rfl, rfl, hgd, hc2⟩ | ⟨g, d, rfl, rfl, hgd, hc2⟩
    · exact (not_three_dvd_both hab ⟨3 * g ^ 4, by ring⟩ ⟨d ^ 4, by ring⟩).elim
    · exact ⟨g, d, Or.inr ⟨by ring, by ring⟩, hc2, hgd⟩

private theorem isCoprime_of_add_sub {a b : ℤ} (h : IsCoprime (a + b) (b - a)) :
    IsCoprime a b := by
  obtain ⟨s, t, hst⟩ := h
  exact ⟨s - t, s + t, by linear_combination hst⟩

-- A primitive solution of `W² = u⁴ - 18u²v² - 27v⁴` with `v ≠ 0` gives a solution of
-- `V² = α⁴ + 9α²β² + 27β⁴` with `|αβ| = |v|`: halve the coprime factors of
-- `(u² - 9v²)² - W² = 108v⁴`.
private theorem descend_first_quartic {u v W : ℤ} (huv : IsCoprime u v) (hv : v ≠ 0)
    (h : W ^ 2 = u ^ 4 - 18 * u ^ 2 * v ^ 2 - 27 * v ^ 4) :
    ∃ α β : ℤ, u ^ 2 = α ^ 4 + 9 * α ^ 2 * β ^ 2 + 27 * β ^ 4 ∧ v ^ 2 = α ^ 2 * β ^ 2 ∧
      IsCoprime α β ∧ ¬ (3 : ℤ) ∣ α ∧ Even (α * β) := by
  -- Modulo 8 and 32, the second coordinate is even.
  have hveven : Even v := by
    by_contra hodd
    obtain ⟨t, rfl⟩ := Int.not_even_iff_odd.mp hodd
    rcases Int.even_or_odd u with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · have hc := congrArg (Int.cast : ℤ → ZMod 8) h
      push_cast at hc
      rw [show ∀ x t : ZMod 8, (x + x) ^ 4 - 18 * (x + x) ^ 2 * (2 * t + 1) ^ 2 -
          27 * (2 * t + 1) ^ 4 = 5 by decide] at hc
      exact (show ∀ w : ZMod 8, w ^ 2 ≠ 5 by decide) _ hc
    · have hc := congrArg (Int.cast : ℤ → ZMod 32) h
      push_cast at hc
      rw [show ∀ x t : ZMod 32, (2 * x + 1) ^ 4 - 18 * (2 * x + 1) ^ 2 * (2 * t + 1) ^ 2 -
          27 * (2 * t + 1) ^ 4 = 20 by decide] at hc
      exact (show ∀ w : ZMod 32, w ^ 2 ≠ 20 by decide) _ hc
  have huodd : Odd u := by
    by_contra heven
    rw [Int.not_odd_iff_even, even_iff_two_dvd] at heven
    have := Int.isUnit_iff.mp (huv.isUnit_of_dvd' heven (even_iff_two_dvd.mp hveven))
    omega
  -- The first coordinate is prime to 3: otherwise 3 would divide W² exactly three times.
  have hu3 : ¬ (3 : ℤ) ∣ u := by
    rintro ⟨u₁, rfl⟩
    obtain ⟨W₁, rfl⟩ := Int.prime_three.dvd_of_dvd_pow (n := 2)
      ⟨9 * (3 * u₁ ^ 4 - 6 * u₁ ^ 2 * v ^ 2 - v ^ 4), by rw [h]; ring⟩
    have h₁ : W₁ ^ 2 = 3 * (3 * u₁ ^ 4 - 6 * u₁ ^ 2 * v ^ 2 - v ^ 4) :=
      mul_left_cancel₀ (by norm_num : (9 : ℤ) ≠ 0) (by linear_combination h)
    obtain ⟨W₂, rfl⟩ := Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨_, h₁⟩
    have h₂ : v ^ 4 = 3 * (u₁ ^ 4 - 2 * u₁ ^ 2 * v ^ 2 - W₂ ^ 2) :=
      mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) (by linear_combination h₁)
    exact not_three_dvd_both huv (dvd_mul_right 3 u₁)
      (Int.prime_three.dvd_of_dvd_pow (n := 4) ⟨_, h₂⟩)
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = u ^ 2 - 9 * v ^ 2 := ⟨_, rfl⟩
  have hv4 : 0 < v ^ 4 := by positivity
  have hZpos : 0 < Z := by
    by_contra hle
    have hu2 : u ^ 2 ≤ 9 * v ^ 2 := by linarith [not_lt.mp hle]
    nlinarith [sq_nonneg W, mul_nonneg (sq_nonneg u)
      (show (0 : ℤ) ≤ 18 * v ^ 2 - u ^ 2 by nlinarith [sq_nonneg v])]
  have hZW : W ^ 2 = Z ^ 2 - 108 * v ^ 4 := by rw [h, hZ]; ring
  have hZodd : Odd Z := by
    obtain ⟨x, rfl⟩ := huodd
    obtain ⟨y, rfl⟩ := hveven
    exact ⟨2 * x ^ 2 + 2 * x - 18 * y ^ 2, by rw [hZ]; ring⟩
  have hWodd : Odd W := (Int.odd_pow' two_ne_zero).mp (by
    rw [hZW]
    exact hZodd.pow.sub_even ⟨54 * v ^ 4, by ring⟩)
  -- Z is prime to 2, 3 and v, hence to Z² - W² = 108v⁴, hence to W.
  have hZv : IsCoprime Z v := by
    have := (huv.pow_left (m := 2)).add_mul_left_left (-9 * v)
    rw [hZ]; convert this using 1; ring
  have hZ3 : IsCoprime Z 3 := ((Prime.coprime_iff_not_dvd Int.prime_three).mpr (by
    intro h3
    apply hu3
    apply Int.prime_three.dvd_of_dvd_pow (n := 2)
    have : u ^ 2 = Z + 3 * (3 * v ^ 2) := by rw [hZ]; ring
    rw [this]
    exact dvd_add h3 (dvd_mul_right _ _))).symm
  have hZW' : IsCoprime Z W := by
    have h108 : IsCoprime Z (2 ^ 2 * 3 ^ 3 * v ^ 4) :=
      ((hZodd.isCoprime_two.pow_right).mul_right hZ3.pow_right).mul_right
        hZv.pow_right
    have : IsCoprime Z (-W ^ 2 + Z * Z) := by
      convert h108 using 1; linear_combination -hZW
    exact (IsCoprime.pow_right_iff two_pos).mp
      ((IsCoprime.neg_right_iff _ _).mp this.of_add_mul_left_right)
  obtain ⟨a, ha⟩ := hZodd.sub_odd hWodd
  have hlt := abs_lt_of_sq_lt_sq' (show W ^ 2 < Z ^ 2 by linarith) hZpos.le
  have hapos : 0 < a := by linarith
  have hbpos : 0 < a + W := by linarith
  have hab : a * (a + W) = 27 * v ^ 4 :=
    mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
      (by linear_combination -(2 * a + W + Z) * ha - hZW)
  have hcop : IsCoprime a (a + W) :=
    isCoprime_of_add_sub (by convert hZW' using 1 <;> linarith)
  obtain ⟨g, d, hgd, hv2, hcop'⟩ := fourth_power_factors hapos hbpos hcop hab
  have heven : ∀ {x y : ℤ}, v ^ 2 = x ^ 2 * y ^ 2 → Even (x * y) := by
    intro x y hxy
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show (x * y) ^ 2 = v ^ 2 by rw [hxy]; ring) with
      hv' | hv'
    · rw [hv']; exact hveven
    · rw [hv']; exact hveven.neg
  rcases hgd with ⟨hga, hdb⟩ | ⟨hga, hdb⟩
  · refine ⟨d, g, by linear_combination -hZ + ha + hdb + hga + 9 * hv2, by rw [hv2]; ring,
      hcop'.symm, fun h3 => ?_, heven (by rw [hv2]; ring)⟩
    exact not_three_dvd_both hcop (by rw [hga]; exact ⟨9 * g ^ 4, by ring⟩)
      (by rw [hdb]; exact dvd_pow h3 (by norm_num))
  · refine ⟨g, d, by linear_combination -hZ + ha + hdb + hga + 9 * hv2, hv2, hcop',
      fun h3 => ?_, heven hv2⟩
    exact not_three_dvd_both hcop (by rw [hga]; exact dvd_pow h3 (by norm_num))
      (by rw [hdb]; exact ⟨9 * d ^ 4, by ring⟩)

-- A solution of `V² = α⁴ + 9α²β² + 27β⁴` as produced above gives a solution of
-- `W² = u⁴ - 18u²v² - 27v⁴` with `0 < |v| < |αβ|`: factor `(2V)² - (2α² + 9β²)² = 27β⁴`.
private theorem descend_second_quartic {α β V : ℤ} (hαβ : IsCoprime α β)
    (h3 : ¬ (3 : ℤ) ∣ α) (he : Even (α * β)) (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : V ^ 2 = α ^ 4 + 9 * α ^ 2 * β ^ 2 + 27 * β ^ 4) :
    ∃ u v W : ℤ, W ^ 2 = u ^ 4 - 18 * u ^ 2 * v ^ 2 - 27 * v ^ 4 ∧ v ≠ 0 ∧
      v.natAbs < (α * β).natAbs := by
  obtain ⟨V, hV0, h⟩ : ∃ V' : ℤ, 0 ≤ V' ∧ V' ^ 2 = α ^ 4 + 9 * α ^ 2 * β ^ 2 + 27 * β ^ 4 :=
    ⟨|V|, abs_nonneg V, by rw [sq_abs]; exact h⟩
  have hle : ∀ {g d b : ℤ}, b ^ 2 = g ^ 2 * d ^ 2 → b ≠ 0 → g ≠ 0 ∧ g.natAbs ≤ b.natAbs := by
    intro g d b hb hb0
    have hnat : b.natAbs = g.natAbs * d.natAbs := by
      rw [← Int.natAbs_mul]; exact Int.natAbs_eq_iff_sq_eq.mpr (by rw [hb]; ring)
    have hb' : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb0
    rw [hnat] at hb'
    refine ⟨Int.natAbs_ne_zero.mp (left_ne_zero_of_mul hb'), ?_⟩
    rw [hnat]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (right_ne_zero_of_mul hb'))
  have hα1 : 0 < α.natAbs := Int.natAbs_pos.mpr hα
  have hβ1 : 0 < β.natAbs := Int.natAbs_pos.mpr hβ
  rcases Int.even_mul.mp he with hαe | hβe
  · -- α is even and β is odd.
    have hβo : Odd β := by
      rw [← Int.not_even_iff_odd]
      intro hβe
      have := Int.isUnit_iff.mp
        (hαβ.isUnit_of_dvd' (even_iff_two_dvd.mp hαe) (even_iff_two_dvd.mp hβe))
      omega
    obtain ⟨X, hX⟩ : ∃ X, X = 2 * α ^ 2 + 9 * β ^ 2 := ⟨_, rfl⟩
    have hXpos : 0 < X := by rw [hX]; positivity
    have hXodd : Odd X := by
      obtain ⟨r, rfl⟩ := hαe
      obtain ⟨s, rfl⟩ := hβo
      exact ⟨4 * r ^ 2 + 18 * s ^ 2 + 18 * s + 4, by rw [hX]; ring⟩
    have hdiff : (2 * V) ^ 2 - X ^ 2 = 27 * β ^ 4 := by rw [hX]; linear_combination 4 * h
    have hX3 : IsCoprime X 3 := ((Prime.coprime_iff_not_dvd Int.prime_three).mpr (by
      intro h3X
      apply h3
      have h32 : (3 : ℤ) ∣ 2 * α ^ 2 := by
        have : 2 * α ^ 2 = X - 3 * (3 * β ^ 2) := by rw [hX]; ring
        rw [this]; exact dvd_sub h3X (dvd_mul_right _ _)
      rcases Int.prime_three.dvd_or_dvd h32 with h32 | h3α
      · norm_num at h32
      · exact Int.prime_three.dvd_of_dvd_pow h3α)).symm
    have hXβ : IsCoprime X β := by
      have h2 : IsCoprime (2 * α ^ 2) β :=
        (Int.isCoprime_two_left.mpr hβo).mul_left (hαβ.pow_left (m := 2))
      rw [hX]; convert h2.add_mul_left_left (9 * β) using 1; ring
    have hXV : IsCoprime X V := by
      have h27 : IsCoprime X (3 ^ 3 * β ^ 4) := hX3.pow_right.mul_right hXβ.pow_right
      have h4 : IsCoprime X (2 ^ 2 * V ^ 2) := by
        convert h27.add_mul_left_right X using 1; linear_combination hdiff
      exact (IsCoprime.pow_right_iff two_pos).mp h4.of_mul_right_right
    have hβ4 : 0 < β ^ 4 := by positivity
    have hlt := abs_lt_of_sq_lt_sq' (show X ^ 2 < (2 * V) ^ 2 by linarith)
      (by linarith : (0 : ℤ) ≤ 2 * V)
    have hapos : 0 < 2 * V - X := by linarith
    have hbpos : 0 < 2 * V + X := by linarith
    have hab : (2 * V - X) * (2 * V + X) = 27 * β ^ 4 := by linear_combination hdiff
    have hodd : Odd (2 * V - X) := by
      obtain ⟨r, hr⟩ := hXodd
      exact ⟨V - r - 1, by rw [hr]; ring⟩
    have hcop : IsCoprime (2 * V - X) (2 * V + X) := by
      have ha2 : IsCoprime (2 * V - X) 2 := hodd.isCoprime_two
      have haX : IsCoprime (2 * V - X) X := by
        have : IsCoprime (2 * V) X := (Int.isCoprime_two_left.mpr hXodd).mul_left hXV.symm
        convert this.add_mul_left_left (-1) using 1; ring
      convert (ha2.mul_right haX).add_mul_left_right 1 using 1; ring
    obtain ⟨g, d, hgd, hβ2, -⟩ := fourth_power_factors hapos hbpos hcop hab
    obtain ⟨hg0, hgle⟩ := hle hβ2 hβ
    rcases hgd with ⟨hga, hdb⟩ | ⟨hga, hdb⟩
    · refine ⟨d, g, 2 * α, by linear_combination -hga + hdb - 2 * hX - 18 * hβ2, hg0, ?_⟩
      have hα2 : 2 ≤ α.natAbs := by
        obtain ⟨r, rfl⟩ := hαe
        rw [← two_mul, Int.natAbs_mul] at hα1 ⊢
        norm_num at hα1 ⊢
        omega
      rw [Int.natAbs_mul]
      nlinarith
    · -- Modulo 16 the two sides differ by 8.
      exfalso
      have hgo : Odd g := (Int.odd_pow' (by norm_num : (4 : ℕ) ≠ 0)).mp (hga ▸ hodd)
      have hsum : Odd (2 * V + X) := by
        convert hodd.add_even (⟨X, by ring⟩ : Even (2 * X)) using 1; ring
      rw [hdb] at hsum
      have hdo : Odd d := (Int.odd_pow' (by norm_num : (4 : ℕ) ≠ 0)).mp (Int.odd_mul.mp hsum).2
      have E : 4 * α ^ 2 = 27 * d ^ 4 - g ^ 4 - 18 * g ^ 2 * d ^ 2 := by
        linear_combination -hga + hdb - 2 * hX - 18 * hβ2
      obtain ⟨r, rfl⟩ := hαe
      obtain ⟨s, rfl⟩ := hgo
      obtain ⟨t, rfl⟩ := hdo
      have hc := congrArg (Int.cast : ℤ → ZMod 16) E
      push_cast at hc
      rw [show ∀ r : ZMod 16, 4 * (r + r) ^ 2 = 0 by decide,
        show ∀ s t : ZMod 16, 27 * (2 * t + 1) ^ 4 - (2 * s + 1) ^ 4 -
          18 * (2 * s + 1) ^ 2 * (2 * t + 1) ^ 2 = 8 by decide] at hc
      exact absurd hc (by decide)
  · -- β is even and α is odd.
    have hαo : Odd α := by
      rw [← Int.not_even_iff_odd]
      intro hαe
      have := Int.isUnit_iff.mp
        (hαβ.isUnit_of_dvd' (even_iff_two_dvd.mp hαe) (even_iff_two_dvd.mp hβe))
      omega
    obtain ⟨b, rfl⟩ := hβe
    have hb0 : b ≠ 0 := by rintro rfl; simp at hβ
    have hαb : IsCoprime α b := by
      have : IsCoprime α (2 * b) := by rw [two_mul]; exact hαβ
      exact this.of_mul_right_right
    obtain ⟨X, hX⟩ : ∃ X, X = α ^ 2 + 18 * b ^ 2 := ⟨_, rfl⟩
    have hXpos : 0 < X := by rw [hX]; positivity
    have hXodd : Odd X := by
      obtain ⟨r, rfl⟩ := hαo
      exact ⟨2 * r ^ 2 + 2 * r + 9 * b ^ 2, by rw [hX]; ring⟩
    have hdiff : V ^ 2 - X ^ 2 = 108 * b ^ 4 := by rw [hX]; linear_combination h
    have hVodd : Odd V := (Int.odd_pow' two_ne_zero).mp (by
      have : V ^ 2 = X ^ 2 + 2 * (54 * b ^ 4) := by linear_combination hdiff
      rw [this]; exact hXodd.pow.add_even ⟨54 * b ^ 4, by ring⟩)
    have hX3 : IsCoprime X 3 := ((Prime.coprime_iff_not_dvd Int.prime_three).mpr (by
      intro h3X
      apply h3
      apply Int.prime_three.dvd_of_dvd_pow (n := 2)
      have : α ^ 2 = X - 3 * (6 * b ^ 2) := by rw [hX]; ring
      rw [this]; exact dvd_sub h3X (dvd_mul_right _ _))).symm
    have hXb : IsCoprime X b := by
      have := (hαb.pow_left (m := 2)).add_mul_left_left (18 * b)
      rw [hX]; convert this using 1; ring
    have hXV : IsCoprime X V := by
      have h108 : IsCoprime X (2 ^ 2 * 3 ^ 3 * b ^ 4) :=
        ((hXodd.isCoprime_two.pow_right).mul_right hX3.pow_right).mul_right
          hXb.pow_right
      have h4 : IsCoprime X (V ^ 2) := by
        convert h108.add_mul_left_right X using 1; linear_combination hdiff
      exact (IsCoprime.pow_right_iff two_pos).mp h4
    have hb4 : 0 < b ^ 4 := by positivity
    obtain ⟨a, ha⟩ := hVodd.sub_odd hXodd
    have hlt := abs_lt_of_sq_lt_sq' (show X ^ 2 < V ^ 2 by linarith) hV0
    have hapos : 0 < a := by linarith
    have hbpos : 0 < a + X := by linarith
    have hab : a * (a + X) = 27 * b ^ 4 :=
      mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
        (by linear_combination -(V + X + 2 * a) * ha + hdiff)
    have hcop : IsCoprime a (a + X) :=
      isCoprime_of_add_sub (by convert hXV.symm using 1 <;> linarith)
    obtain ⟨g, d, hgd, hb2, -⟩ := fourth_power_factors hapos hbpos hcop hab
    obtain ⟨hg0, hgle⟩ := hle hb2 hb0
    rcases hgd with ⟨hga, hdb⟩ | ⟨hga, hdb⟩
    · refine ⟨d, g, α, by linear_combination -hga + hdb - hX - 18 * hb2, hg0, ?_⟩
      have hb1 : 0 < b.natAbs := Int.natAbs_pos.mpr hb0
      rw [Int.natAbs_mul, ← two_mul, Int.natAbs_mul]
      norm_num
      nlinarith
    · -- An odd square is 1 modulo 8, which the right side never is.
      exfalso
      have E : α ^ 2 = 27 * d ^ 4 - 18 * g ^ 2 * d ^ 2 - g ^ 4 := by
        linear_combination -hga + hdb - hX - 18 * hb2
      obtain ⟨r, rfl⟩ := hαo
      have hc := congrArg (Int.cast : ℤ → ZMod 8) E
      push_cast at hc
      rw [show ∀ r : ZMod 8, (2 * r + 1) ^ 2 = 1 by decide] at hc
      exact (show ∀ g d : ZMod 8, 1 ≠ 27 * d ^ 4 - 18 * g ^ 2 * d ^ 2 - g ^ 4 by decide) _ _ hc

-- By infinite descent on `|v|`, the quartic `W² = u⁴ - 18u²v² - 27v⁴` forces `v = 0`.
private theorem first_quartic_trivial (n : ℕ) : ∀ {u v W : ℤ}, v.natAbs = n →
    W ^ 2 = u ^ 4 - 18 * u ^ 2 * v ^ 2 - 27 * v ^ 4 → v = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v W hn h
    by_contra hv
    obtain ⟨g, u₀, v₀, hg, hcop, rfl, rfl⟩ :=
      Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_right u hv)
    have hg' : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
    have hv₀ : v₀ ≠ 0 := by rintro rfl; simp at hv
    obtain ⟨W₀, rfl⟩ : (g : ℤ) ^ 2 ∣ W := (Int.pow_dvd_pow_iff two_ne_zero).mp
      ⟨u₀ ^ 4 - 18 * u₀ ^ 2 * v₀ ^ 2 - 27 * v₀ ^ 4, by rw [h]; ring⟩
    have h₀ : W₀ ^ 2 = u₀ ^ 4 - 18 * u₀ ^ 2 * v₀ ^ 2 - 27 * v₀ ^ 4 :=
      mul_left_cancel₀ (pow_ne_zero 4 hg') (by linear_combination h)
    obtain ⟨α, β, hu, hv₂, hαβ, h3, he⟩ :=
      descend_first_quartic (Int.isCoprime_iff_gcd_eq_one.mpr hcop) hv₀ h₀
    have hαβ0 : α * β ≠ 0 := by
      intro h0
      apply hv₀
      have : v₀ ^ 2 = 0 := by rw [hv₂, ← mul_pow, h0]; ring
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    obtain ⟨u', v', W', h', hv', hlt⟩ := descend_second_quartic hαβ h3 he
      (left_ne_zero_of_mul hαβ0) (right_ne_zero_of_mul hαβ0) hu
    have heq : (α * β).natAbs = v₀.natAbs := Int.natAbs_eq_iff_sq_eq.mpr (by rw [hv₂]; ring)
    have hle : v₀.natAbs ≤ n := by
      rw [← hn, Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.le_mul_of_pos_right _ hg
    exact hv' (ih _ (by omega) rfl h')

-- The discriminant is a square only when `p = q`: a square root `3w'` gives the solution
-- `(p + q, (p - q) / 3, 2w')` of the first quartic.
private theorem discriminant_nonsquare {p q : ℤ} (hpq : p ≠ q) :
    ¬ IsSquare (discriminant p q) := by
  rintro ⟨w, hw⟩
  unfold discriminant at hw
  obtain ⟨w', rfl⟩ : (3 : ℤ) ∣ w := (Int.prime_three.dvd_or_dvd ⟨_, hw.symm⟩).elim id id
  have h1 : 12 * p ^ 2 * q ^ 2 - (p - q) ^ 4 = 3 * w' ^ 2 :=
    mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) (by linear_combination hw)
  obtain ⟨r, hr⟩ : (3 : ℤ) ∣ p - q := Int.prime_three.dvd_of_dvd_pow (n := 4)
    ⟨4 * p ^ 2 * q ^ 2 - w' ^ 2, by linear_combination -h1⟩
  have h2 : w' ^ 2 = 4 * p ^ 2 * q ^ 2 - 27 * r ^ 4 := by
    rw [hr] at h1
    exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) (by linear_combination -h1)
  obtain rfl : p = q + 3 * r := by linarith
  have hr0 := first_quartic_trivial _ (u := 2 * q + 3 * r) (v := r) (W := 2 * w') rfl
    (by linear_combination 4 * h2)
  apply hpq
  rw [hr0]
  ring

/-! ### The equation in the plane -/

-- The plane is parametrized by (y - p*t, y, y + q*t). Complete the square in y.
private def pellReal (p q y t : ℤ) : ℤ :=
  3 * (p - q) * (2 * y + 1) - 3 * (p ^ 2 + q ^ 2) * t

private theorem pell_identity (p q y t : ℤ) :
    t * (pellReal p q y t ^ 2 - discriminant p q * t ^ 2 - 3 * (p - q) ^ 2) =
      6 * (p - q) * (2 * (y * (y + 1) * (2 * y + 1)) -
        ((y - p * t) * (y - p * t + 1) * (2 * (y - p * t) + 1) +
          (y + q * t) * (y + q * t + 1) * (2 * (y + q * t) + 1))) := by
  unfold pellReal discriminant
  ring

-- A rational upper bound on the published bound for the ratio of the two spans.
private theorem ratio_bound_lt_four :
    1 + (2 : ℝ) ^ (1 / 3 : ℝ) + (2 : ℝ) ^ (2 / 3 : ℝ) < 4 := by
  have h : (2 : ℝ) ^ (1 / 3 : ℝ) < 9 / 7 := by
    rw [one_div, Real.rpow_inv_lt_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have h₂ : (2 : ℝ) ^ (2 / 3 : ℝ) < (9 / 7) ^ 2 := by
    rw [show (2 / 3 : ℝ) = (1 / 3 : ℝ) * (2 : ℕ) by norm_num,
      Real.rpow_mul_natCast (by norm_num)]
    exact pow_lt_pow_left₀ h (by positivity) (by decide)
  linarith only [h, h₂]

end soCS_infinite_family_plane

open soCS_infinite_family_plane in
/-- **Infinite families of solutions in a plane.** Let $(a, b, c)$ be a solution of the sum of
consecutive squares problem. Then there are infinitely many distinct integer triples $(x, y, z)$
satisfying the sum of consecutive squares equation
$2\,y(y+1)(2y+1) = x(x+1)(2x+1) + z(z+1)(2z+1)$, with no order or sign condition, such that
$(b - c)x + (c - a)y + (a - b)z = 0$ and $z - x \equiv c - a \pmod 2$.

The coordinates of a triple need not be distinct. For an even span $c - a$ the statement
therefore already holds with the diagonal triples $(n, n, n)$, $n \in \mathbb{N}$, which satisfy
the equation, lie in the plane and have $z - x = 0$. The source excludes these trivial
solutions: its proof assumes that $x$, $y$ and $z$ are distinct. For an odd span the parity
condition gives $z \ne x$, and in the plane two equal coordinates force all three to be equal,
so the coordinates of each triple are then distinct.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Proposition 1
(`integers-2026-A1-prop-1`). -/
public theorem soCS_infinite_family_plane (a b c : ℤ)
    (h : IsSoCSSolution a b c) :
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, SoCSEq (f n).1 (f n).2.1 (f n).2.2 ∧
        (b - c) * (f n).1 + (c - a) * (f n).2.1 + (a - b) * (f n).2.2 = 0 ∧
        (f n).2.2 - (f n).1 ≡ c - a [ZMOD 2] := by
  let p := b - a
  let q := c - b
  let k := p - q
  let d := discriminant p q
  have hq : 0 < q := sub_pos.mpr h.2.2.1
  have hqℝ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have bounds := soCS_ratio_bounds a b c h
  have hpq : q < p := by
    have lower := (lt_div_iff₀ hqℝ).mp (by
      simpa only [p, q, Int.cast_sub] using bounds.1)
    rw [one_mul] at lower
    exact_mod_cast lower
  have hp : p < 4 * q := by
    have upper := (div_lt_iff₀ hqℝ).mp (by
      simpa only [p, q, Int.cast_sub] using bounds.2.trans ratio_bound_lt_four)
    exact_mod_cast upper
  have hk : 0 < k := sub_pos.mpr hpq
  have hd : 0 < d := discriminant_pos hq hpq hp
  have hn : ¬ IsSquare d := discriminant_nonsquare hpq.ne'
  -- Keep both Pell coordinates fixed modulo 6*k so the inverse substitution is integral.
  let m := (6 * k).toNat
  have hm : (m : ℤ) = 6 * k := Int.toNat_of_nonneg (by positivity)
  let : NeZero m := ⟨by omega⟩
  let s : QuadraticAlgebra ℤ d 0 := ⟨pellReal p q b 1, 1⟩
  have hs : s.norm = 3 * k ^ 2 := by
    have he : SoCSEq (b - p * 1) b (b + q * 1) := by simpa [p, q] using h.2.2.2
    unfold SoCSEq at he
    have hid := pell_identity p q b 1
    rw [sub_eq_zero.mpr he, mul_zero, one_mul, one_pow, mul_one] at hid
    simpa [s, QuadraticAlgebra.norm_def, k, d, sq, mul_assoc] using sub_eq_zero.mp hid
  obtain ⟨g, hg, hnorm⟩ := pellOrbit d (m := m) hd hn s (hs ▸ by positivity)
  have hyInt (n : ℕ) : (6 * k) ∣ ((g n).re + 3 * (p ^ 2 + q ^ 2) * (g n).im - 3 * k) := by
    obtain ⟨_, hre, him⟩ := hnorm n
    have hc := (hre.add (him.mul_left (3 * (p ^ 2 + q ^ 2)))).sub_right (3 * k)
    rw [hm, show s.re + 3 * (p ^ 2 + q ^ 2) * s.im - 3 * k = 6 * k * b by
      dsimp [s, pellReal, k]
      ring] at hc
    exact hc.dvd_iff.mpr (dvd_mul_right _ _)
  let y (n : ℕ) := ((g n).re + 3 * (p ^ 2 + q ^ 2) * (g n).im - 3 * k) / (6 * k)
  have hy (n : ℕ) : pellReal p q (y n) (g n).im = (g n).re := by
    have he := Int.mul_ediv_cancel' (hyInt n)
    change 6 * k * y n = _ at he
    change 3 * k * (2 * y n + 1) - 3 * (p ^ 2 + q ^ 2) * (g n).im = _
    linear_combination he
  let f (n : ℕ) : ℤ × ℤ × ℤ := (y n - p * (g n).im, y n, y n + q * (g n).im)
  refine ⟨f, ?_, ?_⟩
  · intro i j hf
    -- The middle and last coordinates determine the Pell coordinates.
    have hy' : y i = y j := congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) hf
    have hz : y i + q * (g i).im = y j + q * (g j).im :=
      congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) hf
    rw [hy', add_right_inj] at hz
    have ht := mul_left_cancel₀ hq.ne' hz
    apply hg
    exact QuadraticAlgebra.ext (by rw [← hy i, ← hy j, hy', ht]) ht
  · intro n
    have hN := (hnorm n).1.trans hs
    have hN' : (g n).re ^ 2 - d * (g n).im ^ 2 = 3 * k ^ 2 := by
      simpa [QuadraticAlgebra.norm_def, sq, mul_assoc] using hN
    have hid := pell_identity p q (y n) (g n).im
    rw [hy, show discriminant p q = d from rfl, hN', sub_self, mul_zero,
      eq_comm, mul_eq_zero] at hid
    refine ⟨?_, ?_, ?_⟩
    · exact sub_eq_zero.mp (hid.resolve_left (by positivity))
    · dsimp [f, p, q]
      ring
    -- The Pell coordinate stays odd, so `z - x = (c - a) t` has the parity of `c - a`.
    · have hm₂ : (2 : ℤ) ∣ (m : ℤ) := by
        rw [hm]
        exact ⟨3 * k, by ring⟩
      have ht := (hnorm n).2.2.of_dvd hm₂
      change (g n).im ≡ 1 [ZMOD 2] at ht
      have hspan : (f n).2.2 - (f n).1 = (c - a) * (g n).im := by
        dsimp [f, p, q]
        ring
      simpa only [hspan, mul_one] using ht.mul_left (c - a)

end MetaMathlibExt
