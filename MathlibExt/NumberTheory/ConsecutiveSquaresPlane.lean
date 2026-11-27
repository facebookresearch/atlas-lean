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
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Pell

/-!
# Infinite families for the sum of consecutive squares equation

This module constructs infinitely many integer solutions to the sum of consecutive squares
equation on the plane determined by a given solution and the diagonal, preserving span parity.
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

private theorem discriminant_nonsquare {p q : ℤ} (h : Odd (p + q)) :
    ¬ IsSquare (discriminant p q) := by
  -- Opposite parity gives a discriminant of 5 modulo 8.
  obtain ⟨r, hr⟩ := h
  have hq : q = 2 * r + 1 - p := by omega
  have hd : (discriminant p q : ZMod 8) = 5 := by
    have residues : ∀ x y : ZMod 8,
        3 * (12 * x ^ 2 * (2 * y + 1 - x) ^ 2 - (x - (2 * y + 1 - x)) ^ 4) = 5 := by
      decide
    simpa [discriminant, hq, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow]
      using residues (p : ZMod 8) (r : ZMod 8)
  rintro ⟨z, hz⟩
  rw [hz, Int.cast_mul] at hd
  exact (show ∀ z : ZMod 8, z * z ≠ 5 by decide) _ hd

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
  rcases Int.even_or_odd (c - a) with he | ho
  -- For even span, the diagonal already gives an infinite family.
  · refine ⟨fun n => (n, n, n), ?_, ?_⟩
    · intro i j hij
      have hi : (i : ℤ) = (j : ℤ) := congrArg Prod.fst hij
      exact_mod_cast hi
    · intro n
      refine ⟨?_, ?_, ?_⟩
      · unfold SoCSEq
        ring
      · ring
      · simpa using (Int.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp he)).symm
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
  have hn : ¬ IsSquare d := discriminant_nonsquare (show Odd (p + q) by
    convert ho using 1
    dsimp [p, q]
    ring)
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
