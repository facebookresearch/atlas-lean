/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix
public import MathlibExt.NumberTheory.FermatQuotient
import MathlibExt.NumberTheory.WolstenholmeCongruenceEquivalence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination

/-!
# Two Delannoy triangle entries modulo a prime cube

The theorem `delannoy_two_mul` evaluates the central entry in row `2 * p` and its
neighbor in row `2 * p - 1` modulo `p ^ 3` for primes `p ≥ 5`, using the Fermat
quotient of two (with the coprimality witness required by `Int.fermatQuotient`).

## References

* Chahinaze Djadi and Hacène Belbachir, *Congruence Properties for the Delannoy Triangle
  Coefficients*, Journal of Integer Sequences 29 (2026), Article 26.5.2, Theorem 1.
-/

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

open Finset

private abbrev R (p : ℕ) := ZMod (p ^ 3)

private def frac (p k : ℕ) : R p := p * (k : R p)⁻¹

private theorem cube_zero (p : ℕ) : (p : R p) ^ 3 = 0 := by
  simp [← Nat.cast_pow, R]

private theorem unit_of_lt {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    IsUnit (k : R p) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).2 (Nat.not_dvd_of_pos_of_lt hk hkp)

private theorem frac_mul {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    frac p k * k = p := by
  rw [frac, mul_assoc, mul_comm (_⁻¹), ZMod.mul_inv_of_unit _ (unit_of_lt hp hk hkp), mul_one]

-- The opposite denominators k and p-k satisfy y = -x-x², since x³ vanishes.
private theorem frac_reflect {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    frac p (p - k) = -frac p k - frac p k ^ 2 := by
  apply (unit_of_lt hp (k := p - k) (by omega) (by omega)).mul_right_cancel
  rw [frac_mul hp (by omega) (by omega), Nat.cast_sub hkp.le]
  have h := frac_mul hp hk hkp
  have hz : (p : R p) * frac p k ^ 2 = 0 := by
    unfold frac
    linear_combination ((k : R p)⁻¹) ^ 2 * cube_zero p
  linear_combination -(1 + frac p k) * h + hz

private theorem frac_reflect_sq {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    frac p (p - k) ^ 2 = frac p k ^ 2 := by
  rw [frac_reflect hp hk hkp, frac]
  linear_combination ((k : R p)⁻¹ ^ 3 * (2 + p * (k : R p)⁻¹)) * cube_zero p

private def squareSum (p j : ℕ) : R p :=
  (p : R p) ^ 2 * ∑ i ∈ range j, ((i + 1 : ℕ) : R p)⁻¹ ^ 2

private theorem squareSum_succ (p j : ℕ) :
    squareSum p (j + 1) = squareSum p j + frac p (j + 1) ^ 2 := by
  simp [squareSum, sum_range_succ, frac, mul_add, mul_pow]

-- The common factor in the two binomial sums gains a factor 1 - (p/k)² at each step.
private theorem paired_choose {p : ℕ} (hp : p.Prime) (j : ℕ) (hj : j < p) :
    ((p - 1).choose j : R p) * ((p + j).choose j : R p) =
      (-1) ^ j * (1 - squareSum p j) := by
  induction j with
  | zero => simp [squareSum]
  | succ j ih =>
    have hjp : j < p := by omega
    let k := j + 1
    have hu := unit_of_lt hp (k := k) (by omega) hj
    have ha := congrArg (Nat.cast : ℕ → R p) (Nat.choose_succ_right_eq (p - 1) j)
    have hb := congrArg (Nat.cast : ℕ → R p) (Nat.add_one_mul_choose_eq (p + j) j)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (show j ≤ p - 1 by omega), Nat.cast_sub hp.pos] at ha hb
    change ((p - 1).choose k : R p) * (((p + j + 1).choose k : ℕ) : R p) = _
    apply (hu.mul hu).mul_right_cancel
    calc
      _ = (((p - 1).choose k : R p) * k) * (((p + j + 1).choose k : R p) * k) := by ring
      _ = ((p - 1).choose j : R p) * ((p + j).choose j : R p) *
          ((p : R p) - k) * (p + k) := by
        dsimp [k]
        push_cast
        rw [ha, ← hb]
        ring
      _ = _ := by
        rw [ih hjp, squareSum_succ, pow_succ (-1 : R p)]
        have hx := frac_mul hp (k := k) (by omega) hj
        change _ = (-1) ^ j * -1 * (1 - (squareSum p j + frac p k ^ 2)) * (↑k * ↑k)
        have hx2 := congrArg (fun z : R p => z ^ 2) hx
        rw [mul_pow] at hx2
        unfold squareSum
        linear_combination -((-1 : R p) ^ j) * hx2 -
          (-1 : R p) ^ j * p * (∑ i ∈ range j, ((i + 1 : ℕ) : R p)⁻¹ ^ 2) * cube_zero p

private theorem central_twice (p : ℕ) (hp : 0 < p) :
    (2 * p).choose p = 2 * (2 * p - 1).choose (p - 1) := by
  have h := Nat.choose_succ_succ' (2 * p - 1) (p - 1)
  rw [show 2 * p - 1 + 1 = 2 * p by omega, Nat.sub_add_cancel hp,
    Nat.choose_symm_of_eq_add (show 2 * p - 1 = p + (p - 1) by omega)] at h
  simpa only [two_mul] using h

private theorem central_choose {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((2 * p - 1).choose (p - 1) : R p) = 1 := by
  have hd := (MetaMathlibExt.choose_two_mul_prime_congr_iff_pow_three p 1 1 hp hp5).1.mpr
    (by simp)
  have hc : ((2 * p).choose p : R p) = 2 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by exact_mod_cast hd)
    exact sub_eq_zero.mp (by simpa using h)
  have hu := unit_of_lt hp (k := 2) (by decide) (by omega)
  apply hu.mul_left_cancel
  push_cast
  rw [central_twice p hp.pos, Nat.cast_mul, Nat.cast_ofNat] at hc
  simpa using hc

private theorem interior_terms {p : ℕ} (hp : p.Prime) (j : ℕ) (hj : j + 1 < p) :
    ((p - 1).choose j : R p) * ((p + j).choose (p - 1) : R p) =
        (-1) ^ j * frac p (j + 1) ∧
      (p.choose (j + 1) : R p) * ((p + (j + 1)).choose p : R p) =
        (-1) ^ j * (frac p (j + 1) + frac p (j + 1) ^ 2) := by
  let k := j + 1
  have hu := unit_of_lt hp (k := k) (by omega) hj
  have hx := frac_mul hp (k := k) (by omega) hj
  have hA : (p.choose k : R p) = frac p k * ((p - 1).choose j : R p) := by
    apply hu.mul_right_cancel
    rw [mul_right_comm (frac p k), hx]
    exact_mod_cast congrArg (Nat.cast : ℕ → R p) (show p * (p - 1).choose j = p.choose k * k by
      simpa [k, Nat.sub_add_cancel hp.pos] using Nat.add_one_mul_choose_eq (p - 1) j).symm
  have hB : ((p + k).choose p : R p) = (1 + frac p k) * ((p + j).choose j : R p) := by
    rw [Nat.choose_symm_add]
    apply hu.mul_right_cancel
    rw [mul_right_comm (1 + _), add_mul, one_mul, hx, add_comm (k : R p)]
    exact_mod_cast congrArg (Nat.cast : ℕ → R p) (Nat.add_one_mul_choose_eq (p + j) j).symm
  have hC : ((p + j).choose (p - 1) : R p) = frac p k * ((p + j).choose j : R p) := by
    rw [Nat.choose_symm_of_eq_add (show p + j = (p - 1) + k by omega)]
    apply hu.mul_right_cancel
    rw [mul_right_comm (frac p k), hx, mul_comm (p : R p)]
    exact_mod_cast congrArg (Nat.cast : ℕ → R p)
      (show (p + j).choose k * k = (p + j).choose j * p by
      simpa [k] using Nat.choose_succ_right_eq (p + j) j)
  have hpair := paired_choose hp j (by omega)
  have hzero : frac p k * squareSum p j = 0 := by
    unfold frac squareSum
    linear_combination ((k : R p)⁻¹ * ∑ i ∈ range j, ((i + 1 : ℕ) : R p)⁻¹ ^ 2) * cube_zero p
  constructor
  · rw [hC, mul_left_comm, hpair]
    linear_combination -(-1 : R p) ^ j * hzero
  · change (p.choose k : R p) * ((p + k).choose p : R p) = _
    rw [hA, hB, mul_mul_mul_comm, hpair]
    change _ = (-1) ^ j * (frac p k + frac p k ^ 2)
    linear_combination -(-1 : R p) ^ j * (1 + frac p k) * hzero

private theorem entry_reverse (p a b : ℕ) :
    (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix (a + b) a 1 : R p) =
      ∑ j ∈ range (a + 1), (a.choose j : R p) * ((b + j).choose a : R p) := by
  simp only [MetaMathlibExt.ordinaryRiordanPascalLikeMatrix, one_pow, mul_one,
    Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  rw [← sum_range_reflect (fun j => (a.choose j : R p) * _) (a + 1)]
  apply sum_congr rfl
  intro j hj
  have hja : j ≤ a := by simpa using hj
  simp [Nat.choose_symm hja, show a + b - (a - j) = b + j by omega]

private theorem entries {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix (2 * p) p 1 : R p) =
        3 + ∑ j ∈ range (p - 1), (-1) ^ j * (frac p (j + 1) + frac p (j + 1) ^ 2) ∧
      (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix (2 * p - 1) (p - 1) 1 : R p) =
        1 + ∑ j ∈ range (p - 1), (-1) ^ j * frac p (j + 1) := by
  have hc := central_choose hp hp5
  constructor
  · rw [show 2 * p = p + p by omega, entry_reverse, sum_range_succ']
    have hsplit (f : ℕ → R p) : ∑ i ∈ range p, f i =
        ∑ i ∈ range (p - 1), f i + f (p - 1) := by
      simpa only [Nat.sub_add_cancel hp.pos] using sum_range_succ f (p - 1)
    rw [hsplit]
    simp only [Nat.sub_add_cancel hp.pos, Nat.choose_self, Nat.cast_one, Nat.choose_zero_right,
      Nat.add_zero, one_mul, ← two_mul p, central_twice p hp.pos, Nat.cast_mul, Nat.cast_ofNat, hc,
      mul_one]
    rw [sum_congr rfl (fun j hj => (interior_terms hp j (by have := mem_range.mp hj; omega)).2)]
    ring
  · rw [show 2 * p - 1 = (p - 1) + p by omega, entry_reverse, sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, show p + (p - 1) = 2 * p - 1 by omega, hc]
    rw [sum_congr rfl (fun j hj => (interior_terms hp j (by have := mem_range.mp hj; omega)).1)]
    ring

@[to_additive]
private theorem prod_pairs {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∏ j ∈ range (2 * m), f j =
      (∏ i ∈ range m, f (2 * i)) * ∏ i ∈ range m, f (2 * i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, prod_range_succ,
      prod_range_succ, ih, prod_range_succ, prod_range_succ (fun i => f (2 * i + 1))]
    ac_rfl

-- Pair the odd denominators in increasing order with the even ones in decreasing order.
private theorem sum_reflected_pairs {p m : ℕ} (hm : p = 2 * m + 1) (f : ℕ → R p) :
    ∑ j ∈ range (p - 1), f j =
      ∑ i ∈ range m, (f (2 * i) + f (2 * (m - 1 - i) + 1)) := by
  rw [show p - 1 = 2 * m by omega, sum_pairs, sum_add_distrib,
    sum_range_reflect (fun i => f (2 * i + 1))]

private theorem odd_squares {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : p = 2 * m + 1) :
    ∑ i ∈ range m, frac p (2 * i + 1) ^ 2 = 0 := by
  have h := paired_choose hp (p - 1) (by omega)
  rw [Nat.choose_self, Nat.cast_one, one_mul, show p + (p - 1) = 2 * p - 1 by omega,
    central_choose hp hp5, (show Even (p - 1) from ⟨m, by omega⟩).neg_one_pow, one_mul] at h
  have hs : ∑ j ∈ range (p - 1), frac p (j + 1) ^ 2 = 0 := by
    simp only [frac, mul_pow, ← mul_sum]
    change squareSum p (p - 1) = 0
    linear_combination h
  rw [sum_reflected_pairs hm] at hs
  have he : ∑ i ∈ range m, (frac p (2 * i + 1) ^ 2 + frac p (2 * (m - 1 - i) + 1 + 1) ^ 2) =
      2 * ∑ i ∈ range m, frac p (2 * i + 1) ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [show 2 * (m - 1 - i) + 1 + 1 = p - (2 * i + 1) by omega,
      frac_reflect_sq hp (by omega) (by omega), two_mul (frac _ _ ^ 2)]
  rw [he] at hs
  apply (unit_of_lt hp (k := 2) (by decide) (by omega)).mul_left_cancel
  simpa using hs

private theorem signed_sum {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : p = 2 * m + 1)
    (c : R p) :
    ∑ j ∈ range (p - 1), (-1) ^ j * (frac p (j + 1) + c * frac p (j + 1) ^ 2) =
      ∑ i ∈ range m, (2 * frac p (2 * i + 1) - frac p (2 * i + 1) ^ 2) := by
  rw [sum_reflected_pairs hm]
  calc
    _ = ∑ i ∈ range m, (2 * frac p (2 * i + 1) + frac p (2 * i + 1) ^ 2) := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      simp only [pow_mul, pow_succ (-1 : R p), mul_neg,
        mul_one, neg_mul]
      rw [show 2 * (m - 1 - i) + 1 + 1 = p - (2 * i + 1) by omega,
        frac_reflect_sq hp (by omega) (by omega), frac_reflect hp (by omega) (by omega)]
      ring
    _ = _ := by rw [sum_add_distrib, sum_sub_distrib, odd_squares hp hp5 hm]; simp

-- Double 1,…,p-1. The upper half gives p+1, p+3, …, and the lower half gives the evens.
private theorem doubling_product {p m : ℕ} (hp : p.Prime) (hm : p = 2 * m + 1) :
    ∏ i ∈ range m, (1 + frac p (2 * i + 1)) = (2 : R p) ^ (p - 1) := by
  let odd (i : ℕ) : R p := (2 * i + 1 : ℕ)
  let low (i : ℕ) : R p := (i + 1 : ℕ)
  have hu (i : ℕ) (hi : i ∈ range m) : IsUnit (odd i) :=
    unit_of_lt hp (by omega) (by have := mem_range.mp hi; omega)
  have hl : IsUnit (∏ i ∈ range m, low i) := IsUnit.prod_iff.mpr fun i hi =>
    unit_of_lt hp (by omega) (by have := mem_range.mp hi; omega)
  have hsplit := prod_range_add low m m
  rw [← two_mul m, prod_pairs] at hsplit
  have heven (i : ℕ) : low (2 * i + 1) = 2 * low i := by
    dsimp [low]
    push_cast
    ring
  simp only [heven, prod_mul_distrib, prod_const, card_range] at hsplit
  have hupper : ∏ i ∈ range m, low (m + i) = 2 ^ m * ∏ i ∈ range m, odd i := by
    apply hl.mul_left_cancel
    rw [← hsplit]
    change (∏ i ∈ range m, odd i) * _ = _
    ring
  apply (IsUnit.prod_iff.mpr hu).mul_right_cancel
  rw [← prod_mul_distrib]
  calc
    _ = ∏ i ∈ range m, (2 * low (m + i)) := by
      apply prod_congr rfl
      intro i hi
      rw [add_mul, one_mul, show frac p (2 * i + 1) * odd i = p from
        frac_mul hp (by omega) (by have := mem_range.mp hi; omega)]
      dsimp [odd, low]
      rw [show (p : R p) = ((2 * m + 1 : ℕ) : R p) from congrArg Nat.cast hm]
      push_cast
      ring
    _ = _ := by
      rw [prod_mul_distrib, prod_const, card_range, hupper, ← mul_assoc, ← pow_add,
        show m + m = p - 1 by omega]

-- The polynomial 2t-t² takes products of 1+t to sums when every t is a multiple of p.
private theorem product_expansion (p : ℕ) (f : ℕ → R p) (m : ℕ) :
    let t := (∏ i ∈ range m, (1 + p * f i)) - 1
    2 * t - t ^ 2 = ∑ i ∈ range m, (2 * (p * f i) - (p * f i) ^ 2) := by
  have aux (n : ℕ) : ∃ u : R p, (∏ i ∈ range n, (1 + p * f i)) = 1 + p * u := by
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨u, hu⟩ := ih
      exact ⟨u + f n + p * u * f n, by rw [prod_range_succ, hu]; ring⟩
  dsimp only
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨u, hu⟩ := aux m
    rw [prod_range_succ, sum_range_succ, hu]
    rw [hu] at ih
    linear_combination ih - (u * f m * (2 * u + 2 * f m + p * u * f m)) * cube_zero p

/-- **Delannoy triangle entries $T(2p, p; 1)$ and $T(2p-1, p-1; 1)$ modulo $p^3$.** Let
$p \ge 5$ be a prime, let $q_p(2) = (2^{p-1} - 1)/p$ be the Fermat quotient of $2$, and let
$T(n, k; 1)$ denote the entry of the ordinary Riordan Pascal-like triangle with $r = 1$ (the
Delannoy triangle). Then
$$T(2p, p; 1) \equiv 3 + 2p\,q_p(2) - p^2 q_p(2)^2 \pmod{p^3}$$
and
$$T(2p-1, p-1; 1) \equiv 1 + 2p\,q_p(2) - p^2 q_p(2)^2 \pmod{p^3}.$$

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Theorem 1. -/
public theorem delannoy_two_mul (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
          (2 * p) p 1 : ZMod (p ^ 3)) =
        3 + 2 * (p : ZMod (p ^ 3)) *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) -
          (p : ZMod (p ^ 3)) ^ 2 *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) ^ 2 ∧
      (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
            (2 * p - 1) (p - 1) 1 : ZMod (p ^ 3)) =
        1 + 2 * (p : ZMod (p ^ 3)) *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) -
          (p : ZMod (p ^ 3)) ^ 2 *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) ^ 2 := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  have hprod := product_expansion p (fun i => ((2 * i + 1 : ℕ) : R p)⁻¹) m
  change 2 * ((∏ i ∈ range m, (1 + frac p (2 * i + 1))) - 1) -
      ((∏ i ∈ range m, (1 + frac p (2 * i + 1))) - 1) ^ 2 =
      ∑ i ∈ range m, (2 * frac p (2 * i + 1) - frac p (2 * i + 1) ^ 2) at hprod
  rw [doubling_product hp hm] at hprod
  have hq := congrArg (Int.cast : ℤ → R p) (Int.natCast_mul_fermatQuotient p hp 2 h2p)
  push_cast at hq
  rw [← hq] at hprod
  have h := entries hp hp5
  have h₁ := signed_sum hp hp5 hm 1
  have h₀ := signed_sum hp hp5 hm 0
  simp only [one_mul, zero_mul, add_zero, ← hprod] at h₁ h₀
  constructor
  · rw [h.1, h₁]
    ring
  · rw [h.2, h₀]
    ring

end MathlibExt.NumberTheory.DelannoyTriangleWanted
