/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GobelResidueExponentPeriod
public import MathlibExt.NumberTheory.GobelSequence
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Failure of Göbel residues detects non-integrality

This module proves that the residue sequence `g_{k,p,r}(n)` takes the failure value if and only
if the $(k, 2)$-Göbel sequence has negative $p$-adic valuation at $n$.

## Main statements

* `MetaMathlibExt.gobelResidue_eq_none_iff`: failure detects non-integrality.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Lemma 2.
-/

namespace MetaMathlibExt

@[expose] public section

-- Helper 1: positivity
private theorem gobelSequence_pos (k n : ℕ) (hn : 1 ≤ n) :
    0 < gobelSequence k 2 n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [gobelSequence_one]
    norm_num
  | succ m hm ih =>
    have hrec := gobelSequence_succ k 2 m hm
    have hpow : 0 < gobelSequence k 2 m ^ (k - 1) := pow_pos ih _
    have hm' : (0 : ℚ) ≤ m := Nat.cast_nonneg _
    have hrhs : 0 < gobelSequence k 2 m * ((m : ℚ) + gobelSequence k 2 m ^ (k - 1)) :=
      mul_pos ih (add_pos_of_nonneg_of_pos hm' hpow)
    rw [← hrec] at hrhs
    have hpos : (0 : ℚ) < m + 1 := by positivity
    exact pos_of_mul_pos_right hrhs hpos.le

-- Helper 2: factorial valuation monotonicity
private theorem padicValNat_factorial_mono (p n m : ℕ) (h : n ≤ m) :
    padicValNat p n.factorial ≤ padicValNat p m.factorial := by
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [padicValNat]
  · rw [Nat.padicValNat_def, Nat.padicValNat_def]
    rw [← Nat.pow_dvd_iff_le_multiplicity hp1 (Nat.factorial_ne_zero m)]
    exact (pow_multiplicity_dvd p n.factorial).trans (Nat.factorial_dvd_factorial h)

-- Helper 3: factorial succ valuation
private theorem padicValNat_factorial_succ (p n : ℕ) (hp : p.Prime) :
    padicValNat p (n + 1).factorial = padicValNat p n.factorial + padicValNat p (n + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorial_succ, Nat.padicValNat_def, Nat.padicValNat_def, Nat.padicValNat_def,
    Nat.multiplicity_mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n), add_comm]

-- Helper 4: negativity propagates
private theorem gobelSequence_neg_propagates (p k n : ℕ) (hp : p.Prime) (hk : 2 ≤ k)
    (hn : 1 ≤ n) (hneg : padicValRat p (gobelSequence k 2 n) < 0) :
    padicValRat p (gobelSequence k 2 (n + 1)) < 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hgpos := gobelSequence_pos k n hn
  have hgne : gobelSequence k 2 n ≠ 0 := ne_of_gt hgpos
  have hnne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsucc_ne : (n : ℚ) + 1 ≠ 0 := by positivity
  -- valuations of the two summands
  have hpow_val : padicValRat p ((gobelSequence k 2 n) ^ k)
      = k * padicValRat p (gobelSequence k 2 n) := padicValRat.pow _
  have hmul_val : padicValRat p ((n : ℚ) * gobelSequence k 2 n)
      = padicValRat p (n : ℚ) + padicValRat p (gobelSequence k 2 n) :=
    padicValRat.mul hnne hgne
  have hn_nonneg : 0 ≤ padicValRat p (n : ℚ) := zero_le_padicValRat_of_nat n
  -- k * v < v(n) + v since (k-1)*v < 0 ≤ v(n)
  have hlt : padicValRat p ((gobelSequence k 2 n) ^ k)
      < padicValRat p ((n : ℚ) * gobelSequence k 2 n) := by
    rw [hpow_val, hmul_val]
    have h1 : (k : ℤ) * padicValRat p (gobelSequence k 2 n)
        < 1 * padicValRat p (gobelSequence k 2 n) := by
      apply mul_lt_mul_of_neg_right _ hneg
      norm_num
      omega
    rw [one_mul] at h1
    linarith
  have hterm1_ne : (n : ℚ) * gobelSequence k 2 n ≠ 0 := mul_ne_zero hnne hgne
  have hterm2_ne : (gobelSequence k 2 n) ^ k ≠ 0 := pow_ne_zero k hgne
  -- sum is nonzero since valuations differ
  have hsum_ne : (n : ℚ) * gobelSequence k 2 n + (gobelSequence k 2 n) ^ k ≠ 0 := by
    intro h0
    have heq : (n : ℚ) * gobelSequence k 2 n = -((gobelSequence k 2 n) ^ k) :=
      eq_neg_of_add_eq_zero_left h0
    have hval_eq : padicValRat p ((n : ℚ) * gobelSequence k 2 n)
        = padicValRat p ((gobelSequence k 2 n) ^ k) := by
      rw [heq, padicValRat.neg]
    omega
  have hsum_ne' : (gobelSequence k 2 n) ^ k + (n : ℚ) * gobelSequence k 2 n ≠ 0 := by
    rwa [add_comm]
  have hsum_val : padicValRat p ((n : ℚ) * gobelSequence k 2 n + (gobelSequence k 2 n) ^ k)
      = padicValRat p ((gobelSequence k 2 n) ^ k) := by
    rw [add_comm]
    exact padicValRat.add_eq_of_lt hsum_ne' hterm2_ne hterm1_ne hlt
  -- relate to G (n+1)
  have hrec := gobelSequence_succ k 2 n hn
  rw [mul_add, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k),
    mul_comm (gobelSequence k 2 n) (n : ℚ)] at hrec
  -- hrec : (n+1) * G(n+1) = n * g + g^k
  have hG : gobelSequence k 2 (n + 1)
      = ((n : ℚ) * gobelSequence k 2 n + (gobelSequence k 2 n) ^ k) / (n + 1) := by
    field_simp
    linarith
  rw [hG]
  rw [padicValRat.div hsum_ne hsucc_ne]
  rw [hsum_val, hpow_val]
  have hnp1_nonneg : 0 ≤ padicValRat p (((n : ℚ) + 1)) := by
    have : (((n : ℚ) + 1)) = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [this]
    exact zero_le_padicValRat_of_nat _
  have hkval : (k : ℤ) * padicValRat p (gobelSequence k 2 n) < 0 := by
    apply mul_neg_of_pos_of_neg _ hneg
    norm_num
    omega
  linarith

-- Helper: denominator not divisible by p when valuation nonnegative
private theorem den_not_dvd_of_nonneg (p : ℕ) (hp : p.Prime) (x : ℚ)
    (hx : 0 ≤ padicValRat p x) : ¬ p ∣ x.den := by
  have hden_ne : x.den ≠ 0 := Rat.den_nz x
  have hprime_ne1 : p ≠ 1 := hp.ne_one
  rcases Rat.num_or_den_zero_padicVal x hp with hnum | hden
  · -- num valuation zero, so den valuation must be zero
    have hdef : padicValRat p x = padicValInt p x.num - multiplicity p x.den := by
      rfl
    rw [hnum] at hdef
    -- hdef : v = 0 - mult(den), with 0 ≤ v
    have hmult_eq : multiplicity p x.den = 0 := by
      omega
    rw [Nat.multiplicity_eq_zero_iff] at hmult_eq
    rcases hmult_eq with rfl | h0 | hndvd
    · exact absurd rfl hprime_ne1
    · exact absurd h0 hden_ne
    · exact hndvd
  · rw [Nat.multiplicity_eq_zero_iff] at hden
    rcases hden with rfl | h0 | hndvd
    · exact absurd rfl hprime_ne1
    · exact absurd h0 hden_ne
    · exact hndvd

-- Helper: denominator is a unit mod p^t
private theorem isUnit_den (p D t : ℕ) (hp : p.Prime) (hD : ¬ p ∣ D) :
    IsUnit (D : ZMod (p ^ t)) := by
  rw [ZMod.isUnit_iff_coprime]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have hcop_p : D.Coprime p := by
      rw [Nat.coprime_comm]
      exact (hp.coprime_iff_not_dvd).mpr hD
    exact hcop_p.pow_right _

-- Helper: p'-part of n+1 is not divisible by p
private theorem pprime_part_not_dvd (p n : ℕ) (hp : p.Prime) :
    ¬ p ∣ (n + 1) / p ^ padicValNat p (n + 1) := by
  have hp1 : 1 < p := hp.one_lt
  have hn_ne : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have hpow_ne : p ^ padicValNat p (n + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have heq := Nat.divMaxPow_mul_pow_padicValNat p (n + 1)
  -- heq : divMaxPow (n+1) p * p^v = n+1
  have hdiv_eq : (n + 1) / p ^ padicValNat p (n + 1) = Nat.divMaxPow (n + 1) p :=
    Nat.div_eq_of_eq_mul_left (pow_pos hp.pos _) heq.symm
  rw [hdiv_eq]
  exact Nat.not_dvd_divMaxPow hp1 hn_ne

-- Well-definedness of ratResidue: any representation with unit denominator gives same value
private theorem ratResidue_mk (m : ℕ) (q : ℚ) (n d : ℤ) (hd : d ≠ 0)
    (hq : q = Rat.divInt n d)
    (hdU : IsUnit (d : ZMod m)) (hdenU : IsUnit ((q.den : ℕ) : ZMod m)) :
    ratResidue m q = (n : ZMod m) * (d : ZMod m)⁻¹ := by
  obtain ⟨c, hc1, hc2⟩ := Rat.num_den_mk hd hq
  -- hc1 : n = c * num, hc2 : d = c * den
  have heq : n * (q.den : ℤ) = q.num * d := by
    rw [hc1, hc2]
    ring
  have heq_mod : (n : ZMod m) * ((q.den : ℕ) : ZMod m)
      = (q.num : ZMod m) * (d : ZMod m) := by
    have h := congrArg (fun z : ℤ => (z : ZMod m)) heq
    simpa [Int.cast_mul, Int.cast_natCast] using h
  -- multiply by inverses
  have hd_inv : (d : ZMod m) * (d : ZMod m)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hdU
  have hden_inv : ((q.den : ℕ) : ZMod m) * (((q.den : ℕ) : ZMod m))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hdenU
  -- ratResidue = num * den⁻¹, show equals n * d⁻¹
  unfold ratResidue
  -- from heq_mod: n * den = num * d, so n * d⁻¹ = num * den⁻¹
  have hcalc : (q.num : ZMod m) * (((q.den : ℕ) : ZMod m))⁻¹
      = (n : ZMod m) * (d : ZMod m)⁻¹ := by
    -- multiply heq_mod on right by den⁻¹ * d⁻¹
    have h1 : ((n : ZMod m) * ((q.den : ℕ) : ZMod m))
        * ((((q.den : ℕ) : ZMod m))⁻¹ * (d : ZMod m)⁻¹)
        = ((q.num : ZMod m) * (d : ZMod m))
        * ((((q.den : ℕ) : ZMod m))⁻¹ * (d : ZMod m)⁻¹) := by
      rw [heq_mod]
    have hlhs : ((n : ZMod m) * ((q.den : ℕ) : ZMod m))
        * ((((q.den : ℕ) : ZMod m))⁻¹ * (d : ZMod m)⁻¹)
        = (n : ZMod m) * (d : ZMod m)⁻¹ := by
      calc
        _ = (n : ZMod m) * ((((q.den : ℕ) : ZMod m)
          * (((q.den : ℕ) : ZMod m))⁻¹) * (d : ZMod m)⁻¹) := by ring
        _ = (n : ZMod m) * (d : ZMod m)⁻¹ := by rw [hden_inv, one_mul]
    have hrhs : ((q.num : ZMod m) * (d : ZMod m))
        * ((((q.den : ℕ) : ZMod m))⁻¹ * (d : ZMod m)⁻¹)
        = (q.num : ZMod m) * ((((q.den : ℕ) : ZMod m))⁻¹) := by
      calc
        _ = (q.num : ZMod m) * (((d : ZMod m) * (d : ZMod m)⁻¹)
          * ((((q.den : ℕ) : ZMod m))⁻¹)) := by ring
        _ = (q.num : ZMod m) * ((((q.den : ℕ) : ZMod m))⁻¹) := by
          rw [hd_inv, one_mul]
    rw [hlhs, hrhs] at h1
    exact h1.symm
  exact hcalc

-- Helper: inverse of product for units in ZMod
private theorem zmod_mul_inv_of_unit (m : ℕ) (a b : ZMod m) (ha : IsUnit a)
    (hb : IsUnit b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  apply ZMod.inv_eq_of_mul_eq_one m _ _ _
  have ha1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit _ ha
  have hb1 : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit _ hb
  calc
    (a * b) * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by ring
    _ = 1 := by rw [ha1, hb1, mul_one]

-- Helper: ratResidue preserves addition on p-integral rationals
private theorem ratResidue_add (p t : ℕ) (hp : p.Prime) (x y : ℚ)
    (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) :
    ratResidue (p ^ t) (x + y) = ratResidue (p ^ t) x + ratResidue (p ^ t) y := by
  have : Fact p.Prime := ⟨hp⟩
  have hxU : IsUnit ((x.den : ℕ) : ZMod (p ^ t)) :=
    isUnit_den p x.den t hp (den_not_dvd_of_nonneg p hp x hx)
  have hyU : IsUnit ((y.den : ℕ) : ZMod (p ^ t)) :=
    isUnit_den p y.den t hp (den_not_dvd_of_nonneg p hp y hy)
  have hxy_nonneg : 0 ≤ padicValRat p (x + y) := by
    by_cases h0 : x + y = 0
    · simp [h0]
    · have hmin := padicValRat.min_le_padicValRat_add (p := p) h0
      have hle : 0 ≤ min (padicValRat p x) (padicValRat p y) := le_min hx hy
      exact le_trans hle hmin
  have hxyU : IsUnit ((((x + y).den : ℕ)) : ZMod (p ^ t)) :=
    isUnit_den p (x + y).den t hp (den_not_dvd_of_nonneg p hp (x + y) hxy_nonneg)
  -- representation of x + y
  have hadd := Rat.add_num_den x y
  -- hadd : x + y = (x.num * y.den + x.den * y.num) /. (x.den * y.den)
  have hd_ne : (((x.den : ℤ) * (y.den : ℤ) : ℤ)) ≠ 0 := by
    have hxpos : (0 : ℤ) < x.den := by exact_mod_cast x.pos
    have hypos : (0 : ℤ) < y.den := by exact_mod_cast y.pos
    exact mul_ne_zero (ne_of_gt hxpos) (ne_of_gt hypos)
  have hdU : IsUnit (((((x.den : ℤ) * (y.den : ℤ) : ℤ))) : ZMod (p ^ t)) := by
    have h_eq : (((((x.den : ℤ) * (y.den : ℤ) : ℤ))) : ZMod (p ^ t))
        = ((x.den : ℕ) : ZMod (p ^ t)) * ((y.den : ℕ) : ZMod (p ^ t)) := by
      push_cast
      ring
    rw [h_eq]
    exact IsUnit.mul hxU hyU
  have hmk := ratResidue_mk (p ^ t) (x + y) (x.num * y.den + x.den * y.num)
    ((x.den : ℤ) * y.den) hd_ne hadd hdU hxyU
  rw [hmk]
  unfold ratResidue
  -- need: (n)*(d)⁻¹ = num_x*den_x⁻¹ + num_y*den_y⁻¹
  have hd_eq : (((((x.den : ℤ) * (y.den : ℤ) : ℤ))) : ZMod (p ^ t))
      = ((x.den : ℕ) : ZMod (p ^ t)) * ((y.den : ℕ) : ZMod (p ^ t)) := by
    push_cast
    ring
  have hn_eq : ((((x.num * (y.den : ℤ) + (x.den : ℤ) * y.num : ℤ))) : ZMod (p ^ t))
      = (x.num : ZMod (p ^ t)) * ((y.den : ℕ) : ZMod (p ^ t))
        + ((x.den : ℕ) : ZMod (p ^ t)) * (y.num : ZMod (p ^ t)) := by
    push_cast
    ring
  rw [hn_eq, hd_eq, zmod_mul_inv_of_unit _ _ _ hxU hyU]
  have hx_inv : ((x.den : ℕ) : ZMod (p ^ t)) * (((x.den : ℕ) : ZMod (p ^ t)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hxU
  have hy_inv : ((y.den : ℕ) : ZMod (p ^ t)) * (((y.den : ℕ) : ZMod (p ^ t)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hyU
  -- (a*d + c*b)*(c⁻¹*d⁻¹) = a*c⁻¹ + b*d⁻¹? need ring + inv cancellations
  -- Use linear combination: LHS = a*c⁻¹*(d*d⁻¹) + b*d⁻¹*(c*c⁻¹)
  calc
    ((x.num : ZMod (p ^ t)) * ((y.den : ℕ) : ZMod (p ^ t))
        + ((x.den : ℕ) : ZMod (p ^ t)) * (y.num : ZMod (p ^ t)))
        * ((((x.den : ℕ) : ZMod (p ^ t)))⁻¹ * ((((y.den : ℕ) : ZMod (p ^ t)))⁻¹))
        = (x.num : ZMod (p ^ t)) * ((((x.den : ℕ) : ZMod (p ^ t)))⁻¹)
          * (((y.den : ℕ) : ZMod (p ^ t)) * ((((y.den : ℕ) : ZMod (p ^ t)))⁻¹))
          + (y.num : ZMod (p ^ t)) * ((((y.den : ℕ) : ZMod (p ^ t)))⁻¹)
          * (((x.den : ℕ) : ZMod (p ^ t)) * ((((x.den : ℕ) : ZMod (p ^ t)))⁻¹)) := by
      ring
    _ = (x.num : ZMod (p ^ t)) * ((((x.den : ℕ) : ZMod (p ^ t)))⁻¹)
          + (y.num : ZMod (p ^ t)) * ((((y.den : ℕ) : ZMod (p ^ t)))⁻¹) := by
      rw [hy_inv, hx_inv, mul_one, mul_one]

private theorem ratResidue_natCast (m : ℕ) (n : ℕ) :
    ratResidue m (n : ℚ) = (n : ZMod m) := by
  simp [ratResidue]

private theorem ratResidue_one (m : ℕ) : ratResidue m 1 = 1 := by
  simp [ratResidue]

-- Helper: ratResidue preserves multiplication on p-integral rationals
private theorem ratResidue_mul (p t : ℕ) (hp : p.Prime) (x y : ℚ)
    (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) :
    ratResidue (p ^ t) (x * y) = ratResidue (p ^ t) x * ratResidue (p ^ t) y := by
  have : Fact p.Prime := ⟨hp⟩
  have hxU : IsUnit ((x.den : ℕ) : ZMod (p ^ t)) :=
    isUnit_den p x.den t hp (den_not_dvd_of_nonneg p hp x hx)
  have hyU : IsUnit ((y.den : ℕ) : ZMod (p ^ t)) :=
    isUnit_den p y.den t hp (den_not_dvd_of_nonneg p hp y hy)
  have hxy_nonneg : 0 ≤ padicValRat p (x * y) := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · by_cases hy0 : y = 0
      · simp [hy0]
      · rw [padicValRat.mul hx0 hy0]
        exact add_nonneg hx hy
  have hxyU : IsUnit ((((x * y).den : ℕ)) : ZMod (p ^ t)) :=
    isUnit_den p (x * y).den t hp (den_not_dvd_of_nonneg p hp (x * y) hxy_nonneg)
  have hmul_eq : x * y = Rat.divInt (x.num * y.num) ((x.den * y.den : ℕ) : ℤ) := by
    rw [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt]
  have hd_ne : (((x.den * y.den : ℕ) : ℤ)) ≠ 0 := by
    have hpos : (0 : ℕ) < x.den * y.den := Nat.mul_pos x.pos y.pos
    exact_mod_cast Nat.ne_of_gt hpos
  have hdU : IsUnit (((((x.den * y.den : ℕ) : ℤ))) : ZMod (p ^ t)) := by
    rw [Int.cast_natCast]
    have h_eq : (((x.den * y.den : ℕ)) : ZMod (p ^ t))
        = ((x.den : ℕ) : ZMod (p ^ t)) * ((y.den : ℕ) : ZMod (p ^ t)) := by
      push_cast
      ring
    rw [h_eq]
    exact IsUnit.mul hxU hyU
  have hmk := ratResidue_mk (p ^ t) (x * y) (x.num * y.num)
    ((x.den * y.den : ℕ) : ℤ) hd_ne hmul_eq hdU hxyU
  rw [hmk]
  unfold ratResidue
  have hd_eq : (((((x.den * y.den : ℕ) : ℤ))) : ZMod (p ^ t))
      = ((x.den : ℕ) : ZMod (p ^ t)) * ((y.den : ℕ) : ZMod (p ^ t)) := by
    push_cast
    ring
  have hn_eq : (((x.num * y.num : ℤ)) : ZMod (p ^ t))
      = (x.num : ZMod (p ^ t)) * (y.num : ZMod (p ^ t)) := by
    push_cast
    ring
  rw [hn_eq, hd_eq, zmod_mul_inv_of_unit _ _ _ hxU hyU]
  ring

-- Helper: ratResidue preserves powers on p-integral rationals
private theorem ratResidue_pow (p t : ℕ) (hp : p.Prime) (x : ℚ)
    (hx : 0 ≤ padicValRat p x) (k : ℕ) :
    ratResidue (p ^ t) (x ^ k) = (ratResidue (p ^ t) x) ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  induction k with
  | zero =>
    simp [ratResidue_one]
  | succ k ih =>
    have hx_pow_nonneg : 0 ≤ padicValRat p (x ^ k) := by
      by_cases hx0 : x = 0
      · by_cases hk0 : k = 0
        · simp [hk0]
        · simp [hx0, hk0]
      · rw [padicValRat.pow]
        exact mul_nonneg (Nat.cast_nonneg k) hx
    have hmul := ratResidue_mul p t hp (x ^ k) x hx_pow_nonneg hx
    rw [pow_succ, hmul, ih, pow_succ]

-- Key lemma: val mod p^v vanishes iff p^v divides numerator
private theorem val_mod_pow_dvd_iff (p t v A B : ℕ) (hp : p.Prime) (hvt : v ≤ t)
    (hB : ¬ p ∣ B) :
    (((A : ZMod (p ^ t)) * (B : ZMod (p ^ t))⁻¹).val % p ^ v = 0 ↔ p ^ v ∣ A) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · -- modulus 1: both sides true since v = 0
    have hv0 : v = 0 := by omega
    subst hv0
    simp [Nat.mod_one]
  · have hm_ne : p ^ t ≠ 0 := pow_ne_zero _ hp.ne_zero
    have : NeZero (p ^ t) := ⟨hm_ne⟩
    have hB_unit : IsUnit (B : ZMod (p ^ t)) := isUnit_den p B t hp hB
    -- C is the val of B⁻¹
    set C := ((B : ZMod (p ^ t))⁻¹).val with hC
    have hB_inv_eq : (B : ZMod (p ^ t))⁻¹ = (C : ZMod (p ^ t)) :=
      (ZMod.natCast_zmod_val _).symm
    have hy_eq : (A : ZMod (p ^ t)) * (B : ZMod (p ^ t))⁻¹
        = ((A * C : ℕ) : ZMod (p ^ t)) := by
      rw [hB_inv_eq, ← Nat.cast_mul]
    have hy_val : ((A : ZMod (p ^ t)) * (B : ZMod (p ^ t))⁻¹).val
        = (A * C) % p ^ t := by
      rw [hy_eq, ZMod.val_natCast]
    rw [hy_val]
    have hmod : (A * C) % p ^ t % p ^ v = (A * C) % p ^ v :=
      Nat.mod_mod_of_dvd _ (pow_dvd_pow p hvt)
    rw [hmod]
    rw [Nat.dvd_iff_mod_eq_zero]
    -- now goal: p^v ∣ A*C ↔ p^v ∣ A, using Coprime C (p^v)
    -- show ¬ p ∣ C
    have hC_not_dvd : ¬ p ∣ C := by
      intro hCp
      -- B * C ≡ 1 mod p^t, so mod p gives 0 ≡ 1, contradiction (t > 0)
      have hBC1 : (B : ZMod (p ^ t)) * (C : ZMod (p ^ t)) = 1 := by
        rw [← hB_inv_eq]
        exact ZMod.mul_inv_of_unit _ hB_unit
      have hBC_nat : ((B * C : ℕ) : ZMod (p ^ t)) = ((1 : ℕ) : ZMod (p ^ t)) := by
        rw [Nat.cast_mul]
        simpa [Nat.cast_one] using hBC1
      rw [ZMod.natCast_eq_natCast_iff'] at hBC_nat
      -- hBC_nat : (B*C) % p^t = 1 % p^t
      have hp_dvd_m : p ∣ p ^ t := dvd_pow_self p ht0
      -- reduce mod p
      have h1 : (B * C) % p = 1 % p := by
        have h1a : (B * C) % p ^ t % p = (1 % p ^ t) % p := by rw [hBC_nat]
        rw [Nat.mod_mod_of_dvd _ hp_dvd_m, Nat.mod_mod_of_dvd _ hp_dvd_m] at h1a
        exact h1a
      have hBC_dvd : p ∣ B * C := Dvd.dvd.mul_left hCp B
      rw [Nat.dvd_iff_mod_eq_zero] at hBC_dvd
      rw [hBC_dvd] at h1
      have h1p : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
      rw [h1p] at h1
      omega
    have hcop : C.Coprime (p ^ v) := by
      have hcop_p : C.Coprime p := by
        rw [Nat.coprime_comm]
        exact (hp.coprime_iff_not_dvd).mpr hC_not_dvd
      exact hcop_p.pow_right v
    constructor
    · intro hdiv
      have h_dvd : p ^ v ∣ A * C := Nat.dvd_of_mod_eq_zero hdiv
      have h_A : p ^ v ∣ A := hcop.symm.dvd_of_dvd_mul_right h_dvd
      exact Nat.mod_eq_zero_of_dvd h_A
    · intro hdiv
      have h_A : p ^ v ∣ A := Nat.dvd_of_mod_eq_zero hdiv
      have h_AC : p ^ v ∣ A * C := h_A.trans (dvd_mul_right A C)
      exact Nat.mod_eq_zero_of_dvd h_AC

-- Helper: residue val divisibility corresponds to valuation bound
private theorem residue_val_mod_eq_zero_iff (p t v : ℕ) (hp : p.Prime) (hvt : v ≤ t)
    (S : ℚ) (hS_pos : 0 < S) (hS_nonneg : 0 ≤ padicValRat p S) :
    ((ratResidue (p ^ t) S).val % p ^ v = 0 ↔ (v : ℤ) ≤ padicValRat p S) := by
  have hnum_pos : 0 < S.num := Rat.num_pos.mpr hS_pos
  have hnum_ne : S.num ≠ 0 := ne_of_gt hnum_pos
  have hnum_nonneg : 0 ≤ S.num := le_of_lt hnum_pos
  -- A is natAbs of num
  set A := S.num.natAbs with hA
  have hA_ne : A ≠ 0 := by
    rw [hA]
    exact Int.natAbs_ne_zero.mpr hnum_ne
  have hA_eq : ((A : ℕ) : ℤ) = S.num := Int.natAbs_of_nonneg hnum_nonneg
  -- den multiplicity is zero
  have hden_mult : multiplicity p S.den = 0 := by
    rcases Rat.num_or_den_zero_padicVal S hp with hnum0 | hden0
    · have hdef : padicValRat p S = padicValInt p S.num - multiplicity p S.den := by
        rfl
      rw [hnum0] at hdef
      omega
    · exact hden0
  have hden_not_dvd : ¬ p ∣ S.den := den_not_dvd_of_nonneg p hp S hS_nonneg
  -- valuation equals num valuation
  have hval_eq : padicValRat p S = (padicValInt p S.num : ℤ) := by
    have hdef : padicValRat p S = padicValInt p S.num - multiplicity p S.den := by
      rfl
    rw [hden_mult] at hdef
    simpa using hdef
  -- padicValInt = multiplicity of A
  have hval_int : padicValInt p S.num = multiplicity p A := by
    rw [hA]
    rfl
  -- ratResidue in terms of A
  have hres_eq : ratResidue (p ^ t) S
      = (A : ZMod (p ^ t)) * ((S.den : ℕ) : ZMod (p ^ t))⁻¹ := by
    unfold ratResidue
    have hcast : (S.num : ZMod (p ^ t)) = (A : ZMod (p ^ t)) := by
      conv_lhs => rw [← hA_eq]
      rw [Int.cast_natCast]
    rw [hcast]
  rw [hres_eq]
  rw [val_mod_pow_dvd_iff p t v A S.den hp hvt hden_not_dvd]
  -- now: p^v ∣ A ↔ (v:ℤ) ≤ v(S)
  rw [Nat.pow_dvd_iff_le_multiplicity hp.ne_one hA_ne]
  rw [hval_eq, hval_int]
  norm_cast

private theorem gobelResidue_eq_none_iff_aux (k p r : ℕ) (hk : 2 ≤ k) (_hr : 1 ≤ r)
    (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    padicValNat p n.factorial ≤ r →
    ((gobelResidue k p r n = none ↔ padicValRat p (gobelSequence k 2 n) < 0)
      ∧ ∀ a : ℕ, gobelResidue k p r n = some a →
        ((a : ℕ) : ZMod (p ^ (r - padicValNat p n.factorial)))
          = ratResidue (p ^ (r - padicValNat p n.factorial)) (gobelSequence k 2 n)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro hnr
    constructor
    · simp only [gobelResidue, Option.some_ne_none, false_iff]
      rw [gobelSequence_one]
      exact not_lt.mpr (zero_le_padicValRat_of_nat 2)
    · intro a ha
      simp only [gobelResidue, Option.some_inj] at ha
      subst ha
      have hfact1 : (1 : ℕ).factorial = 1 := rfl
      have hval0 : padicValNat p (1 : ℕ).factorial = 0 := by
        rw [hfact1, Nat.padicValNat_def]
        simp
      rw [hval0, Nat.sub_zero, gobelSequence_one, ratResidue_natCast]
      exact ZMod.natCast_mod 2 (p ^ r)
  | succ m hm ih =>
    intro hnr_succ
    -- v(m!) ≤ r from v((m+1)!) ≤ r
    have hmono : padicValNat p m.factorial ≤ padicValNat p (m + 1).factorial :=
      padicValNat_factorial_mono p m (m + 1) (Nat.le_succ m)
    have hnr_m : padicValNat p m.factorial ≤ r := le_trans hmono hnr_succ
    obtain ⟨ih_iff, ih_corr⟩ := ih hnr_m
    -- split on R m
    cases hRm : gobelResidue k p r m with
    | none =>
      have hneg_m : padicValRat p (gobelSequence k 2 m) < 0 := ih_iff.mp hRm
      have hneg_succ : padicValRat p (gobelSequence k 2 (m + 1)) < 0 :=
        gobelSequence_neg_propagates p k m hp hk hm hneg_m
      obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
      have hR_next : gobelResidue k p r (m0 + 1 + 1) = none := by
        simp [gobelResidue, hRm]
      constructor
      · exact iff_of_true hR_next hneg_succ
      · intro a ha
        rw [hR_next] at ha
        cases ha
    | some a =>
      have hR_ne_none : gobelResidue k p r m ≠ none := by
        rw [hRm]
        exact Option.some_ne_none a
      have hnot_neg : ¬ padicValRat p (gobelSequence k 2 m) < 0 :=
        mt ih_iff.mpr hR_ne_none
      have hg_nonneg : 0 ≤ padicValRat p (gobelSequence k 2 m) := le_of_not_gt hnot_neg
      have ha_corr := ih_corr a hRm
      -- positivity and S
      have hg_pos := gobelSequence_pos k m hm
      have hgne : gobelSequence k 2 m ≠ 0 := ne_of_gt hg_pos
      -- obtain m0 for unfolding
      obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
      -- Now prev is m0+1, next is m0+1+1.
      have : Fact p.Prime := ⟨hp⟩
      -- S and its positivity
      set g : ℚ := gobelSequence k 2 (m0 + 1) with hg_def
      have hg_pos' : 0 < g := hg_pos
      have hg_ne' : g ≠ 0 := hgne
      set S : ℚ := (((m0 + 1 : ℕ)) : ℚ) * g + g ^ k with hS_def
      have hm_pos : (0 : ℚ) < (m0 + 1 : ℕ) := by positivity
      have hS_pos : 0 < S := by
        rw [hS_def]
        exact add_pos (mul_pos (by exact_mod_cast hm_pos) hg_pos') (pow_pos hg_pos' k)
      have hS_ne : S ≠ 0 := ne_of_gt hS_pos
      have hm_ne_Q : ((m0 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hm_nonneg_Q : 0 ≤ padicValRat p (((m0 + 1 : ℕ)) : ℚ) :=
        zero_le_padicValRat_of_nat _
      have hmg_nonneg : 0 ≤ padicValRat p (((m0 + 1 : ℕ) : ℚ) * g) := by
        rw [padicValRat.mul hm_ne_Q hg_ne']
        exact add_nonneg hm_nonneg_Q hg_nonneg
      have hgk_nonneg : 0 ≤ padicValRat p (g ^ k) := by
        rw [padicValRat.pow]
        exact mul_nonneg (Nat.cast_nonneg k) hg_nonneg
      have hS_nonneg : 0 ≤ padicValRat p S := by
        rw [hS_def]
        have hmin := padicValRat.min_le_padicValRat_add (p := p) hS_ne
        exact le_trans (le_min hmg_nonneg hgk_nonneg) hmin
      -- precision and valuations
      set t : ℕ := r - padicValNat p (m0 + 1).factorial with ht_def
      set v : ℕ := padicValNat p (m0 + 1 + 1) with hv_def
      have hvt : v ≤ t := by
        have h1 : padicValNat p (m0 + 1 + 1).factorial
            = padicValNat p (m0 + 1).factorial + padicValNat p (m0 + 1 + 1) :=
          padicValNat_factorial_succ p (m0 + 1) hp
        omega
      -- N equality
      have ha_corr' : ((a : ℕ) : ZMod (p ^ t))
          = ratResidue (p ^ t) g := ha_corr
      have hN_eq : (((m0 + 1 : ℕ) : ZMod (p ^ t)) * (a : ZMod (p ^ t))
          + ((a : ℕ) : ZMod (p ^ t)) ^ k)
          = ratResidue (p ^ t) S := by
        rw [ha_corr']
        have hmul := (ratResidue_mul p t hp (((m0 + 1 : ℕ)) : ℚ) g hm_nonneg_Q hg_nonneg).symm
        have hpow := (ratResidue_pow p t hp g hg_nonneg k).symm
        have hadd := (ratResidue_add p t hp ((((m0 + 1 : ℕ)) : ℚ) * g) (g ^ k)
          hmg_nonneg hgk_nonneg).symm
        rw [ratResidue_natCast] at hmul
        have hS_rw : S = ((((m0 + 1 : ℕ)) : ℚ) * g + g ^ k) := rfl
        rw [hS_rw, ← hadd, ← hmul, ← hpow]
      -- N val equality
      have hN_val : ((((m0 + 1 : ℕ) : ZMod (p ^ t)) * (a : ZMod (p ^ t))
          + ((a : ℕ) : ZMod (p ^ t)) ^ k).val)
          = (ratResidue (p ^ t) S).val := by
        rw [hN_eq]
      -- valuation of G_next
      have hm0_succ_le : 1 ≤ m0 + 1 := by omega
      have hrec := gobelSequence_succ k 2 (m0 + 1) hm0_succ_le
      rw [mul_add, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k),
        mul_comm g (((m0 + 1 : ℕ)) : ℚ)] at hrec
      -- hrec : (↑(m0+1)+1) * G_next = S? need S form with ↑(m0+1)
      have hrecS : ((((m0 + 1 : ℕ)) : ℚ) + 1) * gobelSequence k 2 (m0 + 1 + 1) = S := by
        simpa [hS_def, hg_def] using hrec
      have hdenom_ne : ((((m0 + 1 : ℕ)) : ℚ) + 1) ≠ 0 := by positivity
      have hG_eq : gobelSequence k 2 (m0 + 1 + 1)
          = S / ((((m0 + 1 : ℕ)) : ℚ) + 1) := by
        field_simp
        linarith
      have hdenom_val : padicValRat p ((((m0 + 1 : ℕ)) : ℚ) + 1) = (v : ℤ) := by
        have h_eq : ((((m0 + 1 : ℕ)) : ℚ) + 1) = (((m0 + 1 + 1 : ℕ)) : ℚ) := by
          push_cast
          ring
        rw [h_eq, padicValRat.of_nat, hv_def, Nat.padicValNat_def]
      have hG_val : padicValRat p (gobelSequence k 2 (m0 + 1 + 1))
          = padicValRat p S - (v : ℤ) := by
        rw [hG_eq, padicValRat.div hS_ne hdenom_ne, hdenom_val]
      -- R unfolding iff
      have hR_iff0 : gobelResidue k p r (m0 + 1 + 1) = none ↔
          ((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val % p ^ v ≠ 0) := by
        simp only [gobelResidue, hRm]
        rw [← ht_def, ← hv_def]
        by_cases hcond : ((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val % p ^ v ≠ 0)
        · simp
        · simp
      -- rewrite N to ratResidue S val
      have hN_val' : ((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val)
          = (ratResidue (p ^ t) S).val := by
        exact hN_val
      rw [hN_val'] at hR_iff0
      -- now hR_iff0 : R=none ↔ (ratResidue S).val % ... ≠ 0
      have hmod_iff := residue_val_mod_eq_zero_iff p t v hp hvt S hS_pos hS_nonneg
      -- hmod_iff : ...val % ... = 0 ↔ (v:ℤ) ≤ v(S)
      have hR_iff1 : gobelResidue k p r (m0 + 1 + 1) = none ↔ ¬ (v : ℤ) ≤ padicValRat p S := by
        simpa [hmod_iff] using hR_iff0
      have hR_iff2 : gobelResidue k p r (m0 + 1 + 1) = none ↔
          padicValRat p S < (v : ℤ) := by
        rw [hR_iff1, not_le]
      have h_final : padicValRat p S < (v : ℤ) ↔
          padicValRat p (gobelSequence k 2 (m0 + 1 + 1)) < 0 := by
        rw [hG_val]
        constructor
        · intro h
          omega
        · intro h
          omega
      have h_iff_first : gobelResidue k p r (m0 + 1 + 1) = none ↔
          padicValRat p (gobelSequence k 2 (m0 + 1 + 1)) < 0 :=
        hR_iff2.trans h_final
      constructor
      · exact h_iff_first
      · intro a' ha'
        have hR_ne_none' : gobelResidue k p r (m0 + 1 + 1) ≠ none := by
          rw [ha']
          exact Option.some_ne_none a'
        have hnot_cond_rat : ¬ (ratResidue (p ^ t) S).val % p ^ v ≠ 0 :=
          mt hR_iff0.mpr hR_ne_none'
        have hN0_rat : (ratResidue (p ^ t) S).val % p ^ v = 0 :=
          not_ne_iff.mp hnot_cond_rat
        have hnot_cond : ¬ ((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val % p ^ v ≠ 0) := by
          rw [hN_val']
          exact hnot_cond_rat
        have hN0 : ((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val % p ^ v = 0) := by
          rw [hN_val']
          exact hN0_rat
        have ha'_eq : a' = (((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val / p ^ v *
            ((((m0 + 1 + 1) / p ^ v : ℕ) :
              ZMod (p ^ (r - padicValNat p (m0 + 1 + 1).factorial)))⁻¹).val)
            % p ^ (r - padicValNat p (m0 + 1 + 1).factorial)) := by
          have h_unfold : gobelResidue k p r (m0 + 1 + 1)
              = if ((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val % p ^ v ≠ 0)
                then none
                else some (((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val / p ^ v *
                  ((((m0 + 1 + 1) / p ^ v : ℕ) :
                    ZMod (p ^ (r - padicValNat p (m0 + 1 + 1).factorial)))⁻¹).val)
                  % p ^ (r - padicValNat p (m0 + 1 + 1).factorial)) := by
            simp only [gobelResidue, hRm]
            rw [← ht_def, ← hv_def]
          rw [h_unfold, ite_eq_right hnot_cond] at ha'
          exact (Option.some_inj.mp ha').symm
        -- Now prove (a' : ZMod m') = ratResidue m' G_next via ha'_eq
        have hSv : (v : ℤ) ≤ padicValRat p S := hmod_iff.mp hN0_rat
        -- t' = t - v
        have hfact_eq : padicValNat p (m0 + 1 + 1).factorial
            = padicValNat p (m0 + 1).factorial + padicValNat p (m0 + 1 + 1) :=
          padicValNat_factorial_succ p (m0 + 1) hp
        have ht'_eq : r - padicValNat p (m0 + 1 + 1).factorial = t - v := by
          rw [ht_def, hv_def, hfact_eq]
          omega
        -- A, B, and p^v ∣ A
        set A : ℕ := S.num.natAbs with hA_def
        have hA_ne : A ≠ 0 := by
          have hnum_ne : S.num ≠ 0 := ne_of_gt (Rat.num_pos.mpr hS_pos)
          rw [hA_def]
          exact Int.natAbs_ne_zero.mpr hnum_ne
        have hA_eq : ((A : ℕ) : ℤ) = S.num :=
          Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hS_pos))
        have hden_mult : multiplicity p S.den = 0 := by
          rcases Rat.num_or_den_zero_padicVal S hp with hnum0 | hden0
          · have hdef : padicValRat p S = padicValInt p S.num - multiplicity p S.den := by
              rfl
            rw [hnum0] at hdef
            omega
          · exact hden0
        have hval_eq_S : padicValRat p S = (padicValInt p S.num : ℤ) := by
          have hdef : padicValRat p S = padicValInt p S.num - multiplicity p S.den := by
            rfl
          rw [hden_mult] at hdef
          simpa using hdef
        have hval_int_A : padicValInt p S.num = multiplicity p A := by
          rw [hA_def]
          rfl
        have hv_le_mult : v ≤ multiplicity p A := by
          have h1 : (v : ℤ) ≤ (multiplicity p A : ℤ) := by
            rw [← hval_int_A, ← hval_eq_S]
            exact hSv
          exact Nat.cast_le.mp h1
        have hpow_dvd_A : p ^ v ∣ A :=
          (Nat.pow_dvd_iff_le_multiplicity hp.ne_one hA_ne).mpr hv_le_mult
        set A' : ℕ := A / p ^ v with hA'_def
        have hA_eq' : p ^ v * A' = A := Nat.mul_div_cancel' hpow_dvd_A
        set u : ℕ := (m0 + 1 + 1) / p ^ v with hu_def
        have hpow_dvd_next : p ^ v ∣ (m0 + 1 + 1) := by
          have h1 : p ^ (multiplicity p (m0 + 1 + 1)) ∣ (m0 + 1 + 1) :=
            pow_multiplicity_dvd p _
          rw [← Nat.padicValNat_def, ← hv_def] at h1
          exact h1
        have hpu_eq : p ^ v * u = (m0 + 1 + 1) := Nat.mul_div_cancel' hpow_dvd_next
        have hu_pos : 0 < u := by
          have hle : p ^ v ≤ (m0 + 1 + 1) :=
            Nat.le_of_dvd (by omega) hpow_dvd_next
          have hpos : 0 < p ^ v := pow_pos hp.pos v
          exact Nat.div_pos hle hpos
        have hu_ne : u ≠ 0 := ne_of_gt hu_pos
        have hu_not_dvd : ¬ p ∣ u := pprime_part_not_dvd p (m0 + 1) hp
        -- ratResidue S in terms of A, B
        have hres_eq : ratResidue (p ^ t) S
            = (A : ZMod (p ^ t)) * ((S.den : ℕ) : ZMod (p ^ t))⁻¹ := by
          unfold ratResidue
          have hcast : (S.num : ZMod (p ^ t)) = (A : ZMod (p ^ t)) := by
            conv_lhs => rw [← hA_eq]
            rw [Int.cast_natCast]
          rw [hcast]
        -- C is inverse val mod m
        have hm_ne : p ^ t ≠ 0 := pow_ne_zero _ hp.ne_zero
        have : NeZero (p ^ t) := ⟨hm_ne⟩
        have hB_unit : IsUnit ((S.den : ℕ) : ZMod (p ^ t)) :=
          isUnit_den p S.den t hp (den_not_dvd_of_nonneg p hp S hS_nonneg)
        set C : ℕ := (((S.den : ℕ) : ZMod (p ^ t))⁻¹).val with hC_def
        have hB_inv_eq : ((S.den : ℕ) : ZMod (p ^ t))⁻¹ = (C : ZMod (p ^ t)) :=
          (ZMod.natCast_zmod_val _).symm
        have hN_val_AC : (ratResidue (p ^ t) S).val = (A * C) % p ^ t := by
          rw [hres_eq, hB_inv_eq, ← Nat.cast_mul, ZMod.val_natCast]
        -- N = p^v * ((A'*C) % m')
        have hA_mul : A * C = p ^ v * (A' * C) := by
          rw [← hA_eq']
          ring
        have hpow_eq : p ^ t = p ^ v * p ^ (t - v) := by
          rw [← pow_add, Nat.add_sub_cancel' hvt]
        have hN_eq_mul : (ratResidue (p ^ t) S).val = p ^ v * ((A' * C) % p ^ (t - v)) := by
          rw [hN_val_AC, hA_mul, hpow_eq, Nat.mul_mod_mul_left]
        -- N (explicit) equals same, via hN_val'
        have hN_explicit : ((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val)
            = p ^ v * ((A' * C) % p ^ (t - v)) := by
          rw [hN_val']
          exact hN_eq_mul
        have hN_div : ((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val / p ^ v)
            = (A' * C) % p ^ (t - v) :=
          Nat.div_eq_of_eq_mul_right (pow_pos hp.pos v) hN_explicit
        -- (C mod m') = (B mod m')⁻¹
        have hBC1_m : ((S.den : ℕ) : ZMod (p ^ t)) * (C : ZMod (p ^ t)) = 1 := by
          rw [← hB_inv_eq]
          exact ZMod.mul_inv_of_unit _ hB_unit
        have hBC_mod : (S.den * C) % p ^ t = 1 % p ^ t := by
          have h1 : (((S.den * C : ℕ)) : ZMod (p ^ t)) = ((1 : ℕ) : ZMod (p ^ t)) := by
            rw [Nat.cast_mul]
            simpa [Nat.cast_one] using hBC1_m
          exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
        have hm_dvd : p ^ (t - v) ∣ p ^ t := pow_dvd_pow p (Nat.sub_le t v)
        have hBC_mod' : (S.den * C) % p ^ (t - v) = 1 % p ^ (t - v) := by
          have h1a : (S.den * C) % p ^ t % p ^ (t - v) = (1 % p ^ t) % p ^ (t - v) := by
            rw [hBC_mod]
          rw [Nat.mod_mod_of_dvd _ hm_dvd, Nat.mod_mod_of_dvd _ hm_dvd] at h1a
          exact h1a
        have hBC1_m' : ((S.den : ℕ) : ZMod (p ^ (t - v))) * (C : ZMod (p ^ (t - v))) = 1 := by
          have h1 : (((S.den * C : ℕ)) : ZMod (p ^ (t - v))) = ((1 : ℕ) : ZMod (p ^ (t - v))) :=
            (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hBC_mod'
          rw [Nat.cast_mul] at h1
          simpa [Nat.cast_one] using h1
        have hC_eq_inv : (C : ZMod (p ^ (t - v)))
            = (((S.den : ℕ) : ZMod (p ^ (t - v))))⁻¹ := by
          apply Eq.symm
          exact ZMod.inv_eq_of_mul_eq_one _ _ _ hBC1_m'
        -- (N/p^v : ZMod m') = A' * B⁻¹
        have hm'_ne : p ^ (t - v) ≠ 0 := pow_ne_zero _ hp.ne_zero
        have : NeZero (p ^ (t - v)) := ⟨hm'_ne⟩
        have hNdiv_eq : ((((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val / p ^ v : ℕ))
            : ZMod (p ^ (t - v)))
            = (A' : ZMod (p ^ (t - v))) * (((S.den : ℕ) : ZMod (p ^ (t - v))))⁻¹ := by
          rw [hN_div]
          have h1 : ((((A' * C) % p ^ (t - v) : ℕ)) : ZMod (p ^ (t - v)))
              = ((A' * C : ℕ) : ZMod (p ^ (t - v))) :=
            ZMod.natCast_mod _ _
          rw [h1, Nat.cast_mul, hC_eq_inv]
        -- convert a' modulus to t-v form
        rw [ht'_eq] at ha'_eq ⊢
        set N : ℕ := ((↑(m0 + 1) * ↑a + (↑a) ^ k : ZMod (p ^ t)).val) with hN_def
        have hu_unit' : IsUnit ((u : ℕ) : ZMod (p ^ (t - v))) :=
          isUnit_den p u (t - v) hp hu_not_dvd
        have hC'_eq : (((((u : ℕ) : ZMod (p ^ (t - v)))⁻¹).val : ℕ) : ZMod (p ^ (t - v)))
            = (((u : ℕ) : ZMod (p ^ (t - v))))⁻¹ :=
          ZMod.natCast_zmod_val _
        have ha'_cast : ((a' : ℕ) : ZMod (p ^ (t - v)))
            = (((N / p ^ v : ℕ)) : ZMod (p ^ (t - v)))
              * ((((u : ℕ) : ZMod (p ^ (t - v))))⁻¹) := by
          rw [ha'_eq, ZMod.natCast_mod, Nat.cast_mul, hC'_eq]
        have hNdiv_eq' : (((N / p ^ v : ℕ)) : ZMod (p ^ (t - v)))
            = (A' : ZMod (p ^ (t - v))) * (((S.den : ℕ) : ZMod (p ^ (t - v))))⁻¹ := by
          exact hNdiv_eq
        rw [ha'_cast, hNdiv_eq']
        set B : ℕ := S.den with hB_def
        have hB_ne_Q : ((B : ℕ) : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (by rw [hB_def]; exact Rat.den_nz S)
        have hpv_ne_Q : ((p ^ v : ℕ) : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (pow_ne_zero v hp.ne_zero)
        have hu_ne_Q : ((u : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu_ne
        have hA'_eq_Q : ((A : ℕ) : ℚ) = ((p ^ v : ℕ) : ℚ) * ((A' : ℕ) : ℚ) := by
          rw [← Nat.cast_mul, ← hA_eq']
        have hS_eq : S = ((A : ℕ) : ℚ) / ((B : ℕ) : ℚ) := by
          have hnum : S = (S.num : ℚ) / ((B : ℕ) : ℚ) := by
            rw [hB_def]
            exact (Rat.num_div_den S).symm
          rw [← hA_eq] at hnum
          simpa [Int.cast_natCast] using hnum
        have hm_next_eq : ((m0 + 1 + 1 : ℕ) : ℚ) = ((p ^ v : ℕ) : ℚ) * ((u : ℕ) : ℚ) := by
          rw [← Nat.cast_mul, ← hpu_eq]
        have hdenom_eq : ((((m0 + 1 : ℕ)) : ℚ) + 1) = (((m0 + 1 + 1 : ℕ)) : ℚ) := by
          push_cast
          ring
        have hBu_ne_Q : (((B * u : ℕ)) : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by rw [hB_def]; exact Rat.den_nz S) hu_ne)
        have hBpu_ne_Q : ((B : ℕ) : ℚ) * (((p ^ v : ℕ) : ℚ) * ((u : ℕ) : ℚ)) ≠ 0 :=
          mul_ne_zero hB_ne_Q (mul_ne_zero hpv_ne_Q hu_ne_Q)
        have hBu'_ne_Q : ((B : ℕ) : ℚ) * ((u : ℕ) : ℚ) ≠ 0 :=
          mul_ne_zero hB_ne_Q hu_ne_Q
        have hG_next_eq : gobelSequence k 2 (m0 + 1 + 1)
            = ((A' : ℕ) : ℚ) / (((B * u : ℕ)) : ℚ) := by
          rw [hG_eq, hdenom_eq, hm_next_eq, hS_eq, hA'_eq_Q, Nat.cast_mul, div_div,
            div_eq_div_iff hBpu_ne_Q hBu'_ne_Q]
          ring
        -- 0 ≤ v(G_next) from R=some
        have hG_next_ne_none : gobelResidue k p r (m0 + 1 + 1) ≠ none := hR_ne_none'
        have hG_next_not_neg : ¬ padicValRat p (gobelSequence k 2 (m0 + 1 + 1)) < 0 :=
          mt h_iff_first.mpr hG_next_ne_none
        have hG_next_nonneg : 0 ≤ padicValRat p (gobelSequence k 2 (m0 + 1 + 1)) :=
          le_of_not_gt hG_next_not_neg
        -- G_next = divInt form for ratResidue_mk
        have hG_divInt : gobelSequence k 2 (m0 + 1 + 1)
            = Rat.divInt ((A' : ℕ) : ℤ) (((B * u : ℕ)) : ℤ) := by
          rw [hG_next_eq]
          exact Rat.natCast_div_eq_divInt A' (B * u)
        have hd_ne' : (((B * u : ℕ)) : ℤ) ≠ 0 :=
          Int.natCast_ne_zero.mpr (Nat.mul_ne_zero (by rw [hB_def]; exact Rat.den_nz S) hu_ne)
        have hB_not_dvd' : ¬ p ∣ B := by
          rw [hB_def]
          exact den_not_dvd_of_nonneg p hp S hS_nonneg
        have hBu_not_dvd : ¬ p ∣ (B * u) := by
          rw [hp.dvd_mul]
          exact not_or.mpr ⟨hB_not_dvd', hu_not_dvd⟩
        have hBu_unit : IsUnit (((B * u : ℕ)) : ZMod (p ^ (t - v))) :=
          isUnit_den p (B * u) (t - v) hp hBu_not_dvd
        have hdU' : IsUnit (((((B * u : ℕ)) : ℤ)) : ZMod (p ^ (t - v))) := by
          rw [Int.cast_natCast]
          exact hBu_unit
        have hdenU' : IsUnit ((((gobelSequence k 2 (m0 + 1 + 1)).den : ℕ)) : ZMod (p ^ (t - v))) :=
          isUnit_den p _ _ hp
            (den_not_dvd_of_nonneg p hp _ hG_next_nonneg)
        have hmk' := ratResidue_mk (p ^ (t - v)) (gobelSequence k 2 (m0 + 1 + 1))
          ((A' : ℕ) : ℤ) (((B * u : ℕ)) : ℤ) hd_ne' hG_divInt hdU' hdenU'
        -- hmk' : ratResidue = (A':ZMod)*(d:ZMod)⁻¹ with Int casts; convert to Nat casts
        rw [Int.cast_natCast, Int.cast_natCast] at hmk'
        -- hmk' : ratResidue = ↑A' * (↑(B*u))⁻¹
        have hB_unit' : IsUnit ((B : ℕ) : ZMod (p ^ (t - v))) :=
          isUnit_den p B (t - v) hp (by rw [hB_def] at hB_not_dvd' ⊢; exact hB_not_dvd')
        have hBu_inv : ((((B * u : ℕ)) : ZMod (p ^ (t - v))))⁻¹
            = (((B : ℕ) : ZMod (p ^ (t - v))))⁻¹ * ((((u : ℕ) : ZMod (p ^ (t - v))))⁻¹) := by
          have h_eq : (((B * u : ℕ)) : ZMod (p ^ (t - v)))
              = ((B : ℕ) : ZMod (p ^ (t - v))) * ((u : ℕ) : ZMod (p ^ (t - v))) := by
            push_cast
            ring
          rw [h_eq]
          exact zmod_mul_inv_of_unit _ _ _ hB_unit' hu_unit'
        rw [hmk', hBu_inv, mul_assoc]

/-- **Failure of the residue sequence detects non-integrality.** Let $k \ge 2$ and $r \ge 1$ be
integers, let $p$ be a prime, write $\nu_p$ for the $p$-adic valuation, and let $n \ge 1$ be an
integer with $\nu_p(n!) \le r$. Then the residue sequence $g_{k,p,r}$ takes the failure value $F$
at $n$, that is $g_{k,p,r}(n) = F$, if and only if the value $g_{k,2}(n)$ of the $(k, 2)$-Göbel
sequence has negative $p$-adic valuation, that is $g_{k,2}(n) \notin \mathbb{Z}_{(p)}$.

This is Lemma 10 of Matsuhira, Matsusaka, and Tsuchida.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Lemma 2 (`integers-2026-A23-lem-2`). -/
public theorem gobelResidue_eq_none_iff (k p r n : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r)
    (hp : p.Prime) (hn : 1 ≤ n) (hnr : padicValNat p n.factorial ≤ r) :
    gobelResidue k p r n = none ↔ padicValRat p (gobelSequence k 2 n) < 0
    := by
  exact (gobelResidue_eq_none_iff_aux k p r hk hr hp n hn hnr).1

end

end MetaMathlibExt
