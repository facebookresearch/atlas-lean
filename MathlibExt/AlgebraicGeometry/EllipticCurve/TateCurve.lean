/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_TateFormal.lean`
and
`Definitions/Def_ModularCurve_TateOrigin.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open PowerSeries HahnSeries

namespace TateCurve

/-- The integer `(5d ^ 3 + 7d ^ 5) / 12`, integral for every natural `d`. -/
def tateB (d : ℕ) : ℤ := (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12

theorem twelve_mul_tateB (d : ℕ) :
    12 * tateB d = 5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5 := by
  have key : ∀ c : ℤ, (12 : ℤ) ∣ 5 * c ^ 3 + 7 * c ^ 5 := by
    intro c
    have hr : c % 12 ≡ c [ZMOD 12] := Int.mod_modEq c 12
    have hcong : 5 * (c % 12) ^ 3 + 7 * (c % 12) ^ 5 ≡
        5 * c ^ 3 + 7 * c ^ 5 [ZMOD 12] :=
      ((hr.pow 3).mul_left 5).add ((hr.pow 5).mul_left 7)
    have h12 : c % 12 = 0 ∨ c % 12 = 1 ∨ c % 12 = 2 ∨ c % 12 = 3 ∨
        c % 12 = 4 ∨ c % 12 = 5 ∨ c % 12 = 6 ∨ c % 12 = 7 ∨ c % 12 = 8 ∨
        c % 12 = 9 ∨ c % 12 = 10 ∨ c % 12 = 11 := by
      omega
    have hres : 5 * (c % 12) ^ 3 + 7 * (c % 12) ^ 5 ≡ 0 [ZMOD 12] := by
      rcases h12 with h | h | h | h | h | h | h | h | h | h | h | h <;>
        rw [h] <;> decide
    exact Int.modEq_zero_iff_dvd.mp (hcong.symm.trans hres)
  rw [tateB]
  exact Int.mul_ediv_cancel' (key _)

/-- The Tate coefficient series `a₄(q) = -∑_{n≥1} (∑_{d ∣ n} 5d³) qⁿ`. -/
def tateA4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3)

/-- The Tate coefficient series `a₆(q) = -∑_{n≥1} (∑_{d ∣ n} tateB d) qⁿ`. -/
def tateA6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, tateB d

/-- The weight-six Eisenstein series `1 - 504 ∑_{n≥1} (∑_{d ∣ n} d⁵) qⁿ`. -/
def eisenstein6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

theorem coeff_tateA4 (n : ℕ) :
    PowerSeries.coeff n tateA4 = -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3) :=
  PowerSeries.coeff_mk n _

theorem coeff_tateA6 (n : ℕ) :
    PowerSeries.coeff n tateA6 = -∑ d ∈ n.divisors, tateB d :=
  PowerSeries.coeff_mk n _

theorem coeff_zero_tateA4 : PowerSeries.coeff 0 tateA4 = 0 := by
  rw [coeff_tateA4, Nat.divisors_zero, Finset.sum_empty, neg_zero]

theorem coeff_zero_tateA6 : PowerSeries.coeff 0 tateA6 = 0 := by
  rw [coeff_tateA6, Nat.divisors_zero, Finset.sum_empty, neg_zero]

theorem constantCoeff_tateA4 : PowerSeries.constantCoeff tateA4 = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_tateA4

theorem constantCoeff_tateA6 : PowerSeries.constantCoeff tateA6 = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_tateA6

theorem constantCoeff_eisenstein6 : PowerSeries.constantCoeff eisenstein6 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [eisenstein6]

theorem coeff_one_tateA4 : PowerSeries.coeff 1 tateA4 = -5 := by
  rw [coeff_tateA4, Nat.divisors_one, Finset.sum_singleton]
  norm_num

theorem coeff_one_tateA6 : PowerSeries.coeff 1 tateA6 = -1 := by
  have h : tateB 1 = 1 := by norm_num [tateB]
  rw [coeff_tateA6, Nat.divisors_one, Finset.sum_singleton, h]

/-- The Tate curve `y² + xy = x³ + a₄(q)x + a₆(q)` over `ℤ⟦q⟧`. -/
noncomputable def tatePowerSeries : WeierstrassCurve (PowerSeries ℤ) := ⟨1, 0, 0, tateA4, tateA6⟩

@[simp] theorem tatePowerSeries_a₁ : tatePowerSeries.a₁ = 1 := rfl
@[simp] theorem tatePowerSeries_a₂ : tatePowerSeries.a₂ = 0 := rfl
@[simp] theorem tatePowerSeries_a₃ : tatePowerSeries.a₃ = 0 := rfl
@[simp] theorem tatePowerSeries_a₄ : tatePowerSeries.a₄ = tateA4 := rfl
@[simp] theorem tatePowerSeries_a₆ : tatePowerSeries.a₆ = tateA6 := rfl

/-- The embedding of integer power series into Laurent series over `K`. -/
noncomputable def laurentOfInt (K : Type*) [CommRing K] : PowerSeries ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (Int.castRingHom K))

theorem laurentOfInt_apply (K : Type*) [CommRing K] (f : PowerSeries ℤ) :
    laurentOfInt K f = HahnSeries.ofPowerSeries ℤ K (f.map (Int.castRingHom K)) :=
  rfl

/-- The Tate curve over the Laurent series ring in `K`. -/
noncomputable def tateLaurent (K : Type*) [CommRing K] : WeierstrassCurve (LaurentSeries K) :=
  tatePowerSeries.map (laurentOfInt K)

@[simp] theorem tateLaurent_a₄ (K : Type*) [CommRing K] :
    (tateLaurent K).a₄ = laurentOfInt K tateA4 := rfl

@[simp] theorem tateLaurent_a₆ (K : Type*) [CommRing K] :
    (tateLaurent K).a₆ = laurentOfInt K tateA6 := rfl

instance instIsElliptic_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).IsElliptic := by
  constructor
  have hΔeq : tatePowerSeries.Δ =
      -tateA6 + tateA4 ^ 2 - PowerSeries.C 64 * tateA4 ^ 3 -
        PowerSeries.C 432 * tateA6 ^ 2 + PowerSeries.C 72 * (tateA4 * tateA6) := by
    rw [show (PowerSeries.C (64 : ℤ)) = (64 : PowerSeries ℤ) from map_ofNat _ 64,
      show (PowerSeries.C (432 : ℤ)) = (432 : PowerSeries ℤ) from map_ofNat _ 432,
      show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72]
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, tatePowerSeries_a₁, tatePowerSeries_a₂,
      tatePowerSeries_a₃, tatePowerSeries_a₄, tatePowerSeries_a₆]
    ring
  have hc0 : PowerSeries.constantCoeff tatePowerSeries.Δ = 0 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, PowerSeries.constantCoeff_C,
      constantCoeff_tateA4, constantCoeff_tateA6]
    ring
  have hmul1 : ∀ f g : PowerSeries ℤ, PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
    intro f g
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h420 : PowerSeries.coeff 0 (tateA4 ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_tateA4]
    norm_num
  have hsq4 : PowerSeries.coeff 1 (tateA4 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA4]
    norm_num
  have hsq6 : PowerSeries.coeff 1 (tateA6 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA6]
    norm_num
  have hcb4 : PowerSeries.coeff 1 (tateA4 ^ 3) = 0 := by
    rw [show tateA4 ^ 3 = tateA4 ^ 2 * tateA4 from pow_succ tateA4 2, hmul1, h420, hsq4,
      coeff_zero_tateA4]
    norm_num
  have hprod : PowerSeries.coeff 1 (tateA4 * tateA6) = 0 := by
    rw [hmul1, coeff_zero_tateA4, coeff_zero_tateA6]
    norm_num
  have hc1 : PowerSeries.coeff 1 tatePowerSeries.Δ = 1 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, hsq4, hsq6, hcb4, hprod,
      coeff_one_tateA6]
    norm_num
  obtain ⟨u, hXu⟩ : (PowerSeries.X : PowerSeries ℤ) ∣ tatePowerSeries.Δ :=
    PowerSeries.X_dvd_iff.mpr hc0
  have h1u : PowerSeries.coeff 1 tatePowerSeries.Δ = PowerSeries.constantCoeff u := by
    rw [hXu, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul]
  have hu : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← h1u, hc1]
    exact isUnit_one
  have hΔL : (tateLaurent K).Δ = laurentOfInt K tatePowerSeries.Δ := by
    rw [tateLaurent, WeierstrassCurve.map_Δ]
  rw [hΔL, hXu, map_mul]
  refine IsUnit.mul ?_ (hu.map (laurentOfInt K))
  have hX : laurentOfInt K PowerSeries.X = HahnSeries.single (1 : ℤ) 1 := by
    rw [laurentOfInt_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  rw [hX]
  exact ⟨⟨HahnSeries.single (1 : ℤ) 1, HahnSeries.single (-1 : ℤ) 1,
    by simp [HahnSeries.single_mul_single],
    by simp [HahnSeries.single_mul_single]⟩, rfl⟩

private theorem coeff_ofPowerSeries_of_neg {K : Type*} [CommRing K]
    (x : PowerSeries (PowerSeries K)) {n : ℤ} (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ (PowerSeries K) x).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨a, ha⟩
  simp only [Nat.castOrderEmbedding_apply] at ha
  have : (0 : ℤ) ≤ n := ha.2 ▸ Nat.cast_nonneg a
  omega

/-- The `X`-coordinate series of the Tate curve at the origin. -/
noncomputable def tateOriginX (K : Type*) [CommRing K] : LaurentSeries (PowerSeries K) :=
  HahnSeries.single (-2 : ℤ) (1 : PowerSeries K) +
    HahnSeries.single (-1 : ℤ) (1 : PowerSeries K) +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk fun k =>
      PowerSeries.mk fun M =>
        if M = 0 then 0 else
          (∑ e ∈ M.divisors, (e : K) * ((e.choose k : K) +
            (-1) ^ k * ((e + k - 1).choose k : K))) -
            (if k = 0 then 2 * ∑ e ∈ M.divisors, (e : K) else 0))

/-- The `Y`-coordinate series of the Tate curve at the origin. -/
noncomputable def tateOriginY (K : Type*) [CommRing K] : LaurentSeries (PowerSeries K) :=
  HahnSeries.single (-3 : ℤ) (-1 : PowerSeries K) +
    HahnSeries.single (-2 : ℤ) (-2 : PowerSeries K) +
    HahnSeries.single (-1 : ℤ) (-1 : PowerSeries K) +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk fun k =>
      PowerSeries.mk fun M =>
        if M = 0 then 0 else
          (∑ e ∈ M.divisors, ((e.choose 2 : K) * (e.choose k : K) -
            ((e + 1).choose 2 : K) * ((-1) ^ k * ((e + k - 1).choose k : K)))) +
            (if k = 0 then ∑ e ∈ M.divisors, (e : K) else 0))

theorem coeff_tateOriginX_neg_two (K : Type*) [CommRing K] :
    (tateOriginX K).coeff (-2) = 1 := by
  rw [tateOriginX, HahnSeries.coeff_add, HahnSeries.coeff_add,
    coeff_ofPowerSeries_of_neg _ (by norm_num), HahnSeries.coeff_single,
    HahnSeries.coeff_single, if_pos rfl, if_neg (by norm_num), add_zero, add_zero]

theorem coeff_tateOriginX_of_lt (K : Type*) [CommRing K] {n : ℤ} (hn : n < -2) :
    (tateOriginX K).coeff n = 0 := by
  have h1 : n ≠ -2 := by omega
  have h2 : n ≠ -1 := by omega
  rw [tateOriginX, HahnSeries.coeff_add, HahnSeries.coeff_add,
    coeff_ofPowerSeries_of_neg _ (by omega), HahnSeries.coeff_single,
    HahnSeries.coeff_single, if_neg h1, if_neg h2, add_zero, add_zero]

theorem coeff_tateOriginY_neg_three (K : Type*) [CommRing K] :
    (tateOriginY K).coeff (-3) = -1 := by
  rw [tateOriginY, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add,
    coeff_ofPowerSeries_of_neg _ (by norm_num), HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_pos rfl,
    if_neg (by norm_num), if_neg (by norm_num), add_zero, add_zero, add_zero]

theorem coeff_tateOriginY_of_lt (K : Type*) [CommRing K] {n : ℤ} (hn : n < -3) :
    (tateOriginY K).coeff n = 0 := by
  have h1 : n ≠ -3 := by omega
  have h2 : n ≠ -2 := by omega
  have h3 : n ≠ -1 := by omega
  rw [tateOriginY, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add,
    coeff_ofPowerSeries_of_neg _ (by omega), HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_neg h1, if_neg h2, if_neg h3,
    add_zero, add_zero, add_zero]

end TateCurve
