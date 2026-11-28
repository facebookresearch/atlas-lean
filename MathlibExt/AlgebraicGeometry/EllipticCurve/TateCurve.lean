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

/-!
# Tate curve: power series and origin coordinates

This file sets up the formal series behind the Tate curve `y² + xy = x³ + a₄(q)x + a₆(q)`.

* `TateCurve.tatePowerSeries` is the integral Weierstrass model over `ℤ⟦q⟧`, with coefficients
  `TateCurve.tateA4` and `TateCurve.tateA6`. It is not an elliptic curve over `ℤ⟦q⟧`: the
  constant coefficient of its discriminant is `0`.
* `TateCurve.tateLaurent K` is its base change along `TateCurve.laurentOfInt K` to the Laurent
  series ring `K((q))`, where `q` is invertible. There the discriminant is a unit, so this curve
  is elliptic for every commutative ring `K`.
* `TateCurve.tateOriginX K` and `TateCurve.tateOriginY K` expand Tate's coordinates `X(u, q)` and
  `Y(u, q)` at the origin `u = 1` in the local parameter `T = u - 1`. They lie in `K⟦q⟧((T))`:
  the outer Laurent variable is the local parameter `T`, and the inner power-series variable is
  `q`, the variable of the coefficient series.

The file proves the coefficient formulas, the ellipticity of `tateLaurent K`, and pole bounds for
the origin coordinates: `tateOriginX K` has no term below `T⁻²` and `T⁻²`-coefficient `1`, and
`tateOriginY K` has no term below `T⁻³` and `T⁻³`-coefficient `-1`. It does not prove that
`(tateOriginX K, tateOriginY K)` satisfies the Weierstrass equation of the Tate curve.
-/

@[expose] public section

open PowerSeries HahnSeries

namespace TateCurve

/-- **Divisor terms of the Tate coefficient $a_6$.** For a natural number `d`, the integer quotient
`(5d³ + 7d⁵) / 12`. The division is exact for every `d`. These numbers are the divisor terms of
the Tate coefficient `tateA6`. -/
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

/-- **The Tate coefficient $a_4$.** The integer power series
`a₄(q) = -∑_{n ≥ 1} (∑_{d ∣ n} 5d³) qⁿ = -5 ∑_{n ≥ 1} σ₃(n) qⁿ` in `ℤ⟦q⟧`, where
`σ₃(n) = ∑_{d ∣ n} d³`. -/
def tateA4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3)

/-- **The Tate coefficient $a_6$.** The integer power series
`a₆(q) = -∑_{n ≥ 1} (∑_{d ∣ n} (5d³ + 7d⁵) / 12) qⁿ` in `ℤ⟦q⟧`, whose divisor terms are
`tateB d`. -/
def tateA6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, tateB d

/-- **The Eisenstein series $E_6$ as an integer power series.** The `q`-expansion of the
weight-six Eisenstein series, `E₆(q) = 1 - 504 ∑_{n ≥ 1} (∑_{d ∣ n} d⁵) qⁿ`, in `ℤ⟦q⟧`. -/
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

/-- **The integral Tate model.** The Weierstrass model `y² + xy = x³ + a₄(q)x + a₆(q)` over
`ℤ⟦q⟧`, with `a₁ = 1`, `a₂ = a₃ = 0`, `a₄ = tateA4` and `a₆ = tateA6`. It is an integral model, not
an elliptic curve over `ℤ⟦q⟧`: the constant coefficient of its discriminant is `0`, so the
discriminant is not a unit of `ℤ⟦q⟧`. For a commutative ring `K`, changing coefficients along
`ℤ → K` and then inverting `q` gives `tateLaurent K` over `K((q))`. -/
noncomputable def tatePowerSeries : WeierstrassCurve (PowerSeries ℤ) := ⟨1, 0, 0, tateA4, tateA6⟩

@[simp] theorem tatePowerSeries_a₁ : tatePowerSeries.a₁ = 1 := rfl
@[simp] theorem tatePowerSeries_a₂ : tatePowerSeries.a₂ = 0 := rfl
@[simp] theorem tatePowerSeries_a₃ : tatePowerSeries.a₃ = 0 := rfl
@[simp] theorem tatePowerSeries_a₄ : tatePowerSeries.a₄ = tateA4 := rfl
@[simp] theorem tatePowerSeries_a₆ : tatePowerSeries.a₆ = tateA6 := rfl

/-- **From integer power series to Laurent series over $K$.** The ring map `ℤ⟦q⟧ → K((q))` that
first changes coefficients along `Int.castRingHom K`, giving `ℤ⟦q⟧ → K⟦q⟧`, and then includes
power series into Laurent series; it sends `q` to `q`. It is not an embedding in general: for
`K = ZMod 5` the nonzero constant series `5` maps to `0`. It is injective exactly when
`Int.castRingHom K` is, that is, when `K` has characteristic zero. -/
noncomputable def laurentOfInt (K : Type*) [CommRing K] : PowerSeries ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (Int.castRingHom K))

theorem laurentOfInt_apply (K : Type*) [CommRing K] (f : PowerSeries ℤ) :
    laurentOfInt K f = HahnSeries.ofPowerSeries ℤ K (f.map (Int.castRingHom K)) :=
  rfl

/-- **The Tate curve over Laurent series.** The base change of `tatePowerSeries` along
`laurentOfInt K`: the Weierstrass curve `y² + xy = x³ + a₄(q)x + a₆(q)` over the Laurent series
ring `K((q))`. Its Laurent variable is the same `q`, now invertible; it is not the local parameter
`T` of `tateOriginX`. The discriminant of `tatePowerSeries` is `q` times a unit of `ℤ⟦q⟧`, so here
it is a unit, and the curve is elliptic for every commutative ring `K`. -/
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

/-- **The $X$-coordinate of the Tate curve at the origin.** Tate's coordinate
`X(u, q) = ∑_{n ∈ ℤ} qⁿu / (1 - qⁿu)² - 2 ∑_{n ≥ 1} n qⁿ / (1 - qⁿ)`, expanded at the origin
`u = 1` in the local parameter `T = u - 1`. It lies in `K⟦q⟧((T))`: the outer Laurent variable is
the local parameter `T`, and the inner power-series variable is `q`. Explicitly it is
`T⁻² + T⁻¹ + ∑_{k ≥ 0} c_k Tᵏ`, where `c_k ∈ K⟦q⟧` has constant term `0` and, for `M ≥ 1`,
`qᴹ`-coefficient `∑_{e ∣ M} e (e.choose k + (-1)ᵏ (e + k - 1).choose k)`, minus
`2σ₁(M) = 2 ∑_{e ∣ M} e` when `k = 0`. In particular it has no term below `T⁻²`, and its
`T⁻²`-coefficient is `1`. -/
noncomputable def tateOriginX (K : Type*) [CommRing K] : LaurentSeries (PowerSeries K) :=
  HahnSeries.single (-2 : ℤ) (1 : PowerSeries K) +
    HahnSeries.single (-1 : ℤ) (1 : PowerSeries K) +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk fun k =>
      PowerSeries.mk fun M =>
        if M = 0 then 0 else
          (∑ e ∈ M.divisors, (e : K) * ((e.choose k : K) +
            (-1) ^ k * ((e + k - 1).choose k : K))) -
            (if k = 0 then 2 * ∑ e ∈ M.divisors, (e : K) else 0))

/-- **The $Y$-coordinate of the Tate curve at the origin.** Tate's coordinate
`Y(u, q) = ∑_{n ∈ ℤ} (qⁿu)² / (1 - qⁿu)³ + ∑_{n ≥ 1} n qⁿ / (1 - qⁿ)`, expanded at the origin
`u = 1` in the local parameter `T = u - 1`, as an element of `K⟦q⟧((T))` with outer Laurent
variable `T` and inner power-series variable `q`. Explicitly it is
`-T⁻³ - 2T⁻² - T⁻¹ + ∑_{k ≥ 0} c_k Tᵏ`, where `c_k ∈ K⟦q⟧` has constant term `0` and, for
`M ≥ 1`, `qᴹ`-coefficient
`∑_{e ∣ M} (e.choose 2 · e.choose k - (e + 1).choose 2 · (-1)ᵏ (e + k - 1).choose k)`, plus
`σ₁(M) = ∑_{e ∣ M} e` when `k = 0`. In particular it has no term below `T⁻³`, and its
`T⁻³`-coefficient is `-1`. -/
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
  rw [tateOriginX, HahnSeries.coeff_add, HahnSeries.coeff_add, PowerSeries.coeff_coe,
    ite_eq_left (by norm_num), HahnSeries.coeff_single, HahnSeries.coeff_single,
    ite_eq_left rfl, ite_eq_right (by norm_num), add_zero, add_zero]

theorem coeff_tateOriginX_of_lt (K : Type*) [CommRing K] {n : ℤ} (hn : n < -2) :
    (tateOriginX K).coeff n = 0 := by
  have h1 : n ≠ -2 := by omega
  have h2 : n ≠ -1 := by omega
  rw [tateOriginX, HahnSeries.coeff_add, HahnSeries.coeff_add, PowerSeries.coeff_coe,
    ite_eq_left (by omega), HahnSeries.coeff_single, HahnSeries.coeff_single,
    ite_eq_right h1, ite_eq_right h2, add_zero, add_zero]

theorem coeff_tateOriginY_neg_three (K : Type*) [CommRing K] :
    (tateOriginY K).coeff (-3) = -1 := by
  rw [tateOriginY, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add,
    PowerSeries.coeff_coe, ite_eq_left (by norm_num), HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, ite_eq_left rfl,
    ite_eq_right (by norm_num), ite_eq_right (by norm_num), add_zero, add_zero, add_zero]

theorem coeff_tateOriginY_of_lt (K : Type*) [CommRing K] {n : ℤ} (hn : n < -3) :
    (tateOriginY K).coeff n = 0 := by
  have h1 : n ≠ -3 := by omega
  have h2 : n ≠ -2 := by omega
  have h3 : n ≠ -1 := by omega
  rw [tateOriginY, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add,
    PowerSeries.coeff_coe, ite_eq_left (by omega), HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, ite_eq_right h1, ite_eq_right h2,
    ite_eq_right h3, add_zero, add_zero, add_zero]

end TateCurve
