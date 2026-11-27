/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_FormalGroupLaw.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
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
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Basic

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Substitution

@[expose] public section

set_option autoImplicit false

noncomputable section

open PowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R]

theorem coeff_add_mul_of_X_pow_dvd {f g : R⟦X⟧} {a b : ℕ}
    (hf : (X : R⟦X⟧) ^ a ∣ f) (hg : (X : R⟦X⟧) ^ b ∣ g) :
    coeff (a + b) (f * g) = coeff a f * coeff b g := by
  obtain ⟨f', rfl⟩ := hf
  obtain ⟨g', rfl⟩ := hg
  have h : (X : R⟦X⟧) ^ a * f' * ((X : R⟦X⟧) ^ b * g') = (X : R⟦X⟧) ^ (a + b) * (f' * g') := by
    ring
  rw [h]
  simp [coeff_X_pow_mul', coeff_zero_eq_constantCoeff_apply]

theorem coeff_add_succ_mul_of_X_pow_dvd {f g : R⟦X⟧} {a b : ℕ}
    (hf : (X : R⟦X⟧) ^ a ∣ f) (hg : (X : R⟦X⟧) ^ b ∣ g) :
    coeff (a + b + 1) (f * g)
      = coeff (a + 1) f * coeff b g + coeff a f * coeff (b + 1) g := by
  obtain ⟨f', rfl⟩ := hf
  obtain ⟨g', rfl⟩ := hg
  have h : (X : R⟦X⟧) ^ a * f' * ((X : R⟦X⟧) ^ b * g') = (X : R⟦X⟧) ^ (a + b) * (f' * g') := by
    ring
  rw [h, coeff_X_pow_mul', ite_eq_left (by omega : a + b ≤ a + b + 1),
    (show a + b + 1 - (a + b) = 1 by omega), coeff_one_mul]
  have e1 : coeff (a + 1) ((X : R⟦X⟧) ^ a * f') = coeff 1 f' := by
    rw [coeff_X_pow_mul', ite_eq_left (by omega : a ≤ a + 1), (show a + 1 - a = 1 by omega)]
  have e2 : coeff b ((X : R⟦X⟧) ^ b * g') = constantCoeff g' := by
    rw [coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
  have e3 : coeff a ((X : R⟦X⟧) ^ a * f') = constantCoeff f' := by
    rw [coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
  have e4 : coeff (b + 1) ((X : R⟦X⟧) ^ b * g') = coeff 1 g' := by
    rw [coeff_X_pow_mul', ite_eq_left (by omega : b ≤ b + 1), (show b + 1 - b = 1 by omega)]
  rw [e1, e2, e3, e4]
  ring

end PowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def wSubst (w : R⟦X⟧) : R⟦X⟧ :=
  X ^ 3 + C W.a₁ * (X * w) + C W.a₂ * (X ^ 2 * w) + C W.a₃ * w ^ 2
    + C W.a₄ * (X * w ^ 2) + C W.a₆ * w ^ 3

def wIter : ℕ → R⟦X⟧
  | 0 => 0
  | k + 1 => W.wSubst (wIter k)

@[simp]
theorem wIter_zero : W.wIter 0 = 0 := by simp [wIter]

theorem wIter_succ (k : ℕ) : W.wIter (k + 1) = W.wSubst (W.wIter k) := by simp [wIter]

theorem wSubst_sub_wSubst (w w' : R⟦X⟧) :
    W.wSubst w - W.wSubst w'
      = (w - w') * (C W.a₁ * X + C W.a₂ * X ^ 2 + C W.a₃ * (w + w')
          + C W.a₄ * (X * (w + w')) + C W.a₆ * (w ^ 2 + w * w' + w' ^ 2)) := by
  simp only [wSubst]
  ring

theorem X_dvd_wSubst {w : R⟦X⟧} (hw : (X : R⟦X⟧) ∣ w) : (X : R⟦X⟧) ∣ W.wSubst w := by
  rw [X_dvd_iff] at hw ⊢
  simp [wSubst, hw, constantCoeff_X, constantCoeff_C]

theorem X_pow_three_dvd_wSubst {w : R⟦X⟧} (hw : (X : R⟦X⟧) ^ 3 ∣ w) :
    (X : R⟦X⟧) ^ 3 ∣ W.wSubst w := by
  simp only [wSubst]
  refine dvd_add (dvd_add (dvd_add (dvd_add (dvd_add dvd_rfl ?_) ?_) ?_) ?_) ?_
  · exact (hw.mul_left X).mul_left _
  · exact (hw.mul_left ((X : R⟦X⟧) ^ 2)).mul_left _
  · exact (hw.trans (dvd_pow_self w (by norm_num))).mul_left _
  · exact ((hw.trans (dvd_pow_self w (by norm_num))).mul_left X).mul_left _
  · exact (hw.trans (dvd_pow_self w (by norm_num))).mul_left _

theorem X_pow_succ_dvd_wSubst_sub_wSubst {w w' : R⟦X⟧} {n : ℕ}
    (hw : (X : R⟦X⟧) ∣ w) (hw' : (X : R⟦X⟧) ∣ w')
    (h : (X : R⟦X⟧) ^ n ∣ w - w') :
    (X : R⟦X⟧) ^ (n + 1) ∣ W.wSubst w - W.wSubst w' := by
  rw [W.wSubst_sub_wSubst, pow_succ]
  refine mul_dvd_mul h ?_
  rw [X_dvd_iff] at hw hw' ⊢
  simp [hw, hw', constantCoeff_X, constantCoeff_C]

theorem X_dvd_wIter (k : ℕ) : (X : R⟦X⟧) ∣ W.wIter k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [W.wIter_succ k]
      exact W.X_dvd_wSubst ih

theorem X_pow_three_dvd_wIter (k : ℕ) : (X : R⟦X⟧) ^ 3 ∣ W.wIter k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [W.wIter_succ k]
      exact W.X_pow_three_dvd_wSubst ih

theorem X_pow_succ_dvd_wIter_succ_sub (k : ℕ) :
    (X : R⟦X⟧) ^ (k + 1) ∣ W.wIter (k + 1) - W.wIter k := by
  induction k with
  | zero =>
      rw [W.wIter_succ 0, W.wIter_zero, sub_zero]
      exact dvd_trans (pow_dvd_pow X (by norm_num)) (W.X_pow_three_dvd_wSubst (dvd_zero _))
  | succ k ih =>
      have h := W.X_pow_succ_dvd_wSubst_sub_wSubst (W.X_dvd_wIter (k + 1)) (W.X_dvd_wIter k) ih
      simpa only [wIter_succ] using h

theorem X_pow_succ_dvd_wIter_sub_wIter {k m : ℕ} (h : k ≤ m) :
    (X : R⟦X⟧) ^ (k + 1) ∣ W.wIter m - W.wIter k := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
      have h1 : W.wIter (m + 1) - W.wIter k
          = (W.wIter (m + 1) - W.wIter m) + (W.wIter m - W.wIter k) := by ring
      rw [h1]
      exact dvd_add
        (dvd_trans (pow_dvd_pow X (by omega)) (W.X_pow_succ_dvd_wIter_succ_sub m)) ih

/-- **Power series w(z) of a Weierstrass curve.** The unique power series `w(z)` with zero
constant coefficient satisfying
`w = z ^ 3 + a₁ z w + a₂ z ^ 2 w + a₃ w ^ 2 + a₄ z w ^ 2 + a₆ w ^ 3`, the Weierstrass equation
in the coordinates `z = -x / y` and `w = -1 / y`. -/
def formalW : R⟦X⟧ := PowerSeries.mk fun n => coeff n (W.wIter n)

theorem coeff_formalW (n : ℕ) : coeff n W.formalW = coeff n (W.wIter n) := coeff_mk _ _

theorem X_pow_succ_dvd_formalW_sub_wIter (k : ℕ) :
    (X : R⟦X⟧) ^ (k + 1) ∣ W.formalW - W.wIter k := by
  rw [X_pow_dvd_iff]
  intro m hm
  have hmk : m ≤ k := Nat.lt_succ_iff.mp hm
  have h := W.X_pow_succ_dvd_wIter_sub_wIter hmk
  rw [X_pow_dvd_iff] at h
  have h2 := h m (Nat.lt_succ_self m)
  rw [map_sub] at h2 ⊢
  rw [coeff_formalW, sub_eq_zero.mp h2, sub_self]

theorem constantCoeff_formalW : constantCoeff W.formalW = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_formalW, W.wIter_zero, map_zero]

theorem X_dvd_formalW : (X : R⟦X⟧) ∣ W.formalW :=
  X_dvd_iff.mpr W.constantCoeff_formalW

theorem X_pow_three_dvd_formalW : (X : R⟦X⟧) ^ 3 ∣ W.formalW := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [coeff_formalW]
  exact X_pow_dvd_iff.mp (W.X_pow_three_dvd_wIter m) m hm

theorem coeff_formalW_zero : coeff 0 W.formalW = 0 := by
  rw [coeff_zero_eq_constantCoeff_apply]
  exact W.constantCoeff_formalW

theorem coeff_formalW_one : coeff 1 W.formalW = 0 :=
  X_pow_dvd_iff.mp W.X_pow_three_dvd_formalW 1 (by norm_num)

theorem coeff_formalW_two : coeff 2 W.formalW = 0 :=
  X_pow_dvd_iff.mp W.X_pow_three_dvd_formalW 2 (by norm_num)

theorem X_pow_succ_dvd_formalW_sub_wSubst (k : ℕ) :
    (X : R⟦X⟧) ^ (k + 1) ∣ W.formalW - W.wSubst W.formalW := by
  have h1 : (X : R⟦X⟧) ^ (k + 1 + 1) ∣ W.formalW - W.wIter (k + 1) :=
    W.X_pow_succ_dvd_formalW_sub_wIter (k + 1)
  have h2 : (X : R⟦X⟧) ^ (k + 1) ∣ W.wIter k - W.formalW :=
    dvd_sub_comm.mp (W.X_pow_succ_dvd_formalW_sub_wIter k)
  have h3 : (X : R⟦X⟧) ^ (k + 1 + 1) ∣ W.wSubst (W.wIter k) - W.wSubst W.formalW :=
    W.X_pow_succ_dvd_wSubst_sub_wSubst (W.X_dvd_wIter k) W.X_dvd_formalW h2
  have h4 : W.formalW - W.wSubst W.formalW
      = (W.formalW - W.wIter (k + 1)) + (W.wSubst (W.wIter k) - W.wSubst W.formalW) := by
    rw [W.wIter_succ k]
    ring
  rw [h4]
  exact dvd_add (dvd_trans (pow_dvd_pow X (by omega)) h1)
    (dvd_trans (pow_dvd_pow X (by omega)) h3)

theorem formalW_eq_wSubst : W.formalW = W.wSubst W.formalW := by
  ext n
  have h := W.X_pow_succ_dvd_formalW_sub_wSubst n
  rw [X_pow_dvd_iff] at h
  have h2 := h n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at h2
  exact h2

theorem formalW_eq :
    W.formalW
      = X ^ 3 + C W.a₁ * X * W.formalW + C W.a₂ * X ^ 2 * W.formalW
        + C W.a₃ * W.formalW ^ 2 + C W.a₄ * X * W.formalW ^ 2 + C W.a₆ * W.formalW ^ 3 := by
  conv_lhs => rw [W.formalW_eq_wSubst]
  unfold wSubst
  ring

theorem eq_formalW_of_constantCoeff_eq_zero {w : R⟦X⟧} (hw : constantCoeff w = 0)
    (heq : w = X ^ 3 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2
      + C W.a₄ * X * w ^ 2 + C W.a₆ * w ^ 3) :
    w = W.formalW := by
  have hsub : w = W.wSubst w := by
    conv_lhs => rw [heq]
    unfold wSubst
    ring
  have hX : (X : R⟦X⟧) ∣ w := X_dvd_iff.mpr hw
  have key : ∀ k : ℕ, (X : R⟦X⟧) ^ k ∣ w - W.formalW := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h := W.X_pow_succ_dvd_wSubst_sub_wSubst hX W.X_dvd_formalW ih
        rwa [← hsub, ← W.formalW_eq_wSubst] at h
  ext n
  have h := key (n + 1)
  rw [X_pow_dvd_iff] at h
  have h2 := h n (Nat.lt_succ_self n)
  rwa [map_sub, sub_eq_zero] at h2

theorem existsUnique_formalW :
    ∃! w : R⟦X⟧, constantCoeff w = 0 ∧
      w = X ^ 3 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2
        + C W.a₄ * X * w ^ 2 + C W.a₆ * w ^ 3 :=
  ⟨W.formalW, ⟨W.constantCoeff_formalW, W.formalW_eq⟩,
    fun _ hw => W.eq_formalW_of_constantCoeff_eq_zero hw.1 hw.2⟩

def wUnitFactor : R⟦X⟧ :=
  1 - (C W.a₁ * X + C W.a₂ * X ^ 2 + C W.a₃ * W.formalW + C W.a₄ * (X * W.formalW)
    + C W.a₆ * W.formalW ^ 2)

theorem formalW_mul_wUnitFactor : W.formalW * W.wUnitFactor = X ^ 3 := by
  unfold wUnitFactor
  linear_combination W.formalW_eq

theorem constantCoeff_wUnitFactor : constantCoeff W.wUnitFactor = 1 := by
  unfold wUnitFactor
  simp [W.constantCoeff_formalW, constantCoeff_X, constantCoeff_C]

theorem isUnit_wUnitFactor : IsUnit W.wUnitFactor :=
  isUnit_iff_constantCoeff.mpr (by rw [W.constantCoeff_wUnitFactor]; exact isUnit_one)

private theorem X_pow_six_dvd_formalW_sq : (X : R⟦X⟧) ^ 6 ∣ W.formalW ^ 2 := by
  have h := pow_dvd_pow_of_dvd W.X_pow_three_dvd_formalW 2
  rw [← pow_mul] at h
  norm_num at h
  exact h

private theorem X_pow_nine_dvd_formalW_cube : (X : R⟦X⟧) ^ 9 ∣ W.formalW ^ 3 := by
  have h := pow_dvd_pow_of_dvd W.X_pow_three_dvd_formalW 3
  rw [← pow_mul] at h
  norm_num at h
  exact h

private theorem coeff_formalW_sq_of_lt {n : ℕ} (hn : n < 6) : coeff n (W.formalW ^ 2) = 0 :=
  X_pow_dvd_iff.mp W.X_pow_six_dvd_formalW_sq n hn

private theorem coeff_formalW_cube_of_lt {n : ℕ} (hn : n < 9) : coeff n (W.formalW ^ 3) = 0 :=
  X_pow_dvd_iff.mp W.X_pow_nine_dvd_formalW_cube n hn

private theorem coeff_X_mul_formalW' (n : ℕ) (φ : R⟦X⟧) :
    coeff n ((X : R⟦X⟧) * φ) = if 1 ≤ n then coeff (n - 1) φ else 0 := by
  rw [← pow_one (X : R⟦X⟧), coeff_X_pow_mul']

private theorem coeff_formalW_step (n : ℕ) :
    coeff n W.formalW
      = coeff n ((X : R⟦X⟧) ^ 3) + W.a₁ * coeff n ((X : R⟦X⟧) * W.formalW)
        + W.a₂ * coeff n ((X : R⟦X⟧) ^ 2 * W.formalW) + W.a₃ * coeff n (W.formalW ^ 2)
        + W.a₄ * coeff n ((X : R⟦X⟧) * W.formalW ^ 2) + W.a₆ * coeff n (W.formalW ^ 3) := by
  conv_lhs => rw [W.formalW_eq_wSubst]
  unfold wSubst
  simp only [map_add, coeff_C_mul]

theorem coeff_formalW_three : coeff 3 W.formalW = 1 := by
  have h := W.coeff_formalW_step 3
  have e0 : coeff 3 ((X : R⟦X⟧) ^ 3) = (1 : R) := by rw [coeff_X_pow]; norm_num
  have e1 : coeff 3 ((X : R⟦X⟧) * W.formalW) = 0 := by
    rw [coeff_X_mul_formalW']
    norm_num [W.coeff_formalW_two]
  have e2 : coeff 3 ((X : R⟦X⟧) ^ 2 * W.formalW) = 0 := by
    rw [coeff_X_pow_mul']
    norm_num [W.coeff_formalW_one]
  have e3 : coeff 3 (W.formalW ^ 2) = 0 := W.coeff_formalW_sq_of_lt (by norm_num)
  have e4 : coeff 3 ((X : R⟦X⟧) * W.formalW ^ 2) = 0 := by
    rw [coeff_X_mul_formalW']
    norm_num [W.coeff_formalW_sq_of_lt (show (2 : ℕ) < 6 by norm_num)]
  have e5 : coeff 3 (W.formalW ^ 3) = 0 := W.coeff_formalW_cube_of_lt (by norm_num)
  rw [h, e0, e1, e2, e3, e4, e5]
  ring

theorem coeff_formalW_four : coeff 4 W.formalW = W.a₁ := by
  have h := W.coeff_formalW_step 4
  have e0 : coeff 4 ((X : R⟦X⟧) ^ 3) = (0 : R) := by rw [coeff_X_pow]; norm_num
  have e1 : coeff 4 ((X : R⟦X⟧) * W.formalW) = 1 := by
    rw [coeff_X_mul_formalW']
    norm_num [W.coeff_formalW_three]
  have e2 : coeff 4 ((X : R⟦X⟧) ^ 2 * W.formalW) = 0 := by
    rw [coeff_X_pow_mul']
    norm_num [W.coeff_formalW_two]
  have e3 : coeff 4 (W.formalW ^ 2) = 0 := W.coeff_formalW_sq_of_lt (by norm_num)
  have e4 : coeff 4 ((X : R⟦X⟧) * W.formalW ^ 2) = 0 := by
    rw [coeff_X_mul_formalW']
    norm_num [W.coeff_formalW_sq_of_lt (show (3 : ℕ) < 6 by norm_num)]
  have e5 : coeff 4 (W.formalW ^ 3) = 0 := W.coeff_formalW_cube_of_lt (by norm_num)
  rw [h, e0, e1, e2, e3, e4, e5]
  ring

theorem coeff_formalW_five : coeff 5 W.formalW = W.a₁ ^ 2 + W.a₂ := by
  have h := W.coeff_formalW_step 5
  have e0 : coeff 5 ((X : R⟦X⟧) ^ 3) = (0 : R) := by rw [coeff_X_pow]; norm_num
  have e1 : coeff 5 ((X : R⟦X⟧) * W.formalW) = W.a₁ := by
    rw [coeff_X_mul_formalW']
    norm_num [W.coeff_formalW_four]
  have e2 : coeff 5 ((X : R⟦X⟧) ^ 2 * W.formalW) = 1 := by
    rw [coeff_X_pow_mul']
    norm_num [W.coeff_formalW_three]
  have e3 : coeff 5 (W.formalW ^ 2) = 0 := W.coeff_formalW_sq_of_lt (by norm_num)
  have e4 : coeff 5 ((X : R⟦X⟧) * W.formalW ^ 2) = 0 := by
    rw [coeff_X_mul_formalW']
    norm_num [W.coeff_formalW_sq_of_lt (show (4 : ℕ) < 6 by norm_num)]
  have e5 : coeff 5 (W.formalW ^ 3) = 0 := W.coeff_formalW_cube_of_lt (by norm_num)
  rw [h, e0, e1, e2, e3, e4, e5]
  ring

private theorem coeff_formalW_sq_six : coeff 6 (W.formalW ^ 2) = (1 : R) := by
  have h := PowerSeries.coeff_add_mul_of_X_pow_dvd W.X_pow_three_dvd_formalW
    W.X_pow_three_dvd_formalW
  norm_num [W.coeff_formalW_three] at h
  rw [pow_two, h]

theorem coeff_formalW_six : coeff 6 W.formalW = W.a₁ ^ 3 + 2 * W.a₁ * W.a₂ + W.a₃ := by
  have h := W.coeff_formalW_step 6
  have e0 : coeff 6 ((X : R⟦X⟧) ^ 3) = (0 : R) := by rw [coeff_X_pow]; norm_num
  have e1 : coeff 6 ((X : R⟦X⟧) * W.formalW) = W.a₁ ^ 2 + W.a₂ := by
    rw [coeff_X_mul_formalW']
    norm_num [W.coeff_formalW_five]
  have e2 : coeff 6 ((X : R⟦X⟧) ^ 2 * W.formalW) = W.a₁ := by
    rw [coeff_X_pow_mul']
    norm_num [W.coeff_formalW_four]
  have e3 : coeff 6 (W.formalW ^ 2) = 1 := W.coeff_formalW_sq_six
  have e4 : coeff 6 ((X : R⟦X⟧) * W.formalW ^ 2) = 0 := by
    rw [coeff_X_mul_formalW']
    norm_num [W.coeff_formalW_sq_of_lt (show (5 : ℕ) < 6 by norm_num)]
  have e5 : coeff 6 (W.formalW ^ 3) = 0 := W.coeff_formalW_cube_of_lt (by norm_num)
  rw [h, e0, e1, e2, e3, e4, e5]
  ring

private theorem coeff_formalW_sq_seven : coeff 7 (W.formalW ^ 2) = 2 * W.a₁ := by
  have h := PowerSeries.coeff_add_succ_mul_of_X_pow_dvd W.X_pow_three_dvd_formalW
    W.X_pow_three_dvd_formalW
  norm_num [W.coeff_formalW_three, W.coeff_formalW_four] at h
  rw [pow_two, h]
  ring

theorem coeff_formalW_seven :
    coeff 7 W.formalW
      = W.a₁ ^ 4 + 3 * W.a₁ ^ 2 * W.a₂ + 3 * W.a₁ * W.a₃ + W.a₂ ^ 2 + W.a₄ := by
  have h := W.coeff_formalW_step 7
  have e0 : coeff 7 ((X : R⟦X⟧) ^ 3) = (0 : R) := by rw [coeff_X_pow]; norm_num
  have e1 : coeff 7 ((X : R⟦X⟧) * W.formalW) = W.a₁ ^ 3 + 2 * W.a₁ * W.a₂ + W.a₃ := by
    rw [coeff_X_mul_formalW']
    norm_num [W.coeff_formalW_six]
  have e2 : coeff 7 ((X : R⟦X⟧) ^ 2 * W.formalW) = W.a₁ ^ 2 + W.a₂ := by
    rw [coeff_X_pow_mul']
    norm_num [W.coeff_formalW_five]
  have e3 : coeff 7 (W.formalW ^ 2) = 2 * W.a₁ := W.coeff_formalW_sq_seven
  have e4 : coeff 7 ((X : R⟦X⟧) * W.formalW ^ 2) = 1 := by
    rw [coeff_X_mul_formalW']
    norm_num [W.coeff_formalW_sq_six]
  have e5 : coeff 7 (W.formalW ^ 3) = 0 := W.coeff_formalW_cube_of_lt (by norm_num)
  rw [h, e0, e1, e2, e3, e4, e5]
  ring

theorem exists_eq_X_pow_three_mul :
    ∃ u : R⟦X⟧, constantCoeff u = 1 ∧ W.formalW = (X : R⟦X⟧) ^ 3 * u := by
  obtain ⟨u, hu⟩ := W.X_pow_three_dvd_formalW
  refine ⟨u, ?_, hu⟩
  have h3 : coeff 3 ((X : R⟦X⟧) ^ 3 * u) = constantCoeff u := by
    rw [coeff_X_pow_mul']
    simp
  rw [← h3, ← hu]
  exact W.coeff_formalW_three

theorem order_formalW [Nontrivial R] : (W.formalW).order = (3 : ℕ∞) := by
  rw [show (3 : ℕ∞) = ((3 : ℕ) : ℕ∞) by norm_num, PowerSeries.order_eq_nat]
  refine ⟨?_, fun i hi => X_pow_dvd_iff.mp W.X_pow_three_dvd_formalW i hi⟩
  rw [W.coeff_formalW_three]
  exact one_ne_zero

end WeierstrassCurve

end

noncomputable section

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

noncomputable def fgW₁ : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) W.formalW

noncomputable def fgSlope : MvPowerSeries (Fin 2) R :=
  fun d => PowerSeries.coeff (d 0 + d 1 + 1) W.formalW

noncomputable def fgNu : MvPowerSeries (Fin 2) R :=
  W.fgW₁ - W.fgSlope * MvPowerSeries.X (0 : Fin 2)

noncomputable def fgZ3Denom : MvPowerSeries (Fin 2) R :=
  1 + MvPowerSeries.C W.a₂ * W.fgSlope
    + MvPowerSeries.C W.a₄ * W.fgSlope ^ 2
    + MvPowerSeries.C W.a₆ * W.fgSlope ^ 3

noncomputable def fgInvDenom : R⟦X⟧ :=
  1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * W.formalW

noncomputable def fgInv : R⟦X⟧ :=
  - PowerSeries.X * PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ)

theorem coeff_fgSlope (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d W.fgSlope = PowerSeries.coeff (d 0 + d 1 + 1) W.formalW :=
  rfl

theorem constantCoeff_fgSlope : MvPowerSeries.constantCoeff (σ := Fin 2) W.fgSlope = 0 := by
  have h := W.coeff_fgSlope 0
  simpa [MvPowerSeries.coeff_zero_eq_constantCoeff, W.coeff_formalW_one] using h

end WeierstrassCurve

end

noncomputable section
open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem degree_fin2 (d : Fin 2 →₀ ℕ) : Finsupp.degree d = d 0 + d 1 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem two_le_order_mul_left {f g : MvPowerSeries (Fin 2) R} (h : (2 : ℕ∞) ≤ f.order) :
    (2 : ℕ∞) ≤ (f * g).order :=
  le_trans (le_trans h le_self_add) MvPowerSeries.le_order_mul

theorem constantCoeff_fgNu : MvPowerSeries.constantCoeff (σ := Fin 2) W.fgNu = 0 := by
  unfold fgNu fgW₁
  rw [map_sub, map_mul,
      PowerSeries.constantCoeff_subst_eq_zero
        (by simp [MvPowerSeries.constantCoeff_X]) W.formalW W.constantCoeff_formalW,
      MvPowerSeries.constantCoeff_X, mul_zero, sub_zero]

theorem hasSubst_X0 :
    PowerSeries.HasSubst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp [MvPowerSeries.constantCoeff_X])

theorem constantCoeff_fgInv : PowerSeries.constantCoeff W.fgInv = 0 := by
  unfold fgInv
  simp [map_mul, map_neg, PowerSeries.constantCoeff_X]

theorem coeff_one_fgInv : PowerSeries.coeff 1 W.fgInv = -1 := by
  unfold fgInv
  rw [neg_mul, map_neg, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.constantCoeff_invOfUnit]
  simp

theorem coeff_fgSlope_eq_zero_of_le_one (d : Fin 2 →₀ ℕ) (hd : d 0 + d 1 ≤ 1) :
    MvPowerSeries.coeff d W.fgSlope = 0 := by
  rw [W.coeff_fgSlope]
  interval_cases h : (d 0 + d 1)
  · simpa using W.coeff_formalW_one
  · simpa using W.coeff_formalW_two

theorem two_le_order_fgSlope : (2 : ℕ∞) ≤ W.fgSlope.order := by
  apply MvPowerSeries.le_order
  intro d hd
  apply W.coeff_fgSlope_eq_zero_of_le_one
  have hd' : Finsupp.degree d < 2 := by exact_mod_cast hd
  rw [degree_fin2 d] at hd'
  omega

theorem two_le_order_fgW1 : (2 : ℕ∞) ≤ W.fgW₁.order := by
  apply MvPowerSeries.le_order
  intro d hd
  have hdeg : d 0 + d 1 ≤ 1 := by
    have h2 : Finsupp.degree d < 2 := by exact_mod_cast hd
    rw [degree_fin2 d] at h2; omega
  unfold fgW₁
  rw [PowerSeries.coeff_subst hasSubst_X0,
      finsum_eq_single _ (d 0) (fun n hn => by
        rw [MvPowerSeries.coeff_X_pow, ite_eq_right (fun h => hn (by
          have := congrFun (congrArg DFunLike.coe h) 0
          simp at this; omega)), smul_zero]),
      MvPowerSeries.coeff_X_pow]
  by_cases hd1 : d 1 = 0
  · have hdeq : d = Finsupp.single 0 (d 0) := by
      ext j; fin_cases j <;> simp [hd1]
    rw [ite_eq_left hdeq]
    have : d 0 ≤ 1 := by omega
    interval_cases hh : (d 0)
    · simp [W.coeff_formalW_zero]
    · simp [W.coeff_formalW_one]
  · rw [ite_eq_right (fun h => hd1 (by
      have := congrFun (congrArg DFunLike.coe h) 1
      simpa [Finsupp.single_apply] using this)), smul_zero]

theorem two_le_order_fgNu : (2 : ℕ∞) ≤ W.fgNu.order := by
  apply MvPowerSeries.le_order
  intro d hd
  unfold fgNu
  rw [map_sub,
      MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le hd W.two_le_order_fgW1),
      MvPowerSeries.coeff_of_lt_order
        (lt_of_lt_of_le hd (two_le_order_mul_left W.two_le_order_fgSlope)),
      sub_zero]

end WeierstrassCurve

end

noncomputable section

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

noncomputable def fgZ3Num : MvPowerSeries (Fin 2) R :=
  - ( MvPowerSeries.C W.a₁ * W.fgSlope
    + MvPowerSeries.C W.a₃ * W.fgSlope ^ 2
    + MvPowerSeries.C W.a₂ * W.fgNu
    + MvPowerSeries.C (2 * W.a₄) * (W.fgSlope * W.fgNu)
    + MvPowerSeries.C (3 * W.a₆) * (W.fgSlope ^ 2 * W.fgNu) )

noncomputable def fgZ3 : MvPowerSeries (Fin 2) R :=
  - MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)
    + W.fgZ3Num * MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ)

/-- **Formal group law of a Weierstrass curve.** The power series `F(z₁, z₂)`: `fgZ3` is the
third point where the chord through `(z₁, w(z₁))` and `(z₂, w(z₂))` meets the curve, and
`F(z₁, z₂)` is its image under the formal inverse `fgInv`. -/
noncomputable def formalGroupLaw : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst W.fgZ3 W.fgInv

theorem constantCoeff_fgZ3Num :
    MvPowerSeries.constantCoeff (σ := Fin 2) W.fgZ3Num = 0 := by
  unfold fgZ3Num
  simp [map_neg, map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, W.constantCoeff_fgSlope,
        W.constantCoeff_fgNu]

theorem two_le_order_fgZ3Num : (2 : ℕ∞) ≤ W.fgZ3Num.order := by
  apply MvPowerSeries.le_order
  intro d hd
  have oS := W.two_le_order_fgSlope
  have oN := W.two_le_order_fgNu
  have oS2 : (2 : ℕ∞) ≤ (W.fgSlope ^ 2).order := by rw [pow_two]; exact two_le_order_mul_left oS
  have e : ∀ P : MvPowerSeries (Fin 2) R, (2 : ℕ∞) ≤ P.order → MvPowerSeries.coeff d P = 0 :=
    fun P hP => MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le hd hP)
  unfold fgZ3Num
  rw [map_neg, neg_eq_zero]
  simp only [map_add, MvPowerSeries.coeff_C_mul,
    e _ oS, e _ oS2, e _ oN, e _ (two_le_order_mul_left oS), e _ (two_le_order_mul_left oS2),
    mul_zero, add_zero]

theorem constantCoeff_fgZ3 :
    MvPowerSeries.constantCoeff (σ := Fin 2) W.fgZ3 = 0 := by
  unfold fgZ3
  simp [map_add, map_sub, map_neg, map_mul, MvPowerSeries.constantCoeff_X,
        W.constantCoeff_fgZ3Num]

theorem hasSubst_fgZ3 : PowerSeries.HasSubst W.fgZ3 :=
  PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_fgZ3

theorem coeff_single_fgZ3 (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 1) W.fgZ3 = -1 := by
  unfold fgZ3
  have hprod : MvPowerSeries.coeff (Finsupp.single i 1)
      (W.fgZ3Num * MvPowerSeries.invOfUnit W.fgZ3Denom 1) = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    calc ((Finsupp.degree (Finsupp.single i 1) : ℕ) : ℕ∞)
          = (1 : ℕ∞) := by simp [Finsupp.degree_single]
      _ < (2 : ℕ∞) := by norm_num
      _ ≤ _ := two_le_order_mul_left W.two_le_order_fgZ3Num
  rw [map_add, map_sub, map_neg, hprod, add_zero]
  fin_cases i <;> simp [MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff]

theorem coeff_fgZ3_pow_eq_zero (d : Fin 2 →₀ ℕ) (hd : Finsupp.degree d ≤ 1) {n : ℕ}
    (hn : 2 ≤ n) : MvPowerSeries.coeff d (W.fgZ3 ^ n) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  calc ((Finsupp.degree d : ℕ) : ℕ∞) ≤ (1 : ℕ∞) := by exact_mod_cast hd
    _ < (n : ℕ∞) := by exact_mod_cast hn
    _ ≤ (W.fgZ3 ^ n).order :=
        MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n W.constantCoeff_fgZ3

theorem constantCoeff_formalGroupLaw :
    MvPowerSeries.constantCoeff (σ := Fin 2) W.formalGroupLaw = 0 := by
  unfold formalGroupLaw
  rw [PowerSeries.constantCoeff_subst W.hasSubst_fgZ3]
  rw [finsum_eq_single _ 0 (fun d hd => by
    rw [map_pow, W.constantCoeff_fgZ3, zero_pow hd, smul_zero])]
  rw [map_pow, pow_zero]
  simp [W.constantCoeff_fgInv]

theorem coeff_single_formalGroupLaw (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 1) W.formalGroupLaw = 1 := by
  unfold formalGroupLaw
  rw [PowerSeries.coeff_subst W.hasSubst_fgZ3]
  rw [finsum_eq_single _ 1 (fun d hd => by
    rcases Nat.lt_or_ge d 2 with h2 | h2
    · interval_cases d
      · simp [pow_zero, MvPowerSeries.coeff_one, Finsupp.single_eq_zero]
      · exact absurd rfl hd
    · rw [W.coeff_fgZ3_pow_eq_zero _ (by simp [Finsupp.degree_single]) h2, smul_zero])]
  rw [pow_one, W.coeff_one_fgInv, W.coeff_single_fgZ3]
  simp

theorem coeff_zero_formalGroupLaw :
    MvPowerSeries.coeff (Finsupp.single 0 1) W.formalGroupLaw = 1 :=
  W.coeff_single_formalGroupLaw 0

theorem coeff_one_formalGroupLaw :
    MvPowerSeries.coeff (Finsupp.single 1 1) W.formalGroupLaw = 1 :=
  W.coeff_single_formalGroupLaw 1

theorem coeff_two_fgInv : PowerSeries.coeff 2 W.fgInv = - W.a₁ := by
  have hden0 : PowerSeries.constantCoeff W.fgInvDenom = 1 := by
    unfold fgInvDenom
    simp [map_sub, map_mul, PowerSeries.constantCoeff_X, W.constantCoeff_formalW]
  have hden1 : PowerSeries.coeff 1 W.fgInvDenom = - W.a₁ := by
    unfold fgInvDenom
    simp [map_sub, PowerSeries.coeff_C_mul, W.coeff_formalW_one]
  have hc0den : PowerSeries.coeff 0 W.fgInvDenom = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact hden0
  have hmul : W.fgInv * W.fgInvDenom = - PowerSeries.X := by
    unfold fgInv
    rw [mul_assoc, mul_comm (PowerSeries.invOfUnit W.fgInvDenom 1) W.fgInvDenom,
        PowerSeries.mul_invOfUnit W.fgInvDenom 1 (by rw [hden0]; simp), mul_one]
  have hc0 : PowerSeries.coeff 0 W.fgInv = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact W.constantCoeff_fgInv
  have key := congrArg (PowerSeries.coeff 2) hmul
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i W.fgInv * PowerSeries.coeff j W.fgInvDenom)] at key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_self,
    Nat.sub_zero] at key
  rw [hc0, W.coeff_one_fgInv, hden1, hc0den,
      show PowerSeries.coeff (R := R) 2 (- PowerSeries.X) = 0 by simp [PowerSeries.coeff_X]] at key
  linear_combination key

theorem three_le_order_fgW1 : (3 : ℕ∞) ≤ W.fgW₁.order := by
  apply MvPowerSeries.le_order
  intro d hd
  have hdeg : d 0 + d 1 ≤ 2 := by
    have h2 : Finsupp.degree d < 3 := by exact_mod_cast hd
    rw [degree_fin2 d] at h2; omega
  unfold fgW₁
  rw [PowerSeries.coeff_subst hasSubst_X0,
      finsum_eq_single _ (d 0) (fun n hn => by
        rw [MvPowerSeries.coeff_X_pow, ite_eq_right (fun h => hn (by
          have := congrFun (congrArg DFunLike.coe h) 0
          simp at this; omega)), smul_zero]),
      MvPowerSeries.coeff_X_pow]
  by_cases hd1 : d 1 = 0
  · have hdeq : d = Finsupp.single 0 (d 0) := by
      ext j; fin_cases j <;> simp [hd1]
    rw [ite_eq_left hdeq]
    have : d 0 ≤ 2 := by omega
    interval_cases hh : (d 0)
    · simp [W.coeff_formalW_zero]
    · simp [W.coeff_formalW_one]
    · simp [W.coeff_formalW_two]
  · rw [ite_eq_right (fun h => hd1 (by
      have := congrFun (congrArg DFunLike.coe h) 1
      simpa [Finsupp.single_apply] using this)), smul_zero]

theorem three_le_order_fgNu : (3 : ℕ∞) ≤ W.fgNu.order := by
  apply MvPowerSeries.le_order
  intro d hd
  have hX0 : (1 : ℕ∞) ≤ (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R).order := by
    apply MvPowerSeries.le_order
    intro e he
    rw [MvPowerSeries.coeff_X, ite_eq_right (fun hcon => by
      rw [hcon, Finsupp.degree_single] at he
      exact absurd he (by norm_num))]
  have hSX : (3 : ℕ∞) ≤ (W.fgSlope * MvPowerSeries.X (0 : Fin 2)).order := by
    calc (3 : ℕ∞) = 2 + 1 := by norm_num
      _ ≤ W.fgSlope.order + (MvPowerSeries.X (0 : Fin 2)).order :=
          add_le_add W.two_le_order_fgSlope hX0
      _ ≤ _ := MvPowerSeries.le_order_mul
  unfold fgNu
  rw [map_sub, MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le hd W.three_le_order_fgW1),
      MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le hd hSX), sub_zero]

theorem eq_zero_of_degree_lt_one (e : Fin 2 →₀ ℕ) (he : (↑(Finsupp.degree e) : ℕ∞) < 1) :
    e = 0 :=
  (Finsupp.degree_eq_zero_iff e).mp (Nat.lt_one_iff.mp (by exact_mod_cast he))

theorem coeff_sq_mul_invD {Num : MvPowerSeries (Fin 2) R} (hNum : (2 : ℕ∞) ≤ Num.order)
    (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 2) (Num * MvPowerSeries.invOfUnit W.fgZ3Denom 1)
      = MvPowerSeries.coeff (Finsupp.single i 2) Num := by
  set D := MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ) with hDdef
  have hD0 : MvPowerSeries.constantCoeff (σ := Fin 2) D = 1 := by
    rw [hDdef, MvPowerSeries.constantCoeff_invOfUnit]; simp
  have hDm1 : (1 : ℕ∞) ≤ (D - 1).order := by
    apply MvPowerSeries.le_order
    intro e he
    rw [eq_zero_of_degree_lt_one e he, MvPowerSeries.coeff_zero_eq_constantCoeff,
        map_sub, hD0, map_one, sub_self]
  have hcross : MvPowerSeries.coeff (Finsupp.single i 2) (Num * (D - 1)) = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    calc ((Finsupp.degree (Finsupp.single i 2) : ℕ) : ℕ∞) = 2 := by simp [Finsupp.degree_single]
      _ < 3 := by norm_num
      _ ≤ Num.order + (D - 1).order := by
          calc (3 : ℕ∞) ≤ 2 + 1 := by norm_num
            _ ≤ Num.order + (D - 1).order := add_le_add hNum hDm1
      _ ≤ _ := MvPowerSeries.le_order_mul
  have hsplit : Num * D = Num + Num * (D - 1) := by ring
  rw [hsplit, map_add, hcross, add_zero]

theorem coeff_sq_fgZ3Num (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 2) W.fgZ3Num = - W.a₁ := by
  have ez : ∀ P : MvPowerSeries (Fin 2) R, (3 : ℕ∞) ≤ P.order →
      MvPowerSeries.coeff (Finsupp.single i 2) P = 0 := by
    intro P hP
    apply MvPowerSeries.coeff_of_lt_order
    calc ((Finsupp.degree (Finsupp.single i 2) : ℕ) : ℕ∞) = 2 := by simp [Finsupp.degree_single]
      _ < 3 := by norm_num
      _ ≤ P.order := hP
  have oS := W.two_le_order_fgSlope
  have oN := W.three_le_order_fgNu
  have hsl : MvPowerSeries.coeff (Finsupp.single i 2) W.fgSlope = 1 := by
    rw [W.coeff_fgSlope]
    have h3 : (Finsupp.single i 2) 0 + (Finsupp.single i 2) 1 + 1 = 3 := by
      fin_cases i <;> simp
    rw [h3]; exact W.coeff_formalW_three
  have hsl2 : (3 : ℕ∞) ≤ (W.fgSlope ^ 2).order := by
    rw [pow_two]
    exact le_trans (by calc (3 : ℕ∞) ≤ 2 + 2 := by norm_num
                          _ ≤ W.fgSlope.order + W.fgSlope.order := add_le_add oS oS)
      MvPowerSeries.le_order_mul
  have hslN : (3 : ℕ∞) ≤ (W.fgSlope * W.fgNu).order :=
    le_trans (by calc (3 : ℕ∞) ≤ 2 + 3 := by norm_num
                      _ ≤ W.fgSlope.order + W.fgNu.order := add_le_add oS oN)
      MvPowerSeries.le_order_mul
  have hsl2N : (3 : ℕ∞) ≤ (W.fgSlope ^ 2 * W.fgNu).order :=
    le_trans (by calc (3 : ℕ∞) ≤ 3 + 3 := by norm_num
                      _ ≤ (W.fgSlope ^ 2).order + W.fgNu.order := add_le_add hsl2 oN)
      MvPowerSeries.le_order_mul
  unfold fgZ3Num
  rw [map_neg, map_add, map_add, map_add, map_add,
      MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      hsl, ez _ hsl2, ez _ oN, ez _ hslN, ez _ hsl2N]
  ring

theorem coeff_sq_fgZ3 (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 2) W.fgZ3 = - W.a₁ := by
  have hlin : MvPowerSeries.coeff (Finsupp.single i 2)
      ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) : MvPowerSeries (Fin 2) R)
        = 0 := by
    simp [map_sub, map_neg, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff]
  unfold fgZ3
  rw [map_add, hlin, zero_add, W.coeff_sq_mul_invD W.two_le_order_fgZ3Num,
      W.coeff_sq_fgZ3Num]

theorem coeff_pow_lt {g : MvPowerSeries (Fin 2) R}
    (hg : MvPowerSeries.constantCoeff (σ := Fin 2) g = 0) (d : Fin 2 →₀ ℕ) {n : ℕ}
    (hlt : Finsupp.degree d < n) : MvPowerSeries.coeff d (g ^ n) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  calc ((Finsupp.degree d : ℕ) : ℕ∞) < (n : ℕ∞) := by exact_mod_cast hlt
    _ ≤ (g ^ n).order := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n hg

theorem coeff_sq_pow2 {H : MvPowerSeries (Fin 2) R} (hH : (2 : ℕ∞) ≤ H.order) (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 2)
        ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) + H) ^ 2) = 1 := by
  have hXX1 : (1 : ℕ∞) ≤ (((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2))
      : MvPowerSeries (Fin 2) R)).order := by
    apply MvPowerSeries.le_order
    intro e he
    rw [eq_zero_of_degree_lt_one e he, MvPowerSeries.coeff_zero_eq_constantCoeff]
    simp [map_sub, map_neg, MvPowerSeries.constantCoeff_X]
  have ez3 : ∀ P : MvPowerSeries (Fin 2) R, (3 : ℕ∞) ≤ P.order →
      MvPowerSeries.coeff (Finsupp.single i 2) P = 0 := by
    intro P hP
    apply MvPowerSeries.coeff_of_lt_order
    calc ((Finsupp.degree (Finsupp.single i 2) : ℕ) : ℕ∞) = 2 := by simp [Finsupp.degree_single]
      _ < 3 := by norm_num
      _ ≤ P.order := hP
  have expand : (- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) + H) ^ 2
      = (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) ^ 2
        + ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H * 2 + H * H) := by
    ring
  rw [expand, map_add]
  have hcr : MvPowerSeries.coeff (Finsupp.single i 2)
      ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H * 2 + H * H) = 0 := by
    rw [map_add]
    have hHH : (3 : ℕ∞) ≤ (H * H).order :=
      le_trans (by calc (3 : ℕ∞) ≤ 2 + 2 := by norm_num
                        _ ≤ H.order + H.order := add_le_add hH hH) MvPowerSeries.le_order_mul
    have hLH : (3 : ℕ∞) ≤
        ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H * 2).order := by
      have hbase : (3 : ℕ∞) ≤
          ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H).order :=
        le_trans (by calc (3 : ℕ∞) ≤ 1 + 2 := by norm_num
                          _ ≤ (((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2))
                                : MvPowerSeries (Fin 2) R)).order + H.order :=
                            add_le_add hXX1 hH) MvPowerSeries.le_order_mul
      exact le_trans hbase (le_trans le_self_add MvPowerSeries.le_order_mul)
    rw [ez3 _ hLH, ez3 _ hHH, add_zero]
  rw [hcr, add_zero]
  have hexp2 : (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) :
        MvPowerSeries (Fin 2) R) ^ 2
      = MvPowerSeries.X 0 ^ 2 + MvPowerSeries.X 0 * MvPowerSeries.X 1 * 2
        + MvPowerSeries.X 1 ^ 2 := by
    ring
  have hmono : (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)
      = MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]
  have hX0X1c : MvPowerSeries.coeff (Finsupp.single i 2)
      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = 0 := by
    rw [hmono, MvPowerSeries.coeff_monomial, ite_eq_right]
    intro hcon
    have hc := congrFun (congrArg (DFunLike.coe) hcon.symm) i
    fin_cases i <;> simp [Finsupp.add_apply] at hc
  have hX0X1 : MvPowerSeries.coeff (Finsupp.single i 2)
      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 * 2 : MvPowerSeries (Fin 2) R) = 0 := by
    rw [show (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 * 2 : MvPowerSeries (Fin 2) R)
          = MvPowerSeries.C 2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1) by
        rw [map_ofNat]; ring,
        MvPowerSeries.coeff_C_mul, hX0X1c, mul_zero]
  rw [hexp2, map_add, map_add, hX0X1, add_zero, MvPowerSeries.coeff_X_pow,
      MvPowerSeries.coeff_X_pow]
  fin_cases i <;> simp [Finsupp.single_eq_single_iff]

theorem coeff_sq_subst {g : MvPowerSeries (Fin 2) R} {i : Fin 2} (hg : PowerSeries.HasSubst g)
    (hgc : MvPowerSeries.constantCoeff (σ := Fin 2) g = 0)
    (hg1 : MvPowerSeries.coeff (Finsupp.single i 2) (g ^ 2) = 1) :
    MvPowerSeries.coeff (Finsupp.single i 2) (PowerSeries.subst g W.fgInv)
      = - MvPowerSeries.coeff (Finsupp.single i 2) g - W.a₁ := by
  rw [PowerSeries.coeff_subst hg,
    finsum_eq_finsetSum_of_support_subset _ (s := {1, 2}) (by
      intro n hn
      rw [Function.mem_support] at hn
      match n with
      | 0 => exact absurd (by
          rw [pow_zero, MvPowerSeries.coeff_one, ite_eq_right (by simp [Finsupp.single_eq_zero]),
              smul_zero]) hn
      | 1 => simp
      | 2 => simp
      | (k + 3) => exact absurd (by
          rw [coeff_pow_lt hgc (Finsupp.single i 2) (by rw [Finsupp.degree_single]; omega),
              smul_zero]) hn),
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), pow_one, W.coeff_one_fgInv,
    W.coeff_two_fgInv, hg1]
  simp only [smul_eq_mul]
  ring

theorem coeff_sq_formalGroupLaw (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 2) W.formalGroupLaw = 0 := by
  have hpow2 : MvPowerSeries.coeff (Finsupp.single i 2) (W.fgZ3 ^ 2) = 1 := by
    have hH : (2 : ℕ∞) ≤ (W.fgZ3Num * MvPowerSeries.invOfUnit W.fgZ3Denom 1).order :=
      le_trans W.two_le_order_fgZ3Num (le_trans le_self_add MvPowerSeries.le_order_mul)
    have := coeff_sq_pow2 hH i
    rwa [show (- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)
      + W.fgZ3Num * MvPowerSeries.invOfUnit W.fgZ3Denom 1) = W.fgZ3 from rfl] at this
  unfold formalGroupLaw
  rw [W.coeff_sq_subst W.hasSubst_fgZ3 W.constantCoeff_fgZ3 hpow2,
      W.coeff_sq_fgZ3]
  ring

end WeierstrassCurve

end
