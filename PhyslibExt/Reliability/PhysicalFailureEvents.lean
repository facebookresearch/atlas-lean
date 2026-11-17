/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Physical failure events: critical crack length in an LEFM model

## i. Overview

This file starts the physical-failure-event layer: deterministic material
failure thresholds stated as explicit model inputs, whose algebraic
consequences are proved and can later be composed with lifetime and
reliability models. The first model is the standard linear-elastic
fracture mechanics (LEFM) mode-I stress intensity
`K_I(a) = Y * σ * √(π * a)` for a constant geometry factor `Y`, peak
tensile stress `σ`, and crack length `a ≥ 0`, together with the critical
crack length at which `K_I` reaches the fracture toughness `K_IC`.

The stress-intensity formula is an adopted model input with a
small-scale-yielding validity regime. Nothing here validates the model
empirically, and `σ` is a peak tensile stress, not a fatigue stress range.

## ii. Key results

- `Reliability.criticalCrackLength_pos`: the critical crack length is
  positive for positive toughness, geometry factor, and stress.
- `Reliability.modeIStressIntensity_criticalCrackLength`: `K_I` equals
  `K_IC` exactly at the critical crack length.
- `Reliability.modeIStressIntensity_lt_iff_lt_criticalCrackLength`:
  subcriticality `K_I(a) < K_IC` is equivalent to `a < a_c`.
- `Reliability.crackFailure_iff_criticalCrackLength_le`: the
  equality-inclusive failure event is equivalent to `a_c ≤ a`.
- `Reliability.parisCrackPow_at_life` and
  `Reliability.parisCrackExp_at_life`: Paris-law crack-growth solutions
  in the power (`m ≠ 2`) and logarithmic (`m = 2`) branches reach the
  critical length exactly at their Paris lives, with first-crossing
  characterizations `parisCrackPow_lt_iff` and `parisCrackExp_lt_iff`.

## iii. Table of contents

- A. Mode-I stress intensity and the critical crack length
- B. Paris-law crack growth to the critical length

## iv. References

- N. E. Dowling, *Mechanical Behavior of Materials: Engineering Methods
  for Deformation, Fracture, and Fatigue*, 4th ed., Pearson (2013): the
  mode-I stress intensity model and the critical-crack condition
  `K_I = K_IC` used here.

## A. Mode-I stress intensity and the critical crack length

-/

@[expose] public section

namespace Reliability

/-- Mode-I stress intensity factor in the adopted linear-elastic fracture
mechanics (LEFM) model `K_I(a) = Y * σ * √(π * a)`, where `Y` is a constant
geometry factor, `σ` is the peak tensile stress, and `a` is the crack length.
This formula is a model input with a small-scale-yielding validity regime;
the theorems below are its algebraic consequences, not an experimental
validation of the model. The formula is intended for `0 ≤ a`. -/
noncomputable def modeIStressIntensity (Y σ a : ℝ) : ℝ :=
  Y * σ * Real.sqrt (Real.pi * a)

/-- Critical crack length `a_c = (K_IC / (Y * σ)) ^ 2 / π` in the same LEFM
model: the crack length at which `modeIStressIntensity` reaches the fracture
toughness `K_IC`. -/
noncomputable def criticalCrackLength (KIC Y σ : ℝ) : ℝ :=
  (KIC / (Y * σ)) ^ 2 / Real.pi

/-- Equality-inclusive crack failure in this model: the mode-I stress
intensity demand reaches the fracture toughness. -/
def crackFailure (KIC Y σ a : ℝ) : Prop :=
  KIC ≤ modeIStressIntensity Y σ a

/-- At zero crack length the mode-I stress intensity is zero. -/
lemma modeIStressIntensity_zero (Y σ : ℝ) :
    modeIStressIntensity Y σ 0 = 0 := by
  simp [modeIStressIntensity]

/-- For positive fracture toughness, geometry factor, and peak tensile
stress, the critical crack length is positive. -/
lemma criticalCrackLength_pos {KIC Y σ : ℝ} (hKIC : 0 < KIC) (hY : 0 < Y)
    (hσ : 0 < σ) :
    0 < criticalCrackLength KIC Y σ := by
  unfold criticalCrackLength
  exact div_pos (pow_pos (div_pos hKIC (mul_pos hY hσ)) 2) Real.pi_pos

/-- The LEFM critical condition: at the critical crack length, the mode-I
stress intensity equals the fracture toughness `K_IC`. This is the standard
critical-crack criterion of linear-elastic fracture mechanics (see, for
example, Dowling, *Mechanical Behavior of Materials*, 4th ed.), stated here
for the adopted intensity model `K_I(a) = Y * σ * √(π * a)`. -/
theorem modeIStressIntensity_criticalCrackLength {KIC Y σ : ℝ}
    (hKIC : 0 < KIC) (hY : 0 < Y) (hσ : 0 < σ) :
    modeIStressIntensity Y σ (criticalCrackLength KIC Y σ) = KIC := by
  have hYσ : 0 < Y * σ := mul_pos hY hσ
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hYσ' : Y * σ ≠ 0 := ne_of_gt hYσ
  have hK : 0 < KIC / (Y * σ) := div_pos hKIC hYσ
  unfold modeIStressIntensity criticalCrackLength
  rw [mul_comm Real.pi _, div_mul_cancel₀ _ hπ, Real.sqrt_sq (le_of_lt hK),
    mul_comm (Y * σ) _, div_mul_cancel₀ _ hYσ']

/-- Subcriticality characterization: for nonnegative crack length, the
mode-I stress intensity is strictly below the fracture toughness exactly
below the critical crack length. -/
lemma modeIStressIntensity_lt_iff_lt_criticalCrackLength {KIC Y σ a : ℝ}
    (hKIC : 0 < KIC) (hY : 0 < Y) (hσ : 0 < σ) (ha : 0 ≤ a) :
    modeIStressIntensity Y σ a < KIC ↔ a < criticalCrackLength KIC Y σ := by
  have hYσ : 0 < Y * σ := mul_pos hY hσ
  have hK : 0 < KIC / (Y * σ) := div_pos hKIC hYσ
  unfold modeIStressIntensity criticalCrackLength
  rw [mul_comm (Y * σ) _, ← lt_div_iff₀ hYσ,
    Real.sqrt_lt (mul_nonneg (le_of_lt Real.pi_pos) ha) (le_of_lt hK),
    mul_comm Real.pi a, lt_div_iff₀ Real.pi_pos]

/-- The equality-inclusive crack-failure event holds exactly from the
critical crack length on. -/
lemma crackFailure_iff_criticalCrackLength_le {KIC Y σ a : ℝ}
    (hKIC : 0 < KIC) (hY : 0 < Y) (hσ : 0 < σ) (ha : 0 ≤ a) :
    crackFailure KIC Y σ a ↔ criticalCrackLength KIC Y σ ≤ a := by
  unfold crackFailure
  rw [← not_lt, ← not_lt,
    modeIStressIntensity_lt_iff_lt_criticalCrackLength hKIC hY hσ ha]

/- ### B. Paris-law crack growth -/

/-- Paris-law crack-growth solution, power branch. With growth exponent
`m ≠ 2` and coefficient `K > 0` in `da/dN = K * a ^ (m / 2)`, writing
`r = 1 - m / 2 ≠ 0`, the solution with `a(0) = a0` is
`a(N) = (a0 ^ r + r * K * N) ^ (1 / r)`. It is valid only while the base
`a0 ^ r + r * K * N` stays positive; for `r < 0` (that is, `m > 2`) that
is a finite cycle interval. Real powers are `Real.rpow`. -/
noncomputable def parisCrackPow (r K a0 N : ℝ) : ℝ :=
  (a0 ^ r + r * K * N) ^ r⁻¹

/-- Cycles to grow a crack from `a0` to `ac` in the power branch:
`Nf = (ac ^ r - a0 ^ r) / (r * K)`. -/
noncomputable def parisLifePow (r K a0 ac : ℝ) : ℝ :=
  (ac ^ r - a0 ^ r) / (r * K)

/-- The power-branch solution starts at `a0`. -/
lemma parisCrackPow_zero {r K a0 : ℝ} (hr : r ≠ 0) (ha0 : 0 < a0) :
    parisCrackPow r K a0 0 = a0 := by
  have h : (a0 ^ r + r * K * 0) ^ r⁻¹ = a0 := by
    rw [mul_zero, add_zero]
    exact Real.rpow_rpow_inv (le_of_lt ha0) hr
  exact h

/-- The power-branch solution solves `da/dN = K * a ^ (1 - r)` (with
`1 - r = m / 2`) wherever its base is positive. -/
lemma hasDerivAt_parisCrackPow {r K a0 N : ℝ} (hr : r ≠ 0)
    (hbase : 0 < a0 ^ r + r * K * N) :
    HasDerivAt (parisCrackPow r K a0)
      (K * (parisCrackPow r K a0 N) ^ (1 - r)) N := by
  have hmul : HasDerivAt (fun N : ℝ => r * K * N) (r * K) N := by
    have h := HasDerivAt.const_mul (r * K) (hasDerivAt_id N)
    simpa using h
  have hinner : HasDerivAt (fun N : ℝ => a0 ^ r + r * K * N) (r * K) N :=
    HasDerivAt.const_add (a0 ^ r) hmul
  have hcomp : HasDerivAt (fun y : ℝ => (a0 ^ r + r * K * y) ^ r⁻¹)
      ((r * K) * r⁻¹ * (a0 ^ r + r * K * N) ^ (r⁻¹ - 1)) N :=
    HasDerivAt.rpow_const hinner (Or.inl (ne_of_gt hbase)) (p := r⁻¹)
  have hexp : r⁻¹ * (1 - r) = r⁻¹ - 1 := by
    have hrr : r⁻¹ * r = 1 := by
      rw [mul_comm]
      exact mul_inv_cancel₀ hr
    calc r⁻¹ * (1 - r) = r⁻¹ - r⁻¹ * r := by ring
      _ = r⁻¹ - 1 := by rw [hrr]
  have hbase0 : 0 ≤ a0 ^ r + r * K * N := le_of_lt hbase
  have hpow : (parisCrackPow r K a0 N) ^ (1 - r)
      = (a0 ^ r + r * K * N) ^ (r⁻¹ - 1) := by
    show ((a0 ^ r + r * K * N) ^ r⁻¹) ^ (1 - r)
      = (a0 ^ r + r * K * N) ^ (r⁻¹ - 1)
    rw [← Real.rpow_mul hbase0, hexp]
  have h1 : (r * K) * r⁻¹ = K := by
    calc (r * K) * r⁻¹ = K * (r * r⁻¹) := by ring
      _ = K := by rw [mul_inv_cancel₀ hr, mul_one]
  have hderiv : (r * K) * r⁻¹ * (a0 ^ r + r * K * N) ^ (r⁻¹ - 1)
      = K * (parisCrackPow r K a0 N) ^ (1 - r) := by
    rw [hpow, h1]
  rw [hderiv] at hcomp
  exact hcomp

/-- Raising the power-branch solution to `r` recovers the affine base,
wherever the base is nonnegative. -/
lemma parisCrackPow_pow {r K a0 N : ℝ} (hr : r ≠ 0)
    (hbase : 0 ≤ a0 ^ r + r * K * N) :
    (parisCrackPow r K a0 N) ^ r = a0 ^ r + r * K * N := by
  have h : ((a0 ^ r + r * K * N) ^ r⁻¹) ^ r = a0 ^ r + r * K * N :=
    Real.rpow_inv_rpow hbase hr
  exact h

/-- Positive Paris life in the power branch, for either sign of `r`. -/
lemma parisLifePow_pos {r K a0 ac : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < ac) (hr : r ≠ 0) :
    0 < parisLifePow r K a0 ac := by
  show 0 < (ac ^ r - a0 ^ r) / (r * K)
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · have hnum : ac ^ r - a0 ^ r < 0 := by
      have h := Real.rpow_lt_rpow_of_neg ha0 hac hneg
      linarith
    have hden : r * K < 0 := mul_neg_of_neg_of_pos hneg hK
    exact div_pos_of_neg_of_neg hnum hden
  · have hnum : 0 < ac ^ r - a0 ^ r := by
      have h := Real.rpow_lt_rpow (le_of_lt ha0) hac hpos
      linarith
    have hden : 0 < r * K := mul_pos hpos hK
    exact div_pos hnum hden

/-- At the Paris life, the power-branch crack reaches `ac`. -/
lemma parisCrackPow_at_life {r K a0 ac : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : 0 < ac) (hr : r ≠ 0) :
    parisCrackPow r K a0 (parisLifePow r K a0 ac) = ac := by
  have _ : 0 < a0 := ha0
  have hrK : r * K ≠ 0 := mul_ne_zero hr (ne_of_gt hK)
  have hcancel : r * K * ((ac ^ r - a0 ^ r) / (r * K)) = ac ^ r - a0 ^ r :=
    mul_div_cancel₀ _ hrK
  have hbase : a0 ^ r + r * K * (parisLifePow r K a0 ac) = ac ^ r := by
    show a0 ^ r + r * K * ((ac ^ r - a0 ^ r) / (r * K)) = ac ^ r
    rw [hcancel]
    ring
  have h : (a0 ^ r + r * K * (parisLifePow r K a0 ac)) ^ r⁻¹ = ac := by
    rw [hbase]
    exact Real.rpow_rpow_inv (le_of_lt hac) hr
  exact h

/-- First-crossing characterization in the power branch: on the
solution's strict domain (positive base `a0 ^ r + r * K * N`; at base
zero with `r < 0` the real-power formula has the junk value `0` instead
of the blow-up limit, so the crossing statement needs the strict
domain), the crack is below `ac` exactly before the Paris life. -/
lemma parisCrackPow_lt_iff {r K a0 ac N : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < ac) (hr : r ≠ 0)
    (hbase : 0 < a0 ^ r + r * K * N) :
    parisCrackPow r K a0 N < ac ↔ N < parisLifePow r K a0 ac := by
  have hac0 : 0 < ac := lt_trans ha0 hac
  have hcrack : 0 < parisCrackPow r K a0 N := by
    show 0 < (a0 ^ r + r * K * N) ^ r⁻¹
    exact Real.rpow_pos_of_pos hbase _
  have hpow : (parisCrackPow r K a0 N) ^ r = a0 ^ r + r * K * N :=
    parisCrackPow_pow hr (le_of_lt hbase)
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · have hden : r * K < 0 := mul_neg_of_neg_of_pos hneg hK
    have hN : N < parisLifePow r K a0 ac ↔ ac ^ r < a0 ^ r + r * K * N := by
      show N < (ac ^ r - a0 ^ r) / (r * K) ↔ ac ^ r < a0 ^ r + r * K * N
      rw [lt_div_iff_of_neg hden]
      have heq : N * (r * K) = r * K * N := by ring
      rw [heq]
      constructor <;> intro h <;> linarith
    have c1 : parisCrackPow r K a0 N < ac
        ↔ ac ^ r < (parisCrackPow r K a0 N) ^ r :=
      (Real.rpow_lt_rpow_iff_of_neg hac0 hcrack hneg).symm
    have c2 : (ac ^ r < (parisCrackPow r K a0 N) ^ r)
        ↔ (ac ^ r < a0 ^ r + r * K * N) := by
      rw [hpow]
    exact c1.trans (c2.trans hN.symm)
  · have hden : 0 < r * K := mul_pos hpos hK
    have hN : N < parisLifePow r K a0 ac ↔ a0 ^ r + r * K * N < ac ^ r := by
      show N < (ac ^ r - a0 ^ r) / (r * K) ↔ a0 ^ r + r * K * N < ac ^ r
      rw [lt_div_iff₀ hden]
      have heq : N * (r * K) = r * K * N := by ring
      rw [heq]
      constructor <;> intro h <;> linarith
    have c1 : parisCrackPow r K a0 N < ac
        ↔ (parisCrackPow r K a0 N) ^ r < ac ^ r :=
      (Real.rpow_lt_rpow_iff (le_of_lt hcrack) (le_of_lt hac0) hpos).symm
    have c2 : ((parisCrackPow r K a0 N) ^ r < ac ^ r)
        ↔ (a0 ^ r + r * K * N < ac ^ r) := by
      rw [hpow]
    exact c1.trans (c2.trans hN.symm)

/-- For `r < 0` (growth exponent `m > 2`), the Paris life is strictly
before the blow-up cycle count `a0 ^ r / (-(r * K))` at which the
power-branch base would reach zero. -/
lemma parisLifePow_lt_blowup {r K a0 ac : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < ac) (hr : r < 0) :
    parisLifePow r K a0 ac < a0 ^ r / (-(r * K)) := by
  have hden : r * K < 0 := mul_neg_of_neg_of_pos hr hK
  have hac0 : 0 < ac := lt_trans ha0 hac
  have hpos : 0 < ac ^ r := Real.rpow_pos_of_pos hac0 _
  have hRHS : a0 ^ r / (-(r * K)) = -(a0 ^ r / (r * K)) := by
    rw [div_neg]
  show (ac ^ r - a0 ^ r) / (r * K) < a0 ^ r / (-(r * K))
  rw [hRHS]
  have hadd : (ac ^ r - a0 ^ r) / (r * K) + a0 ^ r / (r * K)
      = ac ^ r / (r * K) := by
    have e : (ac ^ r - a0 ^ r) + a0 ^ r = ac ^ r := by ring
    rw [← add_div, e]
  have hneg : ac ^ r / (r * K) < 0 := div_neg_of_pos_of_neg hpos hden
  have hXY : (ac ^ r - a0 ^ r) / (r * K) + a0 ^ r / (r * K) < 0 := by
    rw [hadd]
    exact hneg
  linarith

/-- Paris-law crack-growth solution, logarithmic branch (`m = 2`):
`a(N) = a0 * exp (K * N)` solves `da/dN = K * a`. -/
noncomputable def parisCrackExp (K a0 N : ℝ) : ℝ :=
  a0 * Real.exp (K * N)

/-- Cycles to grow a crack from `a0` to `ac` in the logarithmic branch:
`Nf = log (ac / a0) / K`. -/
noncomputable def parisLifeExp (K a0 ac : ℝ) : ℝ :=
  Real.log (ac / a0) / K

/-- The logarithmic-branch solution starts at `a0`. -/
lemma parisCrackExp_zero (K a0 : ℝ) : parisCrackExp K a0 0 = a0 := by
  show a0 * Real.exp (K * 0) = a0
  rw [mul_zero, Real.exp_zero, mul_one]

/-- The logarithmic-branch solution solves `da/dN = K * a`. -/
lemma hasDerivAt_parisCrackExp (K a0 N : ℝ) :
    HasDerivAt (parisCrackExp K a0) (K * parisCrackExp K a0 N) N := by
  have h1 : HasDerivAt (fun N : ℝ => K * N) K N := by
    have h := HasDerivAt.const_mul K (hasDerivAt_id N)
    simpa using h
  have h2 : HasDerivAt (fun N : ℝ => Real.exp (K * N))
      (Real.exp (K * N) * K) N :=
    HasDerivAt.exp h1
  have h3 : HasDerivAt (fun N : ℝ => a0 * Real.exp (K * N))
      (a0 * (Real.exp (K * N) * K)) N :=
    HasDerivAt.const_mul a0 h2
  have hderiv : a0 * (Real.exp (K * N) * K) = K * (a0 * Real.exp (K * N)) := by
    ring
  rw [hderiv] at h3
  exact h3

/-- Positive Paris life in the logarithmic branch. -/
lemma parisLifeExp_pos {K a0 ac : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < ac) :
    0 < parisLifeExp K a0 ac := by
  have h1 : (1 : ℝ) < ac / a0 := by
    rw [lt_div_iff₀ ha0, one_mul]
    exact hac
  show 0 < Real.log (ac / a0) / K
  exact div_pos (Real.log_pos h1) hK

/-- At the Paris life, the logarithmic-branch crack reaches `ac`. -/
lemma parisCrackExp_at_life {K a0 ac : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : 0 < ac) :
    parisCrackExp K a0 (parisLifeExp K a0 ac) = ac := by
  have hK0 : K ≠ 0 := ne_of_gt hK
  have ha00 : a0 ≠ 0 := ne_of_gt ha0
  have hdiv : 0 < ac / a0 := div_pos hac ha0
  have hexp : K * (Real.log (ac / a0) / K) = Real.log (ac / a0) := by
    field_simp
  show a0 * Real.exp (K * (Real.log (ac / a0) / K)) = ac
  rw [hexp, Real.exp_log hdiv]
  field_simp

/-- First-crossing characterization in the logarithmic branch, for all
real cycle counts. -/
lemma parisCrackExp_lt_iff {K a0 ac N : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < ac) :
    parisCrackExp K a0 N < ac ↔ N < parisLifeExp K a0 ac := by
  have hac0 : 0 < ac := lt_trans ha0 hac
  have hdiv : 0 < ac / a0 := div_pos hac0 ha0
  have hexp : Real.exp (Real.log (ac / a0)) = ac / a0 := Real.exp_log hdiv
  have hstep1 : a0 * Real.exp (K * N) < ac ↔ Real.exp (K * N) < ac / a0 := by
    rw [mul_comm a0 (Real.exp (K * N)), lt_div_iff₀ ha0]
  have hstep4 : K * N < Real.log (ac / a0) ↔ N < Real.log (ac / a0) / K := by
    rw [lt_div_iff₀ hK]
    have heq : N * K = K * N := by ring
    rw [heq]
  have c2 : (Real.exp (K * N) < ac / a0)
      ↔ (Real.exp (K * N) < Real.exp (Real.log (ac / a0))) := by
    rw [hexp]
  exact hstep1.trans (c2.trans (Real.exp_lt_exp.trans hstep4))

end Reliability
