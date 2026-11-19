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
public import Mathlib.Basic.Sign.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibExt.Elasticity.PrismaticMembers

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Physical failure events: LEFM crack failure, demand margins and shaft sizing

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

A declared nonnegative demand `s` (an equivalent stress, or a stress
intensity) against a positive allowable `A` has the dimensional margin
`A - s`, in the unit of the demand, and the equality-inclusive failure
event `A ≤ s`; the crack event above is this event with demand `K_I`
and allowable `K_IC`. For a positive demand the margin of safety
`A / s - 1` has the sign of `A - s`; it takes a proof of `0 < s`, since
at zero demand Lean's `A / 0 = 0` would report a false failure. One
axial load path is instantiated: the fixed-fixed bar of
`PhyslibExt.Elasticity.PrismaticMembers` (`0 < L`, axial rigidity
`0 < EA`, cross-section area `0 < A_cs`) under a uniform load `q` has
the axial stress `EA u'(x) / A_cs = q (L - 2 x) / (2 A_cs)`, and a
supplied yield functional calibrated by the tensile test (it returns
`|σ|` on the uniaxial state `diag(σ, 0, 0)`) turns it into the demand
`|q (L - 2 x)| / (2 A_cs)`, largest at the ends. No yield functional is
derived and no constitutive law is added.

A solid circular shaft of diameter `d > 0` under a declared bending
moment `M` and torque `T` has, by the flexure and torsion formulas with
`I = π d ⁴ / 64` and `J = π d ⁴ / 32`, the outer-fiber stresses
`σ = 32 M / (π d ³)` and `τ = 16 T / (π d ³)` at the critical surface
point, whose stress state carries only the axial normal stress `σ` and the
axial-circumferential shear `τ`. A supplied functional calibrated on these
bending-torsion states with a shear factor `c` (it returns
`√(σ ^ 2 + c τ ^ 2)` there: `c = 3` for von Mises, `c = 4` for Tresca) is
in particular calibrated by the tensile test, and turns them into the
demand `16 √(4 M ^ 2 + c T ^ 2) / (π d ³)`. Against a positive allowable
`A` the demand stays within `A` exactly when
`d ≥ (16 √(4 M ^ 2 + c T ^ 2) / (π A)) ^ (1 / 3)`, and the shaft does not
fail exactly when `d` exceeds this minimum. At `d = 0` Lean's `x / 0 = 0`
would report zero demand, so `0 < d` is a hypothesis; at the nominal
minimum diameter a bending stress-concentration factor `K > 1` pushes the
demand above the allowable, so the nominal sizing covers a plain shaft
only. Fasteners, preload, fatigue and transverse shear are not modeled.

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
- `Reliability.dimensionalMargin`, `Reliability.demandFailure` and
  `Reliability.marginOfSafety`: the margin, the event and the ratio,
  with `Reliability.sign_marginOfSafety`,
  `Reliability.demandFailure_iff_marginOfSafety_nonpos` and
  `Reliability.ratio_at_zero_demand_misreports`.
- `Reliability.crackFailure_iff_demandFailure`: the crack event is a
  demand event.
- `Reliability.axialDemand_eq` and `Reliability.axialBar_failure_iff`:
  the axial bar with a calibrated yield functional fails exactly when
  `2 A_cs A ≤ |q| L`.
- `Reliability.shaftStresses_eq`, `Reliability.shaftDemand_eq`: the
  outer-fiber stresses of a solid circular shaft and its demand through a
  supplied functional calibrated on bending-torsion states
  (`Reliability.BendingTorsionCalibrated`).
- `Reliability.shaftDemand_le_iff`, `Reliability.not_demandFailure_iff`,
  `Reliability.shaftMinDiameter_pos`: the sizing inequality
  `shaftMinDiameter c M T A ≤ d` and the minimum diameter.
- `Reliability.zero_diameter_misreports`,
  `Reliability.stressConcentration_exceeds_at_minDiameter`: the zero
  diameter and an unsupported stress concentration are not covered.

## iii. Table of contents

- A. Mode-I stress intensity and the critical crack length
- B. Paris-law crack growth to the critical length
- C. Demand, allowable and margin
- D. An axial load path with a supplied yield functional
- E. A solid circular shaft under bending and torsion
- F. Shaft sizing: boundary examples

## iv. References

- N. E. Dowling, *Mechanical Behavior of Materials: Engineering Methods
  for Deformation, Fracture, and Fatigue*, 4th ed., Pearson (2013): the
  mode-I stress intensity model and the critical-crack condition
  `K_I = K_IC` used here, and the Paris fatigue-crack-growth law
  `da/dN = C * (ΔK)^m` reduced in section B; yield criteria calibrated
  by the uniaxial test and safety factors against yielding (sections C
  and D).
- S. Timoshenko and J. M. Gere, *Mechanics of Materials* (axially loaded
  bars).
- R. G. Budynas and J. K. Nisbett, *Shigley's Mechanical Engineering
  Design*, 10th ed., McGraw-Hill (2015): shaft design for stress, with the
  distortion-energy and maximum-shear-stress theories for combined bending
  and torsion (sections E and F).
- J. M. Gere and B. J. Goodno, *Mechanics of Materials*, 8th ed., Cengage
  (2013): the flexure and torsion formulas and the section properties of a
  circle.

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

/-! ## B. Paris-law crack growth

The Paris section uses the reduced one-parameter form of the standard
Paris law. The standard law is `da/dN = C * (ΔK)^m` with stress-intensity
range `ΔK = Y * Δσ * √(π * a)` for a constant geometry factor `Y` and
fatigue stress range `Δσ`. Substituting gives
`da/dN = K * a ^ (m / 2)` with the single aggregate coefficient
`K = C * (Y * Δσ * √π) ^ m > 0`, which is the `K` of this section; it is
an aggregate growth coefficient, not a stress intensity (`K_I`, `K_IC`
in section A). The reduction assumes constant `Y` and `Δσ` and the
small-scale-yielding LEFM regime; no load spectrum, crack closure, or
empirical calibration is modeled. -/

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

/-! ## C. Demand, allowable and margin -/

/-- The dimensional margin `A - s` of a demand `s` against an allowable `A`, in the unit of the
demand. -/
def dimensionalMargin (A s : ℝ) : ℝ := A - s

/-- The equality-inclusive failure event: the demand `s` reaches the allowable `A`. -/
def demandFailure (A s : ℝ) : Prop := A ≤ s

/-- The margin of safety `A / s - 1`, defined only for a positive demand `s`. -/
noncomputable def marginOfSafety (A s : ℝ) (_hs : 0 < s) : ℝ := A / s - 1

/-- Failure is a nonpositive dimensional margin. -/
lemma demandFailure_iff_dimensionalMargin_nonpos (A s : ℝ) :
    demandFailure A s ↔ dimensionalMargin A s ≤ 0 := by
  unfold demandFailure dimensionalMargin
  constructor <;> intro h <;> linarith

/-- Equality is failure, with zero margin. -/
lemma demandFailure_self (A : ℝ) : demandFailure A A ∧ dimensionalMargin A A = 0 := by
  unfold demandFailure dimensionalMargin
  exact ⟨le_refl A, sub_self A⟩

/-- For a positive demand, `A - s = s * (A / s - 1)`. -/
lemma dimensionalMargin_eq_mul_marginOfSafety {A s : ℝ} (hs : 0 < s) :
    dimensionalMargin A s = s * marginOfSafety A s hs := by
  unfold dimensionalMargin marginOfSafety
  rw [mul_sub, mul_div_cancel₀ _ hs.ne', mul_one]

/-- For a positive demand, the margin of safety has the sign of the dimensional margin. -/
lemma sign_marginOfSafety {A s : ℝ} (hs : 0 < s) :
    SignType.sign (marginOfSafety A s hs) = SignType.sign (dimensionalMargin A s) := by
  rw [dimensionalMargin_eq_mul_marginOfSafety hs, sign_mul, sign_pos hs, one_mul]

/-- For a positive demand, failure is a nonpositive margin of safety. -/
lemma demandFailure_iff_marginOfSafety_nonpos {A s : ℝ} (hs : 0 < s) :
    demandFailure A s ↔ marginOfSafety A s hs ≤ 0 := by
  rw [demandFailure_iff_dimensionalMargin_nonpos, dimensionalMargin_eq_mul_marginOfSafety hs]
  constructor
  · intro h
    by_contra h'
    linarith [mul_pos hs (not_le.mp h')]
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hs.le h

/-- A change of the stress unit by a factor `c > 0` rescales the dimensional margin by `c` and
changes neither the failure event nor the margin of safety. -/
lemma margin_unit_change {c A s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    dimensionalMargin (c * A) (c * s) = c * dimensionalMargin A s ∧
      (demandFailure (c * A) (c * s) ↔ demandFailure A s) ∧
      marginOfSafety (c * A) (c * s) (mul_pos hc hs) = marginOfSafety A s hs := by
  unfold dimensionalMargin demandFailure marginOfSafety
  refine ⟨by ring,
    ⟨fun h => le_of_mul_le_mul_left h hc, fun h => mul_le_mul_of_nonneg_left h hc.le⟩, ?_⟩
  rw [mul_div_mul_left _ _ hc.ne']

/-- At zero demand the dimensional margin is the allowable, and there is no failure. -/
lemma dimensionalMargin_zero_demand {A : ℝ} (hA : 0 < A) :
    dimensionalMargin A 0 = A ∧ ¬ demandFailure A 0 := by
  unfold dimensionalMargin demandFailure
  exact ⟨sub_zero A, fun h => absurd h (not_le.mpr hA)⟩

/-- The ratio formula must not be used at zero demand: Lean's `A / 0 = 0` makes `A / 0 - 1`
negative, a false failure signal, while the demand `0` does not fail. -/
lemma ratio_at_zero_demand_misreports {A : ℝ} (hA : 0 < A) :
    A / 0 - 1 < 0 ∧ ¬ demandFailure A 0 := by
  unfold demandFailure
  refine ⟨?_, fun h => absurd h (not_le.mpr hA)⟩
  rw [div_zero]
  norm_num

/-- The mode-I crack event is the demand event with demand `K_I` and allowable `K_IC`. -/
lemma crackFailure_iff_demandFailure (KIC Y σ a : ℝ) :
    crackFailure KIC Y σ a ↔ demandFailure KIC (modeIStressIntensity Y σ a) := by
  rfl

/-! ## D. An axial load path with a supplied yield functional -/

/-- A supplied yield functional on stress matrices (tension positive) is calibrated by the
tensile test when it returns `|σ|` on every uniaxial state `diag(σ, 0, 0)`. -/
def UniaxialCalibrated (Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ) : Prop :=
  ∀ σ : ℝ, Φ (Matrix.diagonal ![σ, 0, 0]) = |σ|

/-- The axial normal stress `EA u'(x) / A_cs` at the section `x` of cross-section area `A_cs` for
the closed-form uniform-load displacement `u = axialDisplacement EA L q`, which for `0 < L` and
`0 < EA` solves the fixed-fixed bar problem (`isFixedFixedSolution_axialDisplacement`). -/
noncomputable def axialStress (EA L q Acs x : ℝ) : ℝ :=
  EA * deriv (Elasticity.PrismaticMembers.axialDisplacement EA L q) x / Acs

/-- For positive axial rigidity and cross-section area, the axial stress of the closed-form
uniform-load displacement is `q (L - 2 x) / (2 A_cs)`; for `0 < L` this is the stress of the
fixed-fixed bar. -/
lemma axialStress_eq {EA Acs : ℝ} (hEA : 0 < EA) (hAcs : 0 < Acs) (L q x : ℝ) :
    axialStress EA L q Acs x = q * (L - 2 * x) / (2 * Acs) := by
  have hEA' : EA ≠ 0 := hEA.ne'
  have hAcs' : Acs ≠ 0 := hAcs.ne'
  have hd : deriv (Elasticity.PrismaticMembers.axialDisplacement EA L q) x =
      q * (L - 2 * x) / (2 * EA) := by
    have h : HasDerivAt (Elasticity.PrismaticMembers.axialDisplacement EA L q)
        (q * (L - 2 * x) / (2 * EA)) x := by
      have h1 := (((hasDerivAt_id x).const_mul q).mul ((hasDerivAt_id x).const_sub L)).div_const
        (2 * EA)
      have he : Elasticity.PrismaticMembers.axialDisplacement EA L q =
          fun y => q * id y * (L - id y) / (2 * EA) := by
        funext y
        simp [Elasticity.PrismaticMembers.axialDisplacement]
      rw [he]
      convert h1 using 1
      simp only [id]
      ring
    exact h.deriv
  unfold axialStress
  rw [hd]
  field_simp

/-- Through a calibrated yield functional, the demand at the section `x` is
`|q (L - 2 x)| / (2 A_cs)`, for positive axial rigidity and cross-section area. -/
lemma axialDemand_eq {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} (hΦ : UniaxialCalibrated Φ)
    {EA Acs : ℝ} (hEA : 0 < EA) (hAcs : 0 < Acs) (L q x : ℝ) :
    Φ (Matrix.diagonal ![axialStress EA L q Acs x, 0, 0]) = |q * (L - 2 * x)| / (2 * Acs) := by
  unfold UniaxialCalibrated at hΦ
  rw [hΦ, axialStress_eq hEA hAcs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Acs)]

/-- The fixed-fixed bar (`0 < L`, `0 < EA`, `0 < A_cs`) fails at some section of `[0, L]` exactly
when the end-section demand reaches the allowable: `2 A_cs A ≤ |q| L`. -/
lemma axialBar_failure_iff {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} (hΦ : UniaxialCalibrated Φ)
    {EA Acs L : ℝ} (hEA : 0 < EA) (hAcs : 0 < Acs) (hL : 0 < L) (q A : ℝ) :
    (∃ x ∈ Set.Icc 0 L, demandFailure A (Φ (Matrix.diagonal ![axialStress EA L q Acs x, 0, 0]))) ↔
      2 * Acs * A ≤ |q| * L := by
  simp only [axialDemand_eq hΦ hEA hAcs, demandFailure]
  have h2 : (0 : ℝ) < 2 * Acs := by positivity
  constructor
  · rintro ⟨x, ⟨hx0, hxL⟩, h⟩
    rw [le_div_iff₀ h2] at h
    have hb : |q * (L - 2 * x)| ≤ |q| * L := by
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
      rw [abs_le]
      constructor <;> linarith
    linarith
  · intro h
    refine ⟨0, ⟨le_refl 0, hL.le⟩, ?_⟩
    rw [le_div_iff₀ h2, abs_mul, mul_zero, sub_zero, abs_of_pos hL]
    linarith

/-! ## E. A solid circular shaft under bending and torsion -/

/-- Second moment of area of a solid circular section of diameter `d` about a diameter:
`I = π d ⁴ / 64`. -/
noncomputable def circleSecondMoment (d : ℝ) : ℝ := Real.pi * d ^ 4 / 64

/-- Polar second moment of area of a solid circular section of diameter `d`: `J = π d ⁴ / 32`. -/
noncomputable def circlePolarMoment (d : ℝ) : ℝ := Real.pi * d ^ 4 / 32

/-- Flexure formula at the outer fiber `y = d / 2` of a solid circular shaft under the bending
moment `M`: `σ = M (d / 2) / I`, tension positive on the fiber that `M` stretches. -/
noncomputable def shaftBendingStress (M d : ℝ) : ℝ := M * (d / 2) / circleSecondMoment d

/-- Torsion formula at the surface `r = d / 2` of a solid circular shaft under the torque `T`:
`τ = T (d / 2) / J`. -/
noncomputable def shaftShearStress (T d : ℝ) : ℝ := T * (d / 2) / circlePolarMoment d

/-- For a nonzero diameter the two formulas are `σ = 32 M / (π d ³)` and `τ = 16 T / (π d ³)`. -/
lemma shaftStresses_eq {d : ℝ} (hd : d ≠ 0) (M T : ℝ) :
    shaftBendingStress M d = 32 * M / (Real.pi * d ^ 3) ∧
      shaftShearStress T d = 16 * T / (Real.pi * d ^ 3) := by
  unfold shaftBendingStress shaftShearStress circleSecondMoment circlePolarMoment
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The stress state at the critical surface point, index `0` along the shaft axis and index `1`
circumferential: axial normal stress `σ` and shear `τ`. -/
def bendingTorsionState (σ τ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![σ, τ, 0; τ, 0, 0; 0, 0, 0]

/-- A supplied yield functional (tension positive) is calibrated on the bending-torsion states
with shear factor `c` when it returns `√(σ ^ 2 + c τ ^ 2)` on every such state: `c = 3` for the
von Mises (distortion-energy) criterion, `c = 4` for the Tresca (maximum-shear) criterion. -/
def BendingTorsionCalibrated (Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ σ τ : ℝ, Φ (bendingTorsionState σ τ) = Real.sqrt (σ ^ 2 + c * τ ^ 2)

/-- The bending-torsion calibration contains the tensile-test calibration: at `τ = 0` the state
is uniaxial and the functional returns `|σ|`. -/
lemma BendingTorsionCalibrated.uniaxialCalibrated {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} {c : ℝ}
    (hΦ : BendingTorsionCalibrated Φ c) : Reliability.UniaxialCalibrated Φ := by
  intro σ
  have h : Matrix.diagonal ![σ, 0, 0] = bendingTorsionState σ 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bendingTorsionState]
  rw [h, hΦ]
  simp [Real.sqrt_sq_eq_abs]

/-- The demand at the critical point of a shaft of diameter `d > 0` under `M` and `T`:
`16 √(4 M ^ 2 + c T ^ 2) / (π d ³)`. -/
lemma shaftDemand_eq {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} {c : ℝ}
    (hΦ : BendingTorsionCalibrated Φ c) {d : ℝ} (hd : 0 < d) (M T : ℝ) :
    Φ (bendingTorsionState (shaftBendingStress M d) (shaftShearStress T d)) =
      16 * Real.sqrt (4 * M ^ 2 + c * T ^ 2) / (Real.pi * d ^ 3) := by
  rw [hΦ, (shaftStresses_eq hd.ne' M T).1, (shaftStresses_eq hd.ne' M T).2]
  have hπ : 0 < Real.pi := Real.pi_pos
  have hD : 0 < Real.pi * d ^ 3 := by positivity
  have key : (32 * M / (Real.pi * d ^ 3)) ^ 2 + c * (16 * T / (Real.pi * d ^ 3)) ^ 2 =
      (16 / (Real.pi * d ^ 3)) ^ 2 * (4 * M ^ 2 + c * T ^ 2) := by
    field_simp
    ring
  rw [key, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  field_simp

/-- Minimum diameter for the allowable `A`: `(16 √(4 M ^ 2 + c T ^ 2) / (π A)) ^ (1 / 3)`. -/
noncomputable def shaftMinDiameter (c M T A : ℝ) : ℝ :=
  (16 * Real.sqrt (4 * M ^ 2 + c * T ^ 2) / (Real.pi * A)) ^ (1 / 3 : ℝ)

/-- The sizing inequality: for `d > 0` and a positive allowable `A`, the demand stays within `A`
exactly when `d` is at least the minimum diameter. -/
lemma shaftDemand_le_iff {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} {c : ℝ}
    (hΦ : BendingTorsionCalibrated Φ c) {d A : ℝ} (hd : 0 < d) (hA : 0 < A) (M T : ℝ) :
    Φ (bendingTorsionState (shaftBendingStress M d) (shaftShearStress T d)) ≤ A ↔
      shaftMinDiameter c M T A ≤ d := by
  rw [shaftDemand_eq hΦ hd M T]
  unfold shaftMinDiameter
  have hπ : 0 < Real.pi := Real.pi_pos
  have hD : 0 < Real.pi * d ^ 3 := by positivity
  have hπA : 0 < Real.pi * A := by positivity
  have hS : 0 ≤ Real.sqrt (4 * M ^ 2 + c * T ^ 2) := Real.sqrt_nonneg _
  rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_le_iff_of_pos (by positivity) hd.le (by norm_num),
    show d ^ (3 : ℝ) = d ^ 3 from by exact_mod_cast Real.rpow_natCast d 3,
    div_le_iff₀ hD, div_le_iff₀ hπA]
  constructor <;> intro h <;> linarith

/-- With the equality-inclusive failure event, the shaft does not fail exactly when `d` exceeds
the minimum diameter. -/
lemma not_demandFailure_iff {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} {c : ℝ}
    (hΦ : BendingTorsionCalibrated Φ c) {d A : ℝ} (hd : 0 < d) (hA : 0 < A) (M T : ℝ) :
    ¬ Reliability.demandFailure A
        (Φ (bendingTorsionState (shaftBendingStress M d) (shaftShearStress T d))) ↔
      shaftMinDiameter c M T A < d := by
  unfold Reliability.demandFailure
  rw [not_le, shaftDemand_eq hΦ hd M T]
  unfold shaftMinDiameter
  have hπ : 0 < Real.pi := Real.pi_pos
  have hD : 0 < Real.pi * d ^ 3 := by positivity
  have hπA : 0 < Real.pi * A := by positivity
  have hS : 0 ≤ Real.sqrt (4 * M ^ 2 + c * T ^ 2) := Real.sqrt_nonneg _
  rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_lt_iff_of_pos (by positivity) hd.le (by norm_num),
    show d ^ (3 : ℝ) = d ^ 3 from by exact_mod_cast Real.rpow_natCast d 3,
    div_lt_iff₀ hD, div_lt_iff₀ hπA]
  constructor <;> intro h <;> linarith

/-- For a nonzero load, a positive shear factor and a positive allowable the minimum diameter is
positive, so a zero diameter never meets the sizing inequality. -/
lemma shaftMinDiameter_pos {c M T A : ℝ} (hc : 0 < c) (hA : 0 < A) (hMT : M ≠ 0 ∨ T ≠ 0) :
    0 < shaftMinDiameter c M T A := by
  unfold shaftMinDiameter
  apply Real.rpow_pos_of_pos
  have h4 : 0 < 4 * M ^ 2 + c * T ^ 2 := by
    rcases hMT with h | h
    · have : 0 < M ^ 2 := by positivity
      nlinarith [sq_nonneg T]
    · have : 0 < T ^ 2 := by positivity
      nlinarith [sq_nonneg M]
  have := Real.sqrt_pos.mpr h4
  have := Real.pi_pos
  positivity

/-! ## F. Shaft sizing: boundary examples -/

/-- The zero diameter is rejected, not covered: at `d = 0` Lean's `x / 0 = 0` makes both stress
formulas vanish, so every calibrated functional reports zero demand and no failure for every
load. The hypothesis `0 < d` of the sizing results cannot be dropped. -/
lemma zero_diameter_misreports {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} {c : ℝ}
    (hΦ : BendingTorsionCalibrated Φ c) {A : ℝ} (hA : 0 < A) (M T : ℝ) :
    Φ (bendingTorsionState (shaftBendingStress M 0) (shaftShearStress T 0)) = 0 ∧
      ¬ Reliability.demandFailure A
        (Φ (bendingTorsionState (shaftBendingStress M 0) (shaftShearStress T 0))) := by
  have h0 : shaftBendingStress M 0 = 0 ∧ shaftShearStress T 0 = 0 := by
    simp [shaftBendingStress, shaftShearStress, circleSecondMoment, circlePolarMoment]
  rw [h0.1, h0.2, hΦ]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    Real.sqrt_zero, Reliability.demandFailure, not_le, true_and]
  exact hA

/-- An unsupported stress-concentration assumption is rejected: at the nominal minimum diameter
the nominal demand equals the allowable, and a bending stress-concentration factor `K > 1`
(with `M ≠ 0`) raises the demand strictly above it. The nominal sizing inequality covers a plain
shaft only; a notch or shoulder needs its factor as a supplied input. -/
lemma stressConcentration_exceeds_at_minDiameter {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} {c : ℝ}
    (hΦ : BendingTorsionCalibrated Φ c) (hc : 0 ≤ c) {M A K : ℝ} (hM : M ≠ 0) (hA : 0 < A)
    (hK : 1 < K) (T : ℝ) :
    Φ (bendingTorsionState (shaftBendingStress M (shaftMinDiameter c M T A))
        (shaftShearStress T (shaftMinDiameter c M T A))) = A ∧
      A < Φ (bendingTorsionState (K * shaftBendingStress M (shaftMinDiameter c M T A))
        (shaftShearStress T (shaftMinDiameter c M T A))) := by
  set dm := shaftMinDiameter c M T A with hdm
  have hπ : 0 < Real.pi := Real.pi_pos
  have hM2 : 0 < M ^ 2 := by positivity
  have hS : 0 < 4 * M ^ 2 + c * T ^ 2 := by nlinarith [sq_nonneg T]
  have hsq : 0 < Real.sqrt (4 * M ^ 2 + c * T ^ 2) := Real.sqrt_pos.mpr hS
  have hbase : 0 < 16 * Real.sqrt (4 * M ^ 2 + c * T ^ 2) / (Real.pi * A) := by positivity
  have hdm_pos : 0 < dm := Real.rpow_pos_of_pos hbase _
  have hcube : dm ^ 3 = 16 * Real.sqrt (4 * M ^ 2 + c * T ^ 2) / (Real.pi * A) := by
    rw [hdm]
    unfold shaftMinDiameter
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  have hnom : Φ (bendingTorsionState (shaftBendingStress M dm) (shaftShearStress T dm)) = A := by
    rw [shaftDemand_eq hΦ hdm_pos M T, hcube]
    field_simp
  refine ⟨hnom, ?_⟩
  have hA' := hnom
  rw [hΦ] at hA'
  rw [hΦ, ← hA']
  have hσ : shaftBendingStress M dm ≠ 0 := by
    rw [(shaftStresses_eq hdm_pos.ne' M T).1]
    have : 0 < Real.pi * dm ^ 3 := by positivity
    exact div_ne_zero (mul_ne_zero (by norm_num) hM) this.ne'
  have hσ2 : 0 < shaftBendingStress M dm ^ 2 := by positivity
  have hK2 : 1 < K ^ 2 := by nlinarith
  apply Real.sqrt_lt_sqrt (by positivity)
  have : shaftBendingStress M dm ^ 2 < (K * shaftBendingStress M dm) ^ 2 := by
    rw [mul_pow]
    nlinarith
  linarith

end Reliability
