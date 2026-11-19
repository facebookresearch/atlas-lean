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
public import Mathlib.Probability.Process.HittingTime
public import MathlibExt.Probability.Reliability.SystemLifetime
public import PhyslibExt.Elasticity.PrismaticMembers

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Physical failure events: LEFM crack failure, demand margins, lifetimes and shaft sizing

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

A component whose damage `d ω t` grows along a continuous nondecreasing
path in time `t : ℝ≥0` fails when the damage reaches its threshold
`D ω`, equality included: the hit condition `d ω t - D ω ∈ Ici 0` is
the demand event above. Its lifetime is the hitting time
`MeasureTheory.hittingAfter` of `d - D` into `Ici 0` from time zero, a
value in `ℝ≥0∞`: `⊤` when the threshold is never reached, `0` when the
component is failed at time zero. The hit set is closed and upward
closed, so the infimum is attained and the component is up at a finite
time `t` exactly when `d ω t < D ω`; this uses closedness, not the
`WellFoundedLT` lemmas of the hitting-time API, which do not apply to
real time. Through these level sets, measurable fixed-time damage and
threshold maps give measurable lifetimes, and the lifetime of the
monotone Boolean system of
`MathlibExt.Probability.Reliability.SystemLifetime` is up at `t`
exactly when the configuration of components still below threshold
lies in the increasing system event. An increasing event is a monotone
system, not necessarily a coherent one: the constant events `∅` and
`univ` and systems with irrelevant components are included. No
independence between components is assumed, no damage law is derived,
and no stopping theorem in continuous time is claimed.

The Paris crack of section B, of initial length `0 < a0 < a_c`, becomes
a damage path in time under a constant load frequency `f ≥ 0` (cycles
per unit time): the event path `d t = a (min (f t) Nf)` follows the
crack after `f t` cycles up to the Paris life `Nf` and stays at
`a Nf = a_c` afterwards (`saturatedCrackPath`). The part after failure
is an event model, not continued crack growth, and the event path never
evaluates the power-branch solution at or beyond its blow-up. The event
path is continuous and nondecreasing, so the hitting time of section E
applies: for `f > 0` the lifetime against `a_c` is `Nf / f`; for `f = 0`
the event path is the constant `a0` and the lifetime is `⊤`; a crack
that starts at or above `a_c` is the initially failed constant event
path, with lifetime `0`, and no growth law is used for it. Before
failure the crack in time solves the Paris law at `f` cycles per unit
time, and for `m > 2` the failure time `Nf / f` is strictly before the
blow-up time.

A solid circular shaft of diameter `d > 0` under a declared bending
moment `M` and torque `T` has, by the flexure and torsion formulas with
`I = π d ⁴ / 64` and `J = π d ⁴ / 32`, the outer-fiber stresses
`σ = 32 M / (π d ³)` and `τ = 16 T / (π d ³)` at the critical surface
point, whose stress state carries only the axial normal stress `σ` and the
axial-circumferential shear `τ`. A supplied functional calibrated on these
bending-torsion states with a positive shear factor `c` (it returns
`√(σ ^ 2 + c τ ^ 2)` there: `c = 3` for von Mises, `c = 4` for Tresca) is
in particular calibrated by the tensile test, and turns them into the
demand `16 √(4 M ^ 2 + c T ^ 2) / (π d ³)`. The factor must be positive:
for `c ≤ 0` the square root would give a pure torque zero demand, and the
sizing results would accept every diameter. Against a positive allowable
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
- `Reliability.damageLifetime`, `Reliability.isClosed_damageHitSet`
  and `Reliability.isUpperSet_damageHitSet`: the hitting-time lifetime
  and its closed, upward-closed hit set.
- `Reliability.lt_damageLifetime_iff` and
  `Reliability.damageLifetime_le_iff`: up exactly below threshold;
  failure, equality included, exactly by time `t`.
- `Reliability.damageLifetime_eq_top_iff` and
  `Reliability.damageLifetime_eq_zero`: never hit, initially failed.
- `Reliability.measurable_damageLifetime`,
  `Reliability.lt_systemLifetime_damage_iff` and
  `Reliability.measurable_systemLifetime_damage`: measurable lifetimes
  and the monotone-system event.
- `Reliability.saturatedCrackPath`: the saturated crack event path.
- `Reliability.continuous_monotone_saturatedCrackPath_pow` and
  `Reliability.continuous_monotone_saturatedCrackPath_exp`: the event
  path is continuous and nondecreasing.
- `Reliability.hasDerivAt_parisCrackPow_time` and
  `Reliability.hasDerivAt_parisCrackExp_time`: before failure, the
  crack in time solves the Paris law at `f` cycles per unit time.
- `Reliability.damageLifetime_saturatedCrackPath_pow` and
  `Reliability.damageLifetime_saturatedCrackPath_exp`: the lifetime is
  `Nf / f` for `f > 0`.
- `Reliability.damageLifetime_saturatedCrackPath_pow_zero`,
  `Reliability.damageLifetime_saturatedCrackPath_exp_zero` and
  `Reliability.damageLifetime_initiallyFailed`: no load gives `⊤`, an
  initially failed crack `0`.
- `Reliability.saturatedCrackPath_pow_base_pos` and
  `Reliability.failureTime_lt_blowupTime`: the event path stays on the
  power-branch domain and fails before blow-up.
- `Reliability.shaftStresses_eq`, `Reliability.shaftDemand_eq`: the
  outer-fiber stresses of a solid circular shaft and its demand through a
  supplied functional calibrated on bending-torsion states with a positive
  shear factor (`Reliability.BendingTorsionCalibrated`).
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
- E. Damage hitting times
- F. Measurability and monotone systems
- G. The saturated crack event path
- H. The Paris lifetime: power branch
- I. The Paris lifetime: logarithmic branch and initial failure
- J. A solid circular shaft under bending and torsion
- K. Shaft sizing: boundary examples

## iv. References

- N. E. Dowling, *Mechanical Behavior of Materials: Engineering Methods
  for Deformation, Fracture, and Fatigue*, 4th ed., Pearson (2013): the
  mode-I stress intensity model and the critical-crack condition
  `K_I = K_IC` used here, and the Paris fatigue-crack-growth law
  `da/dN = C * (ΔK)^m` reduced in section B, with its life in time at a
  constant load frequency (sections G to I); yield criteria calibrated
  by the uniaxial test and safety factors against yielding (sections C
  and D).
- S. Timoshenko and J. M. Gere, *Mechanics of Materials* (axially loaded
  bars).
- R. E. Barlow and F. Proschan, *Statistical Theory of Reliability and
  Life Testing*, Holt, Rinehart and Winston (1975): structure functions
  and system lifetimes (section F, for monotone systems; coherent
  systems are the monotone systems in which every component is
  relevant).
- W. Q. Meeker and L. A. Escobar, *Statistical Methods for Reliability
  Data*, Wiley (1998), degradation chapters: failure when a degradation
  path reaches a threshold (sections E and G to I).
- R. G. Budynas and J. K. Nisbett, *Shigley's Mechanical Engineering
  Design*, 10th ed., McGraw-Hill (2015): shaft design for stress, with the
  distortion-energy and maximum-shear-stress theories for combined bending
  and torsion (sections J and K).
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

/-! ## E. Damage hitting times -/

open MeasureTheory
open scoped NNReal ENNReal

/-- The lifetime of a component with damage path `d ω` and threshold `D ω`: the hitting time of
`d - D` into `Ici 0` from time zero, `⊤` when the threshold is never reached. -/
noncomputable def damageLifetime {Ω : Type*} (d : Ω → ℝ≥0 → ℝ) (D : Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  hittingAfter (fun t ω => d ω t - D ω) (Set.Ici 0) 0 ω

variable {Ω : Type*}

open scoped Classical in
private lemma damageLifetime_eq_ite (d : Ω → ℝ≥0 → ℝ) (D : Ω → ℝ) (ω : Ω) :
    damageLifetime d D ω = if ∃ j : ℝ≥0, 0 ≤ j ∧ d ω j - D ω ∈ Set.Ici (0 : ℝ)
      then ((sInf {i : ℝ≥0 | 0 ≤ i ∧ d ω i - D ω ∈ Set.Ici (0 : ℝ)} : ℝ≥0) : ℝ≥0∞) else ⊤ :=
  rfl

/-- The hit condition is the equality-inclusive demand event: `d - D ∈ Ici 0` iff
`demandFailure D d`. -/
lemma mem_damageHitSet_iff (d : Ω → ℝ≥0 → ℝ) (D : Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    d ω t - D ω ∈ Set.Ici (0 : ℝ) ↔ demandFailure (D ω) (d ω t) := by
  rw [Set.mem_Ici, sub_nonneg]
  rfl

/-- For a continuous damage path the hit set is closed. -/
lemma isClosed_damageHitSet {d : Ω → ℝ≥0 → ℝ} {D : Ω → ℝ} {ω : Ω} (hcont : Continuous (d ω)) :
    IsClosed {t : ℝ≥0 | d ω t - D ω ∈ Set.Ici (0 : ℝ)} := by
  exact isClosed_Ici.preimage (hcont.sub continuous_const)

/-- For a nondecreasing damage path the hit set is upward closed. -/
lemma isUpperSet_damageHitSet {d : Ω → ℝ≥0 → ℝ} {D : Ω → ℝ} {ω : Ω} (hmono : Monotone (d ω)) :
    IsUpperSet {t : ℝ≥0 | d ω t - D ω ∈ Set.Ici (0 : ℝ)} := by
  intro a b hab ha
  simp only [Set.mem_ofPred_eq, Set.mem_Ici, sub_nonneg] at ha ⊢
  exact ha.trans (hmono hab)

/-- For a continuous nondecreasing damage path, the component is up at a finite time `t` exactly
when its damage is still below the threshold. -/
lemma lt_damageLifetime_iff {d : Ω → ℝ≥0 → ℝ} {D : Ω → ℝ} {ω : Ω} (hcont : Continuous (d ω))
    (hmono : Monotone (d ω)) (t : ℝ≥0) :
    (t : ℝ≥0∞) < damageLifetime d D ω ↔ d ω t < D ω := by
  constructor
  · intro h
    have hn := notMem_of_lt_hittingAfter (u := fun t ω => d ω t - D ω) (s := Set.Ici (0 : ℝ))
      (n := 0) (ω := ω) (k := t) h (zero_le : (0 : ℝ≥0) ≤ t)
    simp only [Set.mem_Ici, sub_nonneg, not_le] at hn
    exact hn
  · intro h
    rw [damageLifetime_eq_ite]
    split_ifs with hex
    · rw [ENNReal.coe_lt_coe]
      set S := {i : ℝ≥0 | 0 ≤ i ∧ d ω i - D ω ∈ Set.Ici (0 : ℝ)} with hS
      have hSeq : S = {i : ℝ≥0 | d ω i - D ω ∈ Set.Ici (0 : ℝ)} := by
        ext i
        simp only [hS, Set.mem_ofPred_eq, zero_le, true_and]
      have hne : S.Nonempty := by
        obtain ⟨j, hj⟩ := hex
        exact ⟨j, hj⟩
      have hcl : IsClosed S := by
        rw [hSeq]
        exact isClosed_damageHitSet hcont
      have hmem : sInf S ∈ S := hcl.csInf_mem hne (OrderBot.bddBelow S)
      by_contra hle
      rw [not_lt] at hle
      have hmem' : d ω (sInf S) - D ω ∈ Set.Ici (0 : ℝ) := hmem.2
      have ht : d ω t - D ω ∈ Set.Ici (0 : ℝ) := isUpperSet_damageHitSet hmono hle hmem'
      simp only [Set.mem_Ici, sub_nonneg] at ht
      linarith
    · exact ENNReal.coe_lt_top

/-- Equality at the threshold is failure: for a continuous nondecreasing damage path the
lifetime is at most `t` exactly when the demand event holds at `t`. -/
lemma damageLifetime_le_iff {d : Ω → ℝ≥0 → ℝ} {D : Ω → ℝ} {ω : Ω} (hcont : Continuous (d ω))
    (hmono : Monotone (d ω)) (t : ℝ≥0) :
    damageLifetime d D ω ≤ t ↔ demandFailure (D ω) (d ω t) := by
  rw [← not_lt, lt_damageLifetime_iff hcont hmono, not_lt]
  rfl

/-- The lifetime is `⊤` exactly when the damage stays below the threshold at every time. -/
lemma damageLifetime_eq_top_iff (d : Ω → ℝ≥0 → ℝ) (D : Ω → ℝ) (ω : Ω) :
    damageLifetime d D ω = ⊤ ↔ ∀ t, d ω t < D ω := by
  rw [damageLifetime_eq_ite]
  split_ifs with hex
  · simp only [ENNReal.coe_ne_top, false_iff, not_forall, not_lt]
    obtain ⟨j, -, hj⟩ := hex
    exact ⟨j, by simpa only [Set.mem_Ici, sub_nonneg] using hj⟩
  · simp only [true_iff]
    intro t
    by_contra hc
    rw [not_lt] at hc
    exact hex ⟨t, (zero_le : (0 : ℝ≥0) ≤ t), by simpa only [Set.mem_Ici, sub_nonneg] using hc⟩

/-- A component that is failed at time zero has lifetime `0`. -/
lemma damageLifetime_eq_zero {d : Ω → ℝ≥0 → ℝ} {D : Ω → ℝ} {ω : Ω} (h0 : D ω ≤ d ω 0) :
    damageLifetime d D ω = 0 := by
  have hmem0 : (0 : ℝ≥0) ≤ 0 ∧ d ω 0 - D ω ∈ Set.Ici (0 : ℝ) :=
    ⟨le_rfl, by simpa only [Set.mem_Ici, sub_nonneg] using h0⟩
  have hinf : sInf {i : ℝ≥0 | 0 ≤ i ∧ d ω i - D ω ∈ Set.Ici (0 : ℝ)} = 0 :=
    le_antisymm (csInf_le (OrderBot.bddBelow _) hmem0) zero_le
  rw [damageLifetime_eq_ite]
  split_ifs with hex
  · rw [hinf, ENNReal.coe_zero]
  · exact absurd ⟨0, hmem0⟩ hex

/-! ## F. Measurability and monotone systems -/

/-- With measurable fixed-time damage maps, a measurable threshold and continuous nondecreasing
paths, the lifetime is measurable: its level sets `{ω | t < lifetime ω}` are
`{ω | d ω t < D ω}`. -/
lemma measurable_damageLifetime [MeasurableSpace Ω] {d : Ω → ℝ≥0 → ℝ} {D : Ω → ℝ}
    (hmeas : ∀ t, Measurable fun ω => d ω t) (hD : Measurable D)
    (hcont : ∀ ω, Continuous (d ω)) (hmono : ∀ ω, Monotone (d ω)) :
    Measurable (damageLifetime d D) := by
  refine measurable_of_Ioi fun x => ?_
  cases x with
  | top => simp
  | coe t =>
    have hset : damageLifetime d D ⁻¹' Set.Ioi (t : ℝ≥0∞) = {ω | d ω t < D ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_ofPred_eq]
      exact lt_damageLifetime_iff (hcont ω) (hmono ω) t
    rw [hset]
    exact measurableSet_lt (hmeas t) hD

/-- The monotone-system event: for an increasing event `A` (a monotone system, not necessarily
coherent), the system with the damage lifetimes is up at a finite time `t` exactly when the
configuration of components whose damage is still below threshold at `t` lies in `A`. -/
lemma lt_systemLifetime_damage_iff {E : Type*} [Fintype E] (A : Set (StatMech.ConfigSpace E))
    (hA : StatMech.IsIncreasing A) {d : E → Ω → ℝ≥0 → ℝ} {D : E → Ω → ℝ}
    (hcont : ∀ i ω, Continuous (d i ω)) (hmono : ∀ i ω, Monotone (d i ω)) (ω : Ω) (t : ℝ≥0) :
    (t : ℝ≥0∞) < systemLifetime E A (fun i => damageLifetime (d i) (D i) ω) ↔
      (fun i => decide (d i ω t < D i ω)) ∈ A := by
  rw [lt_systemLifetime_iff E A _ t hA]
  have hcfg : upConfig E (fun i => damageLifetime (d i) (D i) ω) t =
      fun i => decide (d i ω t < D i ω) := by
    funext i
    rw [Bool.eq_iff_iff, upConfig_apply_eq_true, decide_eq_true_iff]
    exact lt_damageLifetime_iff (hcont i ω) (hmono i ω) t
  rw [hcfg]

/-- The system lifetime with the damage lifetimes is measurable. -/
lemma measurable_systemLifetime_damage [MeasurableSpace Ω] {E : Type*} [Fintype E]
    (A : Set (StatMech.ConfigSpace E)) {d : E → Ω → ℝ≥0 → ℝ} {D : E → Ω → ℝ}
    (hmeas : ∀ i t, Measurable fun ω => d i ω t) (hD : ∀ i, Measurable (D i))
    (hcont : ∀ i ω, Continuous (d i ω)) (hmono : ∀ i ω, Monotone (d i ω)) :
    Measurable fun ω => systemLifetime E A (fun i => damageLifetime (d i) (D i) ω) := by
  exact measurable_systemLifetime E A Ω (fun i ω => damageLifetime (d i) (D i) ω)
    (fun i => measurable_damageLifetime (hmeas i) (hD i) (hcont i) (hmono i))

/-! ## G. The saturated crack event path -/

/-- The event path `t ↦ a (min (f t) Nf)` of a crack path `a` (crack length against the cycle
count) under the constant load frequency `f`, at time `t : ℝ≥0`: it is the crack after `f t`
cycles up to `Nf` cycles and stays at `a Nf` afterwards. The part after `Nf` cycles is an event
model, not continued crack growth. -/
noncomputable def saturatedCrackPath (a : ℝ → ℝ) (f Nf : ℝ) (t : ℝ≥0) : ℝ :=
  a (min (f * t) Nf)

/-- Saturation: from the time `Nf / f` on, the event path stays at `a Nf`. -/
lemma saturatedCrackPath_of_le (a : ℝ → ℝ) {f Nf : ℝ} (hf : 0 < f) {t : ℝ≥0}
    (ht : Nf / f ≤ t) : saturatedCrackPath a f Nf t = a Nf := by
  change a (min (f * (t : ℝ)) Nf) = a Nf
  have h : Nf ≤ f * (t : ℝ) := by
    have h1 := (div_le_iff₀ hf).mp ht
    linarith
  rw [min_eq_right h]

private lemma pow_base_pos_of_mem {r K a0 ac N : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < ac) (hr : r ≠ 0) (h0 : 0 ≤ N) (hNf : N ≤ parisLifePow r K a0 ac) :
    0 < a0 ^ r + r * K * N := by
  have hac0 : 0 < ac := lt_trans ha0 hac
  have hrK : r * K ≠ 0 := mul_ne_zero hr (ne_of_gt hK)
  have hbaseNf : a0 ^ r + r * K * parisLifePow r K a0 ac = ac ^ r := by
    change a0 ^ r + r * K * ((ac ^ r - a0 ^ r) / (r * K)) = ac ^ r
    rw [mul_div_cancel₀ _ hrK]
    ring
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · have hs : r * K < 0 := mul_neg_of_neg_of_pos hneg hK
    have hle : r * K * parisLifePow r K a0 ac ≤ r * K * N :=
      mul_le_mul_of_nonpos_left hNf (le_of_lt hs)
    have hpos : 0 < ac ^ r := Real.rpow_pos_of_pos hac0 _
    linarith
  · have hs : 0 < r * K := mul_pos hpos hK
    have hnn : 0 ≤ r * K * N := mul_nonneg (le_of_lt hs) h0
    have hpos : 0 < a0 ^ r := Real.rpow_pos_of_pos ha0 _
    linarith

/-! ## H. The Paris lifetime: power branch -/

/-- **The event path never reaches the singularity.** For `K > 0`, `0 < a0 < a_c` with `a_c` the
critical crack length, `r ≠ 0` and `f ≥ 0`, the base `a0 ^ r + r K N` of the power-branch solution
is positive at every cycle count `N = min (f t) Nf` of the event path, `Nf` the Paris life. -/
lemma saturatedCrackPath_pow_base_pos {r K a0 KIC Y σ f : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < criticalCrackLength KIC Y σ) (hr : r ≠ 0) (hf : 0 ≤ f) (t : ℝ≥0) :
    0 < a0 ^ r + r * K * min (f * t) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)) := by
  have hNf : 0 < parisLifePow r K a0 (criticalCrackLength KIC Y σ) :=
    parisLifePow_pos hK ha0 hac hr
  exact pow_base_pos_of_mem hK ha0 hac hr
    (le_min (mul_nonneg hf t.coe_nonneg) (le_of_lt hNf)) (min_le_right _ _)

/-- **A continuous nondecreasing event path.** Under the hypotheses of
`saturatedCrackPath_pow_base_pos`, the event path of the power-branch crack is continuous and
nondecreasing. -/
lemma continuous_monotone_saturatedCrackPath_pow {r K a0 KIC Y σ f : ℝ} (hK : 0 < K)
    (ha0 : 0 < a0) (hac : a0 < criticalCrackLength KIC Y σ) (hr : r ≠ 0) (hf : 0 ≤ f) :
    Continuous (saturatedCrackPath (parisCrackPow r K a0) f
        (parisLifePow r K a0 (criticalCrackLength KIC Y σ))) ∧
      Monotone (saturatedCrackPath (parisCrackPow r K a0) f
        (parisLifePow r K a0 (criticalCrackLength KIC Y σ))) := by
  have hNf : 0 < parisLifePow r K a0 (criticalCrackLength KIC Y σ) :=
    parisLifePow_pos hK ha0 hac hr
  have hinner_cont : Continuous
      (fun t : ℝ≥0 => min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ))) :=
    (continuous_const.mul NNReal.continuous_coe).min continuous_const
  have hinner_mono : Monotone
      (fun t : ℝ≥0 => min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ))) := by
    intro s t hst
    exact min_le_min (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hst) hf) le_rfl
  have hinner_mem : ∀ t : ℝ≥0, min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ))
      ∈ Set.Icc (0 : ℝ) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)) := by
    intro t
    exact ⟨le_min (mul_nonneg hf t.coe_nonneg) (le_of_lt hNf), min_le_right _ _⟩
  have hbase : ∀ N ∈ Set.Icc (0 : ℝ) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)),
      0 < a0 ^ r + r * K * N := by
    intro N hN
    exact pow_base_pos_of_mem hK ha0 hac hr hN.1 hN.2
  have hcrack_cont : ∀ N ∈ Set.Icc (0 : ℝ) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)),
      ContinuousAt (parisCrackPow r K a0) N := by
    intro N hN
    exact (hasDerivAt_parisCrackPow hr (hbase N hN)).continuousAt
  have hcrack_mono : MonotoneOn (parisCrackPow r K a0)
      (Set.Icc (0 : ℝ) (parisLifePow r K a0 (criticalCrackLength KIC Y σ))) := by
    intro x hx y hy hxy
    change (a0 ^ r + r * K * x) ^ r⁻¹ ≤ (a0 ^ r + r * K * y) ^ r⁻¹
    have hbx := hbase x hx
    have hby := hbase y hy
    rcases lt_or_gt_of_ne hr with hneg | hpos
    · have hs : r * K < 0 := mul_neg_of_neg_of_pos hneg hK
      have hbase_le : a0 ^ r + r * K * y ≤ a0 ^ r + r * K * x := by
        have h := mul_le_mul_of_nonpos_left hxy (le_of_lt hs)
        linarith
      have hexp : r⁻¹ < 0 := inv_lt_zero.mpr hneg
      rcases eq_or_lt_of_le hbase_le with heq | hlt
      · rw [heq]
      · exact le_of_lt (Real.rpow_lt_rpow_of_neg hby hlt hexp)
    · have hs : 0 < r * K := mul_pos hpos hK
      have hbase_le : a0 ^ r + r * K * x ≤ a0 ^ r + r * K * y := by
        have h := mul_le_mul_of_nonneg_left hxy (le_of_lt hs)
        linarith
      have hexp : 0 ≤ r⁻¹ := le_of_lt (inv_pos.mpr hpos)
      exact Real.rpow_le_rpow (le_of_lt hbx) hbase_le hexp
  constructor
  · change Continuous fun t : ℝ≥0 =>
      parisCrackPow r K a0 (min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
    rw [continuous_iff_continuousAt]
    intro t
    have hcomp : ContinuousAt ((parisCrackPow r K a0) ∘
        (fun t : ℝ≥0 => min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))) t :=
      ContinuousAt.comp
        (f := fun t : ℝ≥0 => min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
        (x := t) (g := parisCrackPow r K a0)
        (hcrack_cont _ (hinner_mem t)) hinner_cont.continuousAt
    exact hcomp
  · change Monotone fun t : ℝ≥0 =>
      parisCrackPow r K a0 (min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
    intro s t hst
    exact hcrack_mono (hinner_mem s) (hinner_mem t) (hinner_mono hst)

/-- **Before failure the event path is the crack in real time.** Under the hypotheses of
`saturatedCrackPath_pow_base_pos` with `f > 0`, up to the failure time `Nf / f` the event path is
the crack after `f t` cycles, and `s ↦ a (f s)` solves the Paris law in time,
`da/dt = f K a ^ (1 - r)`, on the solution's domain. -/
lemma hasDerivAt_parisCrackPow_time {r K a0 KIC Y σ f : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < criticalCrackLength KIC Y σ) (hr : r ≠ 0) (hf : 0 < f) {t : ℝ≥0}
    (ht : (t : ℝ) ≤ parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f) :
    saturatedCrackPath (parisCrackPow r K a0) f
        (parisLifePow r K a0 (criticalCrackLength KIC Y σ)) t = parisCrackPow r K a0 (f * t) ∧
      HasDerivAt (fun s : ℝ => parisCrackPow r K a0 (f * s))
        (f * (K * parisCrackPow r K a0 (f * t) ^ (1 - r))) t := by
  have hNf : 0 < parisLifePow r K a0 (criticalCrackLength KIC Y σ) :=
    parisLifePow_pos hK ha0 hac hr
  have hle : f * (t : ℝ) ≤ parisLifePow r K a0 (criticalCrackLength KIC Y σ) := by
    have h1 := (le_div_iff₀ hf).mp ht
    linarith
  have hmin : min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ))
      = f * (t : ℝ) := min_eq_left hle
  have hnn : 0 ≤ f * (t : ℝ) := mul_nonneg (le_of_lt hf) t.coe_nonneg
  have hbase : 0 < a0 ^ r + r * K * (f * (t : ℝ)) :=
    pow_base_pos_of_mem hK ha0 hac hr hnn hle
  have hderiv : HasDerivAt (parisCrackPow r K a0)
      (K * parisCrackPow r K a0 (f * (t : ℝ)) ^ (1 - r)) (f * (t : ℝ)) :=
    hasDerivAt_parisCrackPow hr hbase
  have hinner : HasDerivAt (fun s : ℝ => f * s) f (t : ℝ) := by
    have h := HasDerivAt.const_mul f (hasDerivAt_id (t : ℝ))
    simpa using h
  have hcomp : HasDerivAt ((parisCrackPow r K a0) ∘ (fun s : ℝ => f * s))
      ((K * parisCrackPow r K a0 (f * (t : ℝ)) ^ (1 - r)) * f) (t : ℝ) :=
    HasDerivAt.comp (t : ℝ) (h := fun s : ℝ => f * s) (h₂ := parisCrackPow r K a0)
      hderiv hinner
  constructor
  · change parisCrackPow r K a0
          (min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
        = parisCrackPow r K a0 (f * (t : ℝ))
    rw [hmin]
  · have heq : (K * parisCrackPow r K a0 (f * (t : ℝ)) ^ (1 - r)) * f
        = f * (K * parisCrackPow r K a0 (f * (t : ℝ)) ^ (1 - r)) := by ring
    rw [heq] at hcomp
    exact hcomp

/-- **Physical lifetime, power branch.** For `K > 0`, `0 < a0 < a_c`, `r ≠ 0` and a positive load
frequency `f`, the damage lifetime of the event path against the critical crack length is
`Nf / f`, the Paris life in cycles over the cycles per unit time. -/
lemma damageLifetime_saturatedCrackPath_pow {r K a0 KIC Y σ f : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < criticalCrackLength KIC Y σ) (hr : r ≠ 0) (hf : 0 < f) (ω : Ω) :
    damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackPow r K a0) f
        (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
      (fun _ => criticalCrackLength KIC Y σ) ω =
      ENNReal.ofReal (parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f) := by
  obtain ⟨hcont, hmono⟩ :=
    continuous_monotone_saturatedCrackPath_pow hK ha0 hac hr (le_of_lt hf)
  have hNf : 0 < parisLifePow r K a0 (criticalCrackLength KIC Y σ) :=
    parisLifePow_pos hK ha0 hac hr
  have hac0 : 0 < criticalCrackLength KIC Y σ := lt_trans ha0 hac
  have hq : 0 ≤ parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f :=
    le_of_lt (div_pos hNf hf)
  have hofReal : ENNReal.ofReal (parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f)
      = ↑(NNReal.mk (parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f) hq) :=
    ENNReal.ofReal_eq_coe_nnreal hq
  rw [hofReal]
  have key : ∀ t : ℝ≥0, ((t : ℝ≥0∞)
      < damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackPow r K a0) f
          (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω
      ↔ (t : ℝ) < parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f) := by
    intro t
    refine (lt_damageLifetime_iff
      (d := fun _ : Ω => saturatedCrackPath (parisCrackPow r K a0) f
        (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
      (D := fun _ => criticalCrackLength KIC Y σ) (ω := ω) hcont hmono t).trans ?_
    show saturatedCrackPath (parisCrackPow r K a0) f
          (parisLifePow r K a0 (criticalCrackLength KIC Y σ)) t
        < criticalCrackLength KIC Y σ
      ↔ (t : ℝ) < parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f
    constructor
    · intro h
      by_contra hcon
      rw [not_lt] at hcon
      have hge : parisLifePow r K a0 (criticalCrackLength KIC Y σ) ≤ f * (t : ℝ) := by
        have h1 := (div_le_iff₀ hf).mp hcon
        linarith
      have hmin : min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ))
          = parisLifePow r K a0 (criticalCrackLength KIC Y σ) := min_eq_right hge
      have hsat : saturatedCrackPath (parisCrackPow r K a0) f
          (parisLifePow r K a0 (criticalCrackLength KIC Y σ)) t
          = criticalCrackLength KIC Y σ := by
        change parisCrackPow r K a0
            (min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
          = criticalCrackLength KIC Y σ
        rw [hmin]
        exact parisCrackPow_at_life hK ha0 hac0 hr
      rw [hsat] at h
      exact lt_irrefl _ h
    · intro h
      have hlt : f * (t : ℝ) < parisLifePow r K a0 (criticalCrackLength KIC Y σ) := by
        have h1 := (lt_div_iff₀ hf).mp h
        linarith
      have hmin : min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ))
          = f * (t : ℝ) := min_eq_left (le_of_lt hlt)
      have hnn : 0 ≤ f * (t : ℝ) := mul_nonneg (le_of_lt hf) t.coe_nonneg
      have hbase : 0 < a0 ^ r + r * K * (f * (t : ℝ)) :=
        pow_base_pos_of_mem hK ha0 hac hr hnn (le_of_lt hlt)
      have hiff := parisCrackPow_lt_iff hK ha0 hac hr hbase
      change parisCrackPow r K a0
          (min (f * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
        < criticalCrackLength KIC Y σ
      rw [hmin]
      exact hiff.mpr hlt
  apply le_antisymm
  · refine (damageLifetime_le_iff
      (d := fun _ : Ω => saturatedCrackPath (parisCrackPow r K a0) f
        (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
      (D := fun _ => criticalCrackLength KIC Y σ) (ω := ω)
      (t := NNReal.mk (parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f) hq)
      hcont hmono).mpr ?_
    change criticalCrackLength KIC Y σ ≤ saturatedCrackPath (parisCrackPow r K a0) f
        (parisLifePow r K a0 (criticalCrackLength KIC Y σ))
        (NNReal.mk (parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f) hq)
    have ht : parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f
        ≤ ↑(NNReal.mk (parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f) hq) := le_rfl
    have hsat := saturatedCrackPath_of_le (parisCrackPow r K a0) hf ht
    rw [hsat, parisCrackPow_at_life hK ha0 hac0 hr]
  · by_contra hcon
    rw [not_le] at hcon
    have hLtop : damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackPow r K a0) f
          (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω ≠ ⊤ :=
      lt_top_iff_ne_top.mp (lt_of_lt_of_le hcon (le_of_lt ENNReal.coe_lt_top))
    have hLcoe : (((damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackPow r K a0) f
          (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω).toNNReal : ℝ≥0) : ℝ≥0∞)
        = damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackPow r K a0) f
          (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω :=
      ENNReal.coe_toNNReal hLtop
    have hlt : (damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackPow r K a0) f
          (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω).toNNReal
        < NNReal.mk (parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f) hq := by
      rw [← ENNReal.coe_lt_coe, hLcoe]
      exact hcon
    have hltR : (((damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackPow r K a0) f
          (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω).toNNReal : ℝ≥0) : ℝ)
        < parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f :=
      NNReal.coe_lt_coe.mpr hlt
    have hmem := (key _).mpr hltR
    rw [hLcoe] at hmem
    exact lt_irrefl _ hmem

/-- **No load, power branch.** At frequency `0` the event path is the constant `a0`, and below
the critical crack length its lifetime is `⊤`. -/
lemma damageLifetime_saturatedCrackPath_pow_zero {r K a0 KIC Y σ : ℝ} (hK : 0 < K)
    (ha0 : 0 < a0) (hac : a0 < criticalCrackLength KIC Y σ) (hr : r ≠ 0) (ω : Ω) :
    (∀ t, saturatedCrackPath (parisCrackPow r K a0) 0
        (parisLifePow r K a0 (criticalCrackLength KIC Y σ)) t = a0) ∧
      damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackPow r K a0) 0
          (parisLifePow r K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω = ⊤ := by
  have hNf : 0 < parisLifePow r K a0 (criticalCrackLength KIC Y σ) :=
    parisLifePow_pos hK ha0 hac hr
  have hconst : ∀ t : ℝ≥0, saturatedCrackPath (parisCrackPow r K a0) 0
      (parisLifePow r K a0 (criticalCrackLength KIC Y σ)) t = a0 := by
    intro t
    change parisCrackPow r K a0
        (min (0 * (t : ℝ)) (parisLifePow r K a0 (criticalCrackLength KIC Y σ))) = a0
    have h0 : (0 : ℝ) * (t : ℝ) = 0 := zero_mul _
    rw [h0]
    have hmin : min (0 : ℝ) (parisLifePow r K a0 (criticalCrackLength KIC Y σ)) = 0 :=
      min_eq_left (le_of_lt hNf)
    rw [hmin]
    exact parisCrackPow_zero hr ha0
  constructor
  · exact hconst
  · rw [damageLifetime_eq_top_iff]
    intro t
    show saturatedCrackPath (parisCrackPow r K a0) 0
        (parisLifePow r K a0 (criticalCrackLength KIC Y σ)) t
        < criticalCrackLength KIC Y σ
    rw [hconst t]
    exact hac

/-- **Failure strictly before blow-up (`m > 2`).** For `r < 0` and `f > 0`, the failure time
`Nf / f` is strictly before the time `a0 ^ r / (-(r K)) / f` at which the power-branch base would
reach zero. -/
lemma failureTime_lt_blowupTime {r K a0 KIC Y σ f : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < criticalCrackLength KIC Y σ) (hr : r < 0) (hf : 0 < f) :
    parisLifePow r K a0 (criticalCrackLength KIC Y σ) / f < a0 ^ r / (-(r * K)) / f := by
  have h := parisLifePow_lt_blowup hK ha0 hac hr
  rw [div_lt_iff₀ hf, div_mul_cancel₀ _ (ne_of_gt hf)]
  exact h

/-! ## I. The Paris lifetime: logarithmic branch and initial failure -/

/-- **A continuous nondecreasing event path, logarithmic branch.** For `K > 0`, `a0 > 0` and
`f ≥ 0` the event path of the logarithmic-branch crack is continuous and nondecreasing. -/
lemma continuous_monotone_saturatedCrackPath_exp {K a0 KIC Y σ f : ℝ} (hK : 0 < K)
    (ha0 : 0 < a0) (hf : 0 ≤ f) :
    Continuous (saturatedCrackPath (parisCrackExp K a0) f
        (parisLifeExp K a0 (criticalCrackLength KIC Y σ))) ∧
      Monotone (saturatedCrackPath (parisCrackExp K a0) f
        (parisLifeExp K a0 (criticalCrackLength KIC Y σ))) := by
  have hinner_cont : Continuous
      (fun t : ℝ≥0 => min (f * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ))) :=
    (continuous_const.mul NNReal.continuous_coe).min continuous_const
  have hinner_mono : Monotone
      (fun t : ℝ≥0 => min (f * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ))) := by
    intro s t hst
    exact min_le_min (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hst) hf) le_rfl
  have hcrack_cont : Continuous (parisCrackExp K a0) := by
    change Continuous fun N : ℝ => a0 * Real.exp (K * N)
    exact continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hcrack_mono : Monotone (parisCrackExp K a0) := by
    intro x y hxy
    change a0 * Real.exp (K * x) ≤ a0 * Real.exp (K * y)
    have hexp : Real.exp (K * x) ≤ Real.exp (K * y) :=
      Real.exp_monotone (mul_le_mul_of_nonneg_left hxy (le_of_lt hK))
    exact mul_le_mul_of_nonneg_left hexp (le_of_lt ha0)
  constructor
  · change Continuous fun t : ℝ≥0 =>
      parisCrackExp K a0 (min (f * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
    exact hcrack_cont.comp hinner_cont
  · change Monotone fun t : ℝ≥0 =>
      parisCrackExp K a0 (min (f * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
    exact hcrack_mono.comp hinner_mono

/-- **Before failure the event path is the crack in real time, logarithmic branch.** For `f > 0`,
up to the failure time `Nf / f` the event path is the crack after `f t` cycles, and
`s ↦ a (f s)` solves `da/dt = f K a`. -/
lemma hasDerivAt_parisCrackExp_time {K a0 KIC Y σ f : ℝ} (hf : 0 < f) {t : ℝ≥0}
    (ht : (t : ℝ) ≤ parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f) :
    saturatedCrackPath (parisCrackExp K a0) f
        (parisLifeExp K a0 (criticalCrackLength KIC Y σ)) t = parisCrackExp K a0 (f * t) ∧
      HasDerivAt (fun s : ℝ => parisCrackExp K a0 (f * s))
        (f * (K * parisCrackExp K a0 (f * t))) t := by
  have hle : f * (t : ℝ) ≤ parisLifeExp K a0 (criticalCrackLength KIC Y σ) := by
    have h1 := (le_div_iff₀ hf).mp ht
    linarith
  have hmin : min (f * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ))
      = f * (t : ℝ) := min_eq_left hle
  have hderiv : HasDerivAt (parisCrackExp K a0)
      (K * parisCrackExp K a0 (f * (t : ℝ))) (f * (t : ℝ)) :=
    hasDerivAt_parisCrackExp K a0 (f * (t : ℝ))
  have hinner : HasDerivAt (fun s : ℝ => f * s) f (t : ℝ) := by
    have h := HasDerivAt.const_mul f (hasDerivAt_id (t : ℝ))
    simpa using h
  have hcomp : HasDerivAt ((parisCrackExp K a0) ∘ (fun s : ℝ => f * s))
      ((K * parisCrackExp K a0 (f * (t : ℝ))) * f) (t : ℝ) :=
    HasDerivAt.comp (t : ℝ) (h := fun s : ℝ => f * s) (h₂ := parisCrackExp K a0)
      hderiv hinner
  constructor
  · change parisCrackExp K a0
          (min (f * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
        = parisCrackExp K a0 (f * (t : ℝ))
    rw [hmin]
  · have heq : (K * parisCrackExp K a0 (f * (t : ℝ))) * f
        = f * (K * parisCrackExp K a0 (f * (t : ℝ))) := by ring
    rw [heq] at hcomp
    exact hcomp

/-- **Physical lifetime, logarithmic branch.** For `K > 0`, `0 < a0 < a_c` and `f > 0` the
damage lifetime of the event path against the critical crack length is `Nf / f`. -/
lemma damageLifetime_saturatedCrackPath_exp {K a0 KIC Y σ f : ℝ} (hK : 0 < K) (ha0 : 0 < a0)
    (hac : a0 < criticalCrackLength KIC Y σ) (hf : 0 < f) (ω : Ω) :
    damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackExp K a0) f
        (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
      (fun _ => criticalCrackLength KIC Y σ) ω =
      ENNReal.ofReal (parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f) := by
  obtain ⟨hcont, hmono⟩ :=
    continuous_monotone_saturatedCrackPath_exp hK ha0 (le_of_lt hf)
  have hNf : 0 < parisLifeExp K a0 (criticalCrackLength KIC Y σ) :=
    parisLifeExp_pos hK ha0 hac
  have hac0 : 0 < criticalCrackLength KIC Y σ := lt_trans ha0 hac
  have hq : 0 ≤ parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f :=
    le_of_lt (div_pos hNf hf)
  have hofReal : ENNReal.ofReal (parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f)
      = ↑(NNReal.mk (parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f) hq) :=
    ENNReal.ofReal_eq_coe_nnreal hq
  rw [hofReal]
  have key : ∀ t : ℝ≥0, ((t : ℝ≥0∞)
      < damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackExp K a0) f
          (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω
      ↔ (t : ℝ) < parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f) := by
    intro t
    refine (lt_damageLifetime_iff
      (d := fun _ : Ω => saturatedCrackPath (parisCrackExp K a0) f
        (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
      (D := fun _ => criticalCrackLength KIC Y σ) (ω := ω) hcont hmono t).trans ?_
    show saturatedCrackPath (parisCrackExp K a0) f
          (parisLifeExp K a0 (criticalCrackLength KIC Y σ)) t
        < criticalCrackLength KIC Y σ
      ↔ (t : ℝ) < parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f
    constructor
    · intro h
      by_contra hcon
      rw [not_lt] at hcon
      have hge : parisLifeExp K a0 (criticalCrackLength KIC Y σ) ≤ f * (t : ℝ) := by
        have h1 := (div_le_iff₀ hf).mp hcon
        linarith
      have hmin : min (f * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ))
          = parisLifeExp K a0 (criticalCrackLength KIC Y σ) := min_eq_right hge
      have hsat : saturatedCrackPath (parisCrackExp K a0) f
          (parisLifeExp K a0 (criticalCrackLength KIC Y σ)) t
          = criticalCrackLength KIC Y σ := by
        change parisCrackExp K a0
            (min (f * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
          = criticalCrackLength KIC Y σ
        rw [hmin]
        exact parisCrackExp_at_life hK ha0 hac0
      rw [hsat] at h
      exact lt_irrefl _ h
    · intro h
      have hlt : f * (t : ℝ) < parisLifeExp K a0 (criticalCrackLength KIC Y σ) := by
        have h1 := (lt_div_iff₀ hf).mp h
        linarith
      have hmin : min (f * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ))
          = f * (t : ℝ) := min_eq_left (le_of_lt hlt)
      have hiff := parisCrackExp_lt_iff (N := f * (t : ℝ)) hK ha0 hac
      change parisCrackExp K a0
          (min (f * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
        < criticalCrackLength KIC Y σ
      rw [hmin]
      exact hiff.mpr hlt
  apply le_antisymm
  · refine (damageLifetime_le_iff
      (d := fun _ : Ω => saturatedCrackPath (parisCrackExp K a0) f
        (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
      (D := fun _ => criticalCrackLength KIC Y σ) (ω := ω)
      (t := NNReal.mk (parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f) hq)
      hcont hmono).mpr ?_
    change criticalCrackLength KIC Y σ ≤ saturatedCrackPath (parisCrackExp K a0) f
        (parisLifeExp K a0 (criticalCrackLength KIC Y σ))
        (NNReal.mk (parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f) hq)
    have ht : parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f
        ≤ ↑(NNReal.mk (parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f) hq) := le_rfl
    have hsat := saturatedCrackPath_of_le (parisCrackExp K a0) hf ht
    rw [hsat, parisCrackExp_at_life hK ha0 hac0]
  · by_contra hcon
    rw [not_le] at hcon
    have hLtop : damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackExp K a0) f
          (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω ≠ ⊤ :=
      lt_top_iff_ne_top.mp (lt_of_lt_of_le hcon (le_of_lt ENNReal.coe_lt_top))
    have hLcoe : (((damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackExp K a0) f
          (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω).toNNReal : ℝ≥0) : ℝ≥0∞)
        = damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackExp K a0) f
          (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω :=
      ENNReal.coe_toNNReal hLtop
    have hlt : (damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackExp K a0) f
          (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω).toNNReal
        < NNReal.mk (parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f) hq := by
      rw [← ENNReal.coe_lt_coe, hLcoe]
      exact hcon
    have hltR : (((damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackExp K a0) f
          (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω).toNNReal : ℝ≥0) : ℝ)
        < parisLifeExp K a0 (criticalCrackLength KIC Y σ) / f :=
      NNReal.coe_lt_coe.mpr hlt
    have hmem := (key _).mpr hltR
    rw [hLcoe] at hmem
    exact lt_irrefl _ hmem

/-- **No load, logarithmic branch.** At frequency `0` the event path is the constant `a0`, and
below the critical crack length its lifetime is `⊤`. -/
lemma damageLifetime_saturatedCrackPath_exp_zero {K a0 KIC Y σ : ℝ} (hK : 0 < K)
    (ha0 : 0 < a0) (hac : a0 < criticalCrackLength KIC Y σ) (ω : Ω) :
    (∀ t, saturatedCrackPath (parisCrackExp K a0) 0
        (parisLifeExp K a0 (criticalCrackLength KIC Y σ)) t = a0) ∧
      damageLifetime (fun _ : Ω => saturatedCrackPath (parisCrackExp K a0) 0
          (parisLifeExp K a0 (criticalCrackLength KIC Y σ)))
        (fun _ => criticalCrackLength KIC Y σ) ω = ⊤ := by
  have hNf : 0 < parisLifeExp K a0 (criticalCrackLength KIC Y σ) :=
    parisLifeExp_pos hK ha0 hac
  have hconst : ∀ t : ℝ≥0, saturatedCrackPath (parisCrackExp K a0) 0
      (parisLifeExp K a0 (criticalCrackLength KIC Y σ)) t = a0 := by
    intro t
    change parisCrackExp K a0
        (min (0 * (t : ℝ)) (parisLifeExp K a0 (criticalCrackLength KIC Y σ))) = a0
    have h0 : (0 : ℝ) * (t : ℝ) = 0 := zero_mul _
    rw [h0]
    have hmin : min (0 : ℝ) (parisLifeExp K a0 (criticalCrackLength KIC Y σ)) = 0 :=
      min_eq_left (le_of_lt hNf)
    rw [hmin]
    exact parisCrackExp_zero K a0
  constructor
  · exact hconst
  · rw [damageLifetime_eq_top_iff]
    intro t
    show saturatedCrackPath (parisCrackExp K a0) 0
        (parisLifeExp K a0 (criticalCrackLength KIC Y σ)) t
        < criticalCrackLength KIC Y σ
    rw [hconst t]
    exact hac

/-- **Initially failed.** An initial crack at or above the critical length is the constant event
path at `a0`, with lifetime `0`; no crack-growth law is used. -/
lemma damageLifetime_initiallyFailed {a0 KIC Y σ : ℝ} (hfail : criticalCrackLength KIC Y σ ≤ a0)
    (ω : Ω) :
    damageLifetime (fun (_ : Ω) (_ : ℝ≥0) => a0) (fun _ => criticalCrackLength KIC Y σ) ω = 0 := by
  exact damageLifetime_eq_zero hfail

/-! ## J. A solid circular shaft under bending and torsion -/

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
with shear factor `c` when `c` is positive and the functional returns `√(σ ^ 2 + c τ ^ 2)` on every
such state: `c = 3` for the von Mises (distortion-energy) criterion, `c = 4` for the Tresca
(maximum-shear) criterion. A factor `c ≤ 0` is excluded: `Real.sqrt` truncates negative arguments
to `0`, so a pure torque would have zero demand. -/
structure BendingTorsionCalibrated (Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ) (c : ℝ) : Prop where
  /-- The shear factor is positive. -/
  shearFactor_pos : 0 < c
  /-- The functional returns `√(σ ^ 2 + c τ ^ 2)` on every bending-torsion state. -/
  eq_sqrt : ∀ σ τ : ℝ, Φ (bendingTorsionState σ τ) = Real.sqrt (σ ^ 2 + c * τ ^ 2)

/-- The bending-torsion calibration contains the tensile-test calibration: at `τ = 0` the state
is uniaxial and the functional returns `|σ|`. -/
lemma BendingTorsionCalibrated.uniaxialCalibrated {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} {c : ℝ}
    (hΦ : BendingTorsionCalibrated Φ c) : Reliability.UniaxialCalibrated Φ := by
  intro σ
  have h : Matrix.diagonal ![σ, 0, 0] = bendingTorsionState σ 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bendingTorsionState]
  rw [h, hΦ.eq_sqrt]
  simp [Real.sqrt_sq_eq_abs]

/-- The demand at the critical point of a shaft of diameter `d > 0` under `M` and `T`:
`16 √(4 M ^ 2 + c T ^ 2) / (π d ³)`. -/
lemma shaftDemand_eq {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} {c : ℝ}
    (hΦ : BendingTorsionCalibrated Φ c) {d : ℝ} (hd : 0 < d) (M T : ℝ) :
    Φ (bendingTorsionState (shaftBendingStress M d) (shaftShearStress T d)) =
      16 * Real.sqrt (4 * M ^ 2 + c * T ^ 2) / (Real.pi * d ^ 3) := by
  rw [hΦ.eq_sqrt, (shaftStresses_eq hd.ne' M T).1, (shaftStresses_eq hd.ne' M T).2]
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

/-! ## K. Shaft sizing: boundary examples -/

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
  rw [h0.1, h0.2, hΦ.eq_sqrt]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    Real.sqrt_zero, Reliability.demandFailure, not_le, true_and]
  exact hA

/-- An unsupported stress-concentration assumption is rejected: at the nominal minimum diameter
the nominal demand equals the allowable, and a bending stress-concentration factor `K > 1`
(with `M ≠ 0`) raises the demand strictly above it. The nominal sizing inequality covers a plain
shaft only; a notch or shoulder needs its factor as a supplied input. -/
lemma stressConcentration_exceeds_at_minDiameter {Φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ} {c : ℝ}
    (hΦ : BendingTorsionCalibrated Φ c) {M A K : ℝ} (hM : M ≠ 0) (hA : 0 < A) (hK : 1 < K)
    (T : ℝ) :
    Φ (bendingTorsionState (shaftBendingStress M (shaftMinDiameter c M T A))
        (shaftShearStress T (shaftMinDiameter c M T A))) = A ∧
      A < Φ (bendingTorsionState (K * shaftBendingStress M (shaftMinDiameter c M T A))
        (shaftShearStress T (shaftMinDiameter c M T A))) := by
  set dm := shaftMinDiameter c M T A with hdm
  have hc : 0 ≤ c := hΦ.shearFactor_pos.le
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
  rw [hΦ.eq_sqrt] at hA'
  rw [hΦ.eq_sqrt, ← hA']
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
