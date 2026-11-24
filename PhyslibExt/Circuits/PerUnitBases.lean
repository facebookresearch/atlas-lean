/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.BalancedThreePhase
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.ZMod.Basic

/-!
# Per-unit bases for balanced three-phase quantities

## i. Overview

For positive real phase root-mean-square voltage and current bases
`Vb` and `Ib`, the three-phase power base is `3 * Vb * Ib`, the
impedance base is `Vb / Ib`, and the line-voltage base is
`Real.sqrt 3 * Vb`. Per-unit quantities are the physical complex
voltage, current, impedance, and power divided by those bases, with
each real base read as a complex scalar. Per-unit quantities are
dimensionless coordinate changes over the existing phasor
conventions, not a new quantity framework.

## ii. Key results

- `bases_correct`: the headline statement. For positive bases, the
  per-unit coordinate change preserves Ohm's law, sends balanced
  three-phase power `3 * V * conj I` to `Vpu * conj Ipu`, and the
  impedance base is the squared line-voltage base divided by the
  power base.
- `ohm_perUnit_iff`: Ohm's law `V = Z * I` holds physically if and
  only if it holds in per-unit coordinates.
- `threePhasePower_perUnit` and `balancedPower_perUnit`: the
  balanced power identity, stated directly and through the summed
  phase powers of `PhyslibExt.Circuits.BalancedThreePhase`.
- `impedanceBase_eq_lineVoltageBase_sq_div`: the impedance base is
  the squared line-voltage base divided by the power base.
- `lineVoltageBase_eq_norm_lineVoltage`: the line-voltage base is
  the magnitude of every balanced line voltage built from the phase
  base.

The supporting identities are proved by unfolding the base
definitions and cancelling the nonzero bases as complex or real
fields. The balanced power result rewrites the phase sum with the
canonical `sum_complexPower_balancedPhases` theorem and then applies
the direct power identity. The line-voltage result rewrites the
line voltage magnitude with the canonical
`norm_lineVoltage_balancedPhases` theorem and evaluates the norm of
the positive real base. The remaining base identities use
`Real.sq_sqrt` and cancellation of the nonzero bases.

## iii. Table of contents

- A. Bases and per-unit coordinates
- B. Ohm's law and balanced power in per-unit coordinates
- C. The line-voltage base and the impedance base

## iv. References

- J. J. Grainger and W. D. Stevenson Jr., *Power System Analysis*,
  McGraw-Hill, 1994: the per-unit system, three-phase power bases,
  and the relation between phase and line-voltage bases.

## A. Bases and per-unit coordinates
-/

@[expose] public section

open ComplexConjugate
open PhyslibExt.Circuits.BalancedThreePhase

namespace PhyslibExt.Circuits.PerUnitBases

/-- Three-phase power base for phase voltage and current bases. -/
def threePhasePowerBase (Vb Ib : ℝ) : ℝ :=
  3 * Vb * Ib

/-- Impedance base for phase voltage and current bases. -/
noncomputable def impedanceBase (Vb Ib : ℝ) : ℝ :=
  Vb / Ib

/-- Line-voltage base belonging to a phase-voltage base: the square
root of three times the phase base. -/
noncomputable def lineVoltageBase (Vb : ℝ) : ℝ :=
  Real.sqrt 3 * Vb

/-- Voltage in per-unit coordinates: physical voltage divided by
the phase-voltage base, read as a complex scalar. -/
noncomputable def voltagePerUnit (Vb : ℝ) (V : ℂ) : ℂ :=
  V / (Vb : ℂ)

/-- Current in per-unit coordinates: physical current divided by
the phase-current base, read as a complex scalar. -/
noncomputable def currentPerUnit (Ib : ℝ) (I : ℂ) : ℂ :=
  I / (Ib : ℂ)

/-- Impedance in per-unit coordinates: physical impedance divided
by the impedance base, read as a complex scalar. -/
noncomputable def impedancePerUnit (Vb Ib : ℝ) (Z : ℂ) : ℂ :=
  Z / (impedanceBase Vb Ib : ℂ)

/-- Complex power in per-unit coordinates: physical power divided
by the three-phase power base, read as a complex scalar. -/
noncomputable def powerPerUnit (Vb Ib : ℝ) (S : ℂ) : ℂ :=
  S / (threePhasePowerBase Vb Ib : ℂ)

/-- All three bases are positive for positive phase bases, and the
line-voltage base is positive for a positive phase base. -/
lemma bases_pos (Vb Ib : ℝ) (hVb : 0 < Vb) (hIb : 0 < Ib) :
    0 < threePhasePowerBase Vb Ib ∧ 0 < impedanceBase Vb Ib ∧
      0 < lineVoltageBase Vb := by
  unfold threePhasePowerBase impedanceBase lineVoltageBase
  have hsqrt : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  exact ⟨by positivity, div_pos hVb hIb, mul_pos hsqrt hVb⟩

/-- Multiplying a per-unit voltage by its base recovers the physical
voltage, for a nonzero base. -/
lemma base_mul_voltagePerUnit (Vb : ℝ) (hVb : Vb ≠ 0) (V : ℂ) :
    (Vb : ℂ) * voltagePerUnit Vb V = V := by
  unfold voltagePerUnit
  have h : (Vb : ℂ) ≠ 0 := by exact_mod_cast hVb
  field_simp

/-! ### B. Ohm's law and balanced power in per-unit coordinates -/

/-- Ohm's law is preserved by the per-unit coordinate change:
`V = Z * I` if and only if the per-unit quantities satisfy the same
equation, for positive bases. -/
theorem ohm_perUnit_iff (Vb Ib : ℝ) (hVb : 0 < Vb) (hIb : 0 < Ib)
    (V Z I : ℂ) :
    (V = Z * I) ↔
      voltagePerUnit Vb V = impedancePerUnit Vb Ib Z * currentPerUnit Ib I := by
  unfold voltagePerUnit impedancePerUnit currentPerUnit impedanceBase
  push_cast
  have hVb' : (Vb : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hVb
  have hIb' : (Ib : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hIb
  have hdiv : (Vb : ℂ) / (Ib : ℂ) ≠ 0 := div_ne_zero hVb' hIb'
  rw [div_eq_iff hVb']
  have key : Z / ((Vb : ℂ) / (Ib : ℂ)) * (I / (Ib : ℂ)) * (Vb : ℂ)
      = Z * I := by
    field_simp
  rw [key]

/-- Balanced three-phase power in per-unit coordinates: physical
power `3 * V * conj I` divided by the power base equals
`Vpu * conj Ipu`, for positive bases. -/
theorem threePhasePower_perUnit (Vb Ib : ℝ) (hVb : 0 < Vb) (hIb : 0 < Ib)
    (V I : ℂ) :
    powerPerUnit Vb Ib (3 * V * conj I) =
      voltagePerUnit Vb V * conj (currentPerUnit Ib I) := by
  unfold powerPerUnit voltagePerUnit currentPerUnit threePhasePowerBase
  push_cast
  have hVb' : (Vb : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hVb
  have hIb' : (Ib : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hIb
  have hSb : (3 : ℂ) * (Vb : ℂ) * (Ib : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hVb') hIb'
  rw [map_div₀, Complex.conj_ofReal]
  field_simp

/-- The same power identity read through the balanced phase sum:
the summed phase powers, divided by the power base, equal
`Vpu * conj Ipu`. The phase sum is evaluated by the canonical
balanced three-phase power theorem. -/
theorem balancedPower_perUnit (Vb Ib : ℝ) (hVb : 0 < Vb) (hIb : 0 < Ib)
    (V I : ℂ) :
    powerPerUnit Vb Ib
        (∑ p, complexPower (balancedPhases V p) (balancedPhases I p)) =
      voltagePerUnit Vb V * conj (currentPerUnit Ib I) := by
  rw [sum_complexPower_balancedPhases, ← mul_assoc]
  exact threePhasePower_perUnit Vb Ib hVb hIb V I

/-! ### C. The line-voltage base and the impedance base -/

/-- The impedance base is the squared line-voltage base divided by
the three-phase power base, for positive bases. -/
theorem impedanceBase_eq_lineVoltageBase_sq_div (Vb Ib : ℝ)
    (hVb : 0 < Vb) (hIb : 0 < Ib) :
    impedanceBase Vb Ib =
      lineVoltageBase Vb ^ 2 / threePhasePowerBase Vb Ib := by
  unfold impedanceBase lineVoltageBase threePhasePowerBase
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hVb' : Vb ≠ 0 := ne_of_gt hVb
  have hIb' : Ib ≠ 0 := ne_of_gt hIb
  have hSb : 3 * Vb * Ib ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hVb') hIb'
  rw [mul_pow, hsq]
  field_simp

/-- The line-voltage base is the magnitude of every balanced line
voltage built from the phase base, for a positive phase base. This
is the canonical line-voltage magnitude theorem evaluated at the
real base. -/
theorem lineVoltageBase_eq_norm_lineVoltage (Vb : ℝ) (hVb : 0 < Vb)
    (p : ZMod 3) :
    lineVoltageBase Vb =
      ‖lineVoltage (balancedPhases (Vb : ℂ)) p‖ := by
  rw [norm_lineVoltage_balancedPhases]
  unfold lineVoltageBase
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hVb]

/-- The squared phase-voltage base divided by the power base is one
third of the impedance base. Omitting the square-root-of-three
factor in the line-voltage base therefore understates the impedance
base by a factor of three, for positive bases. -/
lemma phaseVoltageBase_sq_div_powerBase (Vb Ib : ℝ)
    (hVb : 0 < Vb) (hIb : 0 < Ib) :
    Vb ^ 2 / threePhasePowerBase Vb Ib = impedanceBase Vb Ib / 3 := by
  unfold threePhasePowerBase impedanceBase
  have hVb' : Vb ≠ 0 := ne_of_gt hVb
  have hIb' : Ib ≠ 0 := ne_of_gt hIb
  have hSb : 3 * Vb * Ib ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hVb') hIb'
  field_simp

/-- Headline: for positive phase voltage and current bases, the
per-unit coordinate change preserves Ohm's law, sends balanced
three-phase power to the per-unit power product, and the impedance
base is the squared line-voltage base over the power base. -/
theorem bases_correct (Vb Ib : ℝ) (hVb : 0 < Vb) (hIb : 0 < Ib) :
    (∀ V Z I : ℂ, (V = Z * I) ↔
      voltagePerUnit Vb V = impedancePerUnit Vb Ib Z * currentPerUnit Ib I) ∧
    (∀ V I : ℂ, powerPerUnit Vb Ib (3 * V * conj I) =
      voltagePerUnit Vb V * conj (currentPerUnit Ib I)) ∧
    impedanceBase Vb Ib =
      lineVoltageBase Vb ^ 2 / threePhasePowerBase Vb Ib := by
  refine ⟨fun V Z I => ohm_perUnit_iff Vb Ib hVb hIb V Z I,
    fun V I => threePhasePower_perUnit Vb Ib hVb hIb V I,
    impedanceBase_eq_lineVoltageBase_sq_div Vb Ib hVb hIb⟩

end PhyslibExt.Circuits.PerUnitBases
