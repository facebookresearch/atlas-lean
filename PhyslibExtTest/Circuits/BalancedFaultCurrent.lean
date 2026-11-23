/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.BalancedFaultCurrent
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

@[expose] public section

open PhyslibExt.Circuits.SymmetricalComponentCoordinates
open PhyslibExt.Circuits.BalancedThreePhase
open PhyslibExt.Circuits.PerUnitBases
open PhyslibExt.Circuits.BalancedFaultCurrent

namespace PhyslibExtTest.Circuits.BalancedFaultCurrent

/-- Bolted fault (`Zf = 0`) behind a unit reactance `Zth = i` with a unit
source: the fault current is `-i`. -/
example : faultCurrent 1 Complex.I 0 = -Complex.I := by
  have h := faultCurrent_bolted_reactive 1 1 one_ne_zero
  simp only [Complex.ofReal_one, one_mul, mul_one, div_one] at h
  exact h

/-- Bolted fault behind `Zth = 2 i` with source `E = 4`: the fault current
is `-2 i`. -/
example : faultCurrent 4 ((2 : ℝ) * Complex.I) 0 = -2 * Complex.I := by
  rw [faultCurrent_bolted_reactive 4 2 two_ne_zero]
  push_cast
  ring

/-- The bolted fault voltage is zero. -/
example : faultVoltage 1 Complex.I 0 = 0 :=
  faultVoltage_bolted 1 Complex.I

/-- The bolted fault current `-i` and voltage `0` satisfy both the
Thevenin law and the fault law. -/
example : IsTheveninFault 1 Complex.I 0 0 (-Complex.I) := by
  have h := isTheveninFault_faultCurrent 1 Complex.I 0 (by simp)
  rwa [faultVoltage_bolted, show faultCurrent 1 Complex.I 0 = -Complex.I by
    simp [faultCurrent]] at h

/-- A resistive fault `Zf = 1` behind `Zth = i`: the laws do not hold at
`V = I = 1`, which differs from the fault current `(1 - i) / 2`. -/
example : ¬ IsTheveninFault 1 Complex.I 1 1 1 := by
  have hne : Complex.I + 1 ≠ 0 := by
    intro h
    simpa using congrArg Complex.re h
  rw [isTheveninFault_iff 1 Complex.I 1 1 1 hne]
  rintro ⟨h, -⟩
  rw [faultCurrent, eq_div_iff hne] at h
  simpa using congrArg Complex.im h

/-- The bolted fault phase currents `(-i, -i α², -i α)` have zero
zero-sequence and negative-sequence components and positive-sequence
component `-i`. -/
example :
    zeroSequence (faultPhaseCurrents 1 Complex.I 0 0) (faultPhaseCurrents 1 Complex.I 0 1)
        (faultPhaseCurrents 1 Complex.I 0 2) = 0 ∧
      positiveSequence (faultPhaseCurrents 1 Complex.I 0 0)
        (faultPhaseCurrents 1 Complex.I 0 1) (faultPhaseCurrents 1 Complex.I 0 2) =
        -Complex.I ∧
      negativeSequence (faultPhaseCurrents 1 Complex.I 0 0)
        (faultPhaseCurrents 1 Complex.I 0 1) (faultPhaseCurrents 1 Complex.I 0 2) = 0 := by
  obtain ⟨h0, h1, h2⟩ := sequence_faultPhaseCurrents 1 Complex.I 0
  refine ⟨h0, ?_, h2⟩
  rw [h1]
  simp [faultCurrent]

/-- Each bolted fault phase, here phase `b`, obeys the same Thevenin and
fault laws with the rotated source `α² * 1`. -/
example : IsTheveninFault (balancedPhases 1 1) Complex.I 0
    (balancedPhases (faultVoltage 1 Complex.I 0) 1) (faultPhaseCurrents 1 Complex.I 0 1) :=
  isTheveninFault_faultPhaseCurrents 1 Complex.I 0 (by simp) 1

/-- Per-unit bolted fault at bases `Vb = 2`, `Ib = 4` (impedance base
`1 / 2`): the per-unit fault current is `(1 / 2) / (2 i)`, and the
physical current is `4` times it. -/
example : currentPerUnit 4 (faultCurrent 1 Complex.I 0) =
    faultCurrent (voltagePerUnit 2 1) (impedancePerUnit 2 4 Complex.I)
      (impedancePerUnit 2 4 0) :=
  faultCurrent_perUnit 1 Complex.I 0 2 4 (by norm_num) (by norm_num)

/-- The per-unit bolted fault current at bases `Vb = 2`, `Ib = 4` is
`-i / 4`. -/
example : currentPerUnit 4 (faultCurrent 1 Complex.I 0) = -Complex.I / 4 := by
  simp [currentPerUnit, faultCurrent]

/-- Zero total impedance `Zth = i`, `Zf = -i` with a unit source admits
no solution. -/
example (V I : ℂ) : ¬ IsTheveninFault 1 Complex.I (-Complex.I) V I :=
  not_isTheveninFault_of_total_eq_zero 1 Complex.I (-Complex.I) V I (by ring) one_ne_zero

/-- Zero total impedance with a zero source: the current `5` solves the
laws, so the fault current is not determined. -/
example : IsTheveninFault 0 Complex.I (-Complex.I) (-Complex.I * 5) 5 :=
  isTheveninFault_of_total_eq_zero Complex.I (-Complex.I) 5 (by ring)

/-- The one-phase set `(1, 0, 0)` has all sequence components `1 / 3` and
is not a balanced set. -/
example : (zeroSequence 1 0 0 = 1 / 3 ∧ positiveSequence 1 0 0 = 1 / 3 ∧
      negativeSequence 1 0 0 = 1 / 3) ∧
    ∀ X : ℂ, (![1, 0, 0] : ZMod 3 → ℂ) ≠ balancedPhases X :=
  ⟨sequence_singlePhase 1, singlePhase_ne_balancedPhases 1 one_ne_zero⟩

/-- The headline at the bolted case with bases `Vb = 2`, `Ib = 4`. -/
example : currentPerUnit 4 (1 / (Complex.I + 0)) =
    voltagePerUnit 2 1 / (impedancePerUnit 2 4 Complex.I + impedancePerUnit 2 4 0) :=
  (fault_correct 1 Complex.I 0 (by simp) 2 4 (by norm_num) (by norm_num)).2.2

end PhyslibExtTest.Circuits.BalancedFaultCurrent
