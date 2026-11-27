/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.PerUnitBases
public import PhyslibExt.Circuits.BalancedThreePhase
public import PhyslibExt.Circuits.SymmetricalComponentCoordinates
public import Mathlib.Data.ZMod.Basic

/-!
# Balanced three-phase fault current

## i. Overview

A balanced positive-sequence fixed-frequency AC source is given by its
Thevenin equivalent: an internal phase voltage phasor `E` behind a
complex impedance `Zth`, so the terminal voltage is `V = E - Zth * I`.
A balanced fault through a complex impedance `Zf` imposes `V = Zf * I`.
When the total impedance `Zth + Zf` is nonzero, the two laws hold
exactly at the fault current `I = E / (Zth + Zf)` and the fault voltage
`V = Zf * I`. The three phase currents are the balanced
positive-sequence set `(I, α² I, α I)`; each phase obeys the same
Thevenin and fault laws, the zero- and negative-sequence components of
the phase currents vanish, and the positive-sequence component is `I`.
On positive phase voltage and current bases the same formula holds with
every quantity in per-unit, and the physical current is the current
base times the per-unit current. Unbalanced faults and subtransient
machine models are out of scope.

## ii. Key results

- `fault_correct`: the headline statement combining the fault
  solution, the sequence components of the phase currents, and the
  per-unit fault current formula.
- `isTheveninFault_iff`: with nonzero total impedance, the Thevenin
  and fault laws hold exactly at the fault current and voltage.
- `sequence_faultPhaseCurrents`: the fault phase currents are purely
  positive sequence.
- `faultCurrent_perUnit`: the per-unit fault current is the per-unit
  source voltage over the per-unit total impedance.
- `faultCurrent_bolted_reactive`, `not_isTheveninFault_of_total_eq_zero`,
  `singlePhase_ne_balancedPhases`: the bolted reactive case, the
  excluded zero total impedance, and an unbalanced one-phase set.

The fault solution is linear algebra in one complex unknown. The
balanced phases rotate a one-phase solution by `α²` and `α`, and the
sequence components are read off the canonical
`balanced_positive_sequence_components`. The per-unit statements
cancel the nonzero bases using `impedanceBase Vb Ib * Ib = Vb`.

## iii. Table of contents

- A. The Thevenin source and the balanced fault
- B. Solving the fault
- C. Balanced phase reconstruction
- D. Physical and per-unit values
- E. Validation cases
- F. Headline

## iv. References

- J. J. Grainger and W. D. Stevenson Jr., *Power System Analysis*,
  McGraw-Hill, 1994: symmetrical three-phase faults through the
  Thevenin equivalent at the fault point, and the per-unit system.

## A. The Thevenin source and the balanced fault
-/

@[expose] public section

namespace PhyslibExt.Circuits.BalancedFaultCurrent

open PhyslibExt.Circuits.SymmetricalComponentCoordinates
open PhyslibExt.Circuits.BalancedThreePhase
open PhyslibExt.Circuits.PerUnitBases

private theorem base_mul (Vb Ib : ℝ) (hIb : (Ib : ℂ) ≠ 0) :
    ((impedanceBase Vb Ib : ℝ) : ℂ) * (Ib : ℂ) = (Vb : ℂ) := by
  unfold impedanceBase
  push_cast
  exact div_mul_cancel₀ _ hIb

private theorem base_ne_zero (Vb Ib : ℝ) (hVb : 0 < Vb) (hIb : 0 < Ib) :
    ((impedanceBase Vb Ib : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (bases_pos Vb Ib hVb hIb).2.1.ne'

private theorem zmod3_cases (p : ZMod 3) : p = 0 ∨ p = 1 ∨ p = 2 := by
  have hall : ∀ q : ZMod 3, q = 0 ∨ q = 1 ∨ q = 2 := by decide
  exact hall p

/-- The supplied Thevenin source law `V = E - Zth * I` and the balanced
fault law `V = Zf * I`, for one positive-sequence phase. -/
def IsTheveninFault (E Zth Zf V I : ℂ) : Prop :=
  V = E - Zth * I ∧ V = Zf * I

/-- Fault current `E / (Zth + Zf)`. -/
noncomputable def faultCurrent (E Zth Zf : ℂ) : ℂ :=
  E / (Zth + Zf)

/-- Fault voltage `Zf * E / (Zth + Zf)` at the faulted terminals. -/
noncomputable def faultVoltage (E Zth Zf : ℂ) : ℂ :=
  Zf * faultCurrent E Zth Zf

/-- Balanced phase currents of the fault, the canonical positive-sequence
set built from the fault current. -/
noncomputable def faultPhaseCurrents (E Zth Zf : ℂ) : ZMod 3 → ℂ :=
  balancedPhases (faultCurrent E Zth Zf)

/-! ## B. Solving the fault -/

/-- With nonzero total impedance, the Thevenin and fault laws hold exactly
at the fault current and fault voltage. -/
theorem isTheveninFault_iff (E Zth Zf V I : ℂ) (h : Zth + Zf ≠ 0) :
    IsTheveninFault E Zth Zf V I ↔
      I = faultCurrent E Zth Zf ∧ V = faultVoltage E Zth Zf := by
  unfold IsTheveninFault faultVoltage faultCurrent
  constructor
  · rintro ⟨h1, h2⟩
    have hI : I = E / (Zth + Zf) := by
      rw [eq_div_iff h]
      linear_combination h1 - h2
    exact ⟨hI, by rw [h2, hI]⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, rfl⟩
    field_simp
    ring

/-- The fault current and voltage satisfy both laws. -/
lemma isTheveninFault_faultCurrent (E Zth Zf : ℂ) (h : Zth + Zf ≠ 0) :
    IsTheveninFault E Zth Zf (faultVoltage E Zth Zf) (faultCurrent E Zth Zf) :=
  (isTheveninFault_iff E Zth Zf _ _ h).mpr ⟨rfl, rfl⟩

/-- The fault voltage is also the source voltage minus the Thevenin drop. -/
lemma faultVoltage_eq_sub (E Zth Zf : ℂ) (h : Zth + Zf ≠ 0) :
    faultVoltage E Zth Zf = E - Zth * faultCurrent E Zth Zf :=
  (isTheveninFault_faultCurrent E Zth Zf h).1

/-! ## C. Balanced phase reconstruction -/

/-- Each balanced phase obeys the same Thevenin and fault laws: rotating a
single-phase solution by the balanced phase operators gives a solution in
every phase. -/
lemma isTheveninFault_balancedPhases (E Zth Zf V I : ℂ)
    (hf : IsTheveninFault E Zth Zf V I) (p : ZMod 3) :
    IsTheveninFault (balancedPhases E p) Zth Zf (balancedPhases V p) (balancedPhases I p) := by
  obtain ⟨h1, h2⟩ := hf
  rcases zmod3_cases p with rfl | rfl | rfl
  · exact ⟨h1, h2⟩
  · change alpha ^ 2 * V = alpha ^ 2 * E - Zth * (alpha ^ 2 * I) ∧
      alpha ^ 2 * V = Zf * (alpha ^ 2 * I)
    exact ⟨by linear_combination (alpha ^ 2) * h1, by linear_combination (alpha ^ 2) * h2⟩
  · change alpha * V = alpha * E - Zth * (alpha * I) ∧ alpha * V = Zf * (alpha * I)
    exact ⟨by linear_combination alpha * h1, by linear_combination alpha * h2⟩

/-- The balanced fault phase currents solve the per-phase laws with the
balanced source and the balanced fault voltages. -/
lemma isTheveninFault_faultPhaseCurrents (E Zth Zf : ℂ) (h : Zth + Zf ≠ 0) (p : ZMod 3) :
    IsTheveninFault (balancedPhases E p) Zth Zf
      (balancedPhases (faultVoltage E Zth Zf) p) (faultPhaseCurrents E Zth Zf p) :=
  isTheveninFault_balancedPhases E Zth Zf (faultVoltage E Zth Zf)
    (faultCurrent E Zth Zf) (isTheveninFault_faultCurrent E Zth Zf h) p

/-- The fault phase currents have zero zero-sequence and negative-sequence
components, and positive-sequence component equal to the fault current. -/
theorem sequence_faultPhaseCurrents (E Zth Zf : ℂ) :
    zeroSequence (faultPhaseCurrents E Zth Zf 0) (faultPhaseCurrents E Zth Zf 1)
        (faultPhaseCurrents E Zth Zf 2) = 0 ∧
      positiveSequence (faultPhaseCurrents E Zth Zf 0) (faultPhaseCurrents E Zth Zf 1)
        (faultPhaseCurrents E Zth Zf 2) = faultCurrent E Zth Zf ∧
      negativeSequence (faultPhaseCurrents E Zth Zf 0) (faultPhaseCurrents E Zth Zf 1)
        (faultPhaseCurrents E Zth Zf 2) = 0 :=
  balanced_positive_sequence_components (faultCurrent E Zth Zf)

/-! ## D. Physical and per-unit values -/

/-- The fault current in per-unit is the per-unit source voltage over the
per-unit total impedance. -/
theorem faultCurrent_perUnit (E Zth Zf : ℂ) (Vb Ib : ℝ) (hVb : 0 < Vb) (hIb : 0 < Ib) :
    currentPerUnit Ib (faultCurrent E Zth Zf) =
      faultCurrent (voltagePerUnit Vb E) (impedancePerUnit Vb Ib Zth)
        (impedancePerUnit Vb Ib Zf) := by
  have hIc : (Ib : ℂ) ≠ 0 := by exact_mod_cast hIb.ne'
  have hZc := base_ne_zero Vb Ib hVb hIb
  have hrel := base_mul Vb Ib hIc
  unfold faultCurrent currentPerUnit voltagePerUnit impedancePerUnit
  rw [← add_div, ← hrel, div_div_div_eq, div_div, mul_assoc, mul_comm E,
    mul_div_mul_left _ _ hZc, mul_comm (Zth + Zf)]

/-- The fault voltage in per-unit is the per-unit fault voltage formula. -/
lemma faultVoltage_perUnit (E Zth Zf : ℂ) (Vb Ib : ℝ) (hVb : 0 < Vb) (hIb : 0 < Ib) :
    voltagePerUnit Vb (faultVoltage E Zth Zf) =
      faultVoltage (voltagePerUnit Vb E) (impedancePerUnit Vb Ib Zth)
        (impedancePerUnit Vb Ib Zf) := by
  have hIc : (Ib : ℂ) ≠ 0 := by exact_mod_cast hIb.ne'
  have hrel := base_mul Vb Ib hIc
  unfold faultVoltage
  rw [← faultCurrent_perUnit E Zth Zf Vb Ib hVb hIb]
  unfold voltagePerUnit currentPerUnit impedancePerUnit
  rw [div_mul_div_comm, hrel]

/-- The Thevenin and fault laws hold physically if and only if they hold
in per-unit coordinates. -/
lemma isTheveninFault_perUnit_iff (E Zth Zf V I : ℂ) (Vb Ib : ℝ) (hVb : 0 < Vb)
    (hIb : 0 < Ib) :
    IsTheveninFault E Zth Zf V I ↔
      IsTheveninFault (voltagePerUnit Vb E) (impedancePerUnit Vb Ib Zth)
        (impedancePerUnit Vb Ib Zf) (voltagePerUnit Vb V) (currentPerUnit Ib I) := by
  have hVc : (Vb : ℂ) ≠ 0 := by exact_mod_cast hVb.ne'
  have hIc : (Ib : ℂ) ≠ 0 := by exact_mod_cast hIb.ne'
  have hrel := base_mul Vb Ib hIc
  have hmul (Z : ℂ) : impedancePerUnit Vb Ib Z * currentPerUnit Ib I = Z * I / (Vb : ℂ) := by
    unfold impedancePerUnit currentPerUnit
    rw [div_mul_div_comm, hrel]
  unfold IsTheveninFault
  rw [hmul, ← ohm_perUnit_iff Vb Ib hVb hIb]
  unfold voltagePerUnit
  rw [← sub_div, div_left_inj' hVc]

/-- Recovery of the physical fault current: the current base times the
per-unit fault current. -/
lemma faultCurrent_eq_base_mul_perUnit (E Zth Zf : ℂ) (Vb Ib : ℝ) (hVb : 0 < Vb)
    (hIb : 0 < Ib) :
    faultCurrent E Zth Zf =
      (Ib : ℂ) * faultCurrent (voltagePerUnit Vb E) (impedancePerUnit Vb Ib Zth)
        (impedancePerUnit Vb Ib Zf) := by
  have hIc : (Ib : ℂ) ≠ 0 := by exact_mod_cast hIb.ne'
  rw [← faultCurrent_perUnit E Zth Zf Vb Ib hVb hIb, currentPerUnit,
    mul_div_cancel₀ _ hIc]

/-- Per-unit phase currents of the fault are the balanced set of the
per-unit fault current. -/
lemma faultPhaseCurrents_perUnit (E Zth Zf : ℂ) (Vb Ib : ℝ) (hVb : 0 < Vb) (hIb : 0 < Ib)
    (p : ZMod 3) :
    currentPerUnit Ib (faultPhaseCurrents E Zth Zf p) =
      faultPhaseCurrents (voltagePerUnit Vb E) (impedancePerUnit Vb Ib Zth)
        (impedancePerUnit Vb Ib Zf) p := by
  have h := faultCurrent_perUnit E Zth Zf Vb Ib hVb hIb
  unfold currentPerUnit at h
  unfold faultPhaseCurrents currentPerUnit
  rw [← h]
  rcases zmod3_cases p with rfl | rfl | rfl
  · rfl
  · exact mul_div_assoc _ _ _
  · exact mul_div_assoc _ _ _

/-! ## E. Validation cases -/

/-- Bolted fault: with `Zf = 0` the fault voltage is zero. -/
lemma faultVoltage_bolted (E Zth : ℂ) : faultVoltage E Zth 0 = 0 :=
  zero_mul _

/-- Bolted fault behind a purely reactive Thevenin impedance `X * i` with
`X ≠ 0`: the fault current is `-i * E / X`, lagging the source by a
quarter period for `X > 0`. -/
lemma faultCurrent_bolted_reactive (E : ℂ) (X : ℝ) (hX : X ≠ 0) :
    faultCurrent E ((X : ℂ) * Complex.I) 0 = -Complex.I * E / (X : ℂ) := by
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  unfold faultCurrent
  rw [add_zero, div_eq_div_iff (mul_ne_zero hXc Complex.I_ne_zero) hXc]
  linear_combination E * (X : ℂ) * Complex.I_mul_I

/-- Zero total impedance is excluded: with a nonzero source no current
satisfies both laws. -/
lemma not_isTheveninFault_of_total_eq_zero (E Zth Zf V I : ℂ) (h : Zth + Zf = 0)
    (hE : E ≠ 0) :
    ¬ IsTheveninFault E Zth Zf V I := by
  rintro ⟨h1, h2⟩
  exact hE (by linear_combination h2 - h1 + I * h)

/-- Zero total impedance is excluded: with a zero source every current
satisfies both laws, so the fault current is not determined. -/
lemma isTheveninFault_of_total_eq_zero (Zth Zf I : ℂ) (h : Zth + Zf = 0) :
    IsTheveninFault 0 Zth Zf (Zf * I) I :=
  ⟨by linear_combination I * h, rfl⟩

/-- A one-phase current set `(I, 0, 0)` has all three sequence components
equal to `I / 3`. -/
lemma sequence_singlePhase (I : ℂ) :
    zeroSequence I 0 0 = I / 3 ∧ positiveSequence I 0 0 = I / 3 ∧
      negativeSequence I 0 0 = I / 3 := by
  simp [zeroSequence, positiveSequence, negativeSequence]

/-- A nonzero one-phase current set is not balanced. -/
lemma singlePhase_ne_balancedPhases (I : ℂ) (hI : I ≠ 0) (X : ℂ) :
    (![I, 0, 0] : ZMod 3 → ℂ) ≠ balancedPhases X := by
  intro hcon
  have h0 : I = X := congrFun hcon 0
  have h1 : (0 : ℂ) = alpha ^ 2 * X := congrFun hcon 1
  have hα2 : alpha ^ 2 ≠ 0 := pow_ne_zero 2 (isPrimitiveRoot_alpha.ne_zero (by norm_num))
  exact hI (h0.trans ((mul_eq_zero.mp h1.symm).resolve_left hα2))

/-! ## F. Headline -/

/-- Balanced three-phase fault current. For a supplied Thevenin source and
a balanced fault with `Zth + Zf ≠ 0`, the laws hold exactly at
`I = E / (Zth + Zf)` and `V = Zf * I`; the balanced phase currents have
zero zero- and negative-sequence components and positive-sequence
component `I`; and on positive phase bases the per-unit fault current is
the per-unit source over the per-unit total impedance. -/
theorem fault_correct (E Zth Zf : ℂ) (h : Zth + Zf ≠ 0) (Vb Ib : ℝ) (hVb : 0 < Vb)
    (hIb : 0 < Ib) :
    (∀ V I : ℂ, IsTheveninFault E Zth Zf V I ↔
        I = E / (Zth + Zf) ∧ V = Zf * (E / (Zth + Zf))) ∧
      (zeroSequence (faultPhaseCurrents E Zth Zf 0) (faultPhaseCurrents E Zth Zf 1)
          (faultPhaseCurrents E Zth Zf 2) = 0 ∧
        positiveSequence (faultPhaseCurrents E Zth Zf 0) (faultPhaseCurrents E Zth Zf 1)
          (faultPhaseCurrents E Zth Zf 2) = E / (Zth + Zf) ∧
        negativeSequence (faultPhaseCurrents E Zth Zf 0) (faultPhaseCurrents E Zth Zf 1)
          (faultPhaseCurrents E Zth Zf 2) = 0) ∧
      currentPerUnit Ib (E / (Zth + Zf)) =
        voltagePerUnit Vb E / (impedancePerUnit Vb Ib Zth + impedancePerUnit Vb Ib Zf) :=
  ⟨fun V I => isTheveninFault_iff E Zth Zf V I h, sequence_faultPhaseCurrents E Zth Zf,
    faultCurrent_perUnit E Zth Zf Vb Ib hVb hIb⟩

end PhyslibExt.Circuits.BalancedFaultCurrent
