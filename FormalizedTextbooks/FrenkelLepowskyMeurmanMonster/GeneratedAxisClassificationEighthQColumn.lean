/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthTensorSquares
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQFixedCriteria

/-! Actual full-axis fixation acts on the original nonzero twentieth spin column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An actual full-axis fixer fixes the entire genuine denominator-cleared twentieth column. -/
theorem generatedEighth_Q_column_fixed (q : Q) (hq : q ∈ generatedEighthAxisQStabilizer) :
    spinRepresentation q generatedEighthTensorColumn = generatedEighthTensorColumn := by
  change rhoLocal (inclQ q) generatedEighthAxis = generatedEighthAxis at hq
  have h := ((generatedFourthQ_full_fixed_iff q generatedEighthAxis).mp hq).2 (20 : Fin 24)
  change spinRepresentation q ((32 * Real.sqrt 2 : ℝ) •
    (fun t => (griessConwayEncode generatedEighthAxis).2.2 t 20)) = _
  rw [map_smul, h]
  rfl

/-- Actual full-axis fixation preserves every original column square along its Q translation. -/
theorem generatedEighth_Q_column_square (q : Q) (hq : q ∈ generatedEighthAxisQStabilizer)
    (t : SpinIndex) :
    (generatedEighthTensorColumn (t + spinTranslation q)) ^ 2 =
      (generatedEighthTensorColumn t) ^ 2 := by
  have h := (generatedSpinSupport_fixed_iff q generatedEighthTensorColumn).mp
    (generatedEighth_Q_column_fixed q hq) t
  have he := congrArg (fun z : ℝ => z ^ 2) h
  rw [mul_pow, pow_two (qSign _), qSign_sq, one_mul] at he
  exact he

/-- Zero original Q translation and the full nonzero column force every phase to vanish. -/
theorem generatedEighth_Q_phase_zero_of_translation_zero (q : Q)
    (hq : q ∈ generatedEighthAxisQStabilizer) (ha : spinTranslation q = 0) (t : SpinIndex) :
    spinPhase q t = 0 := by
  have h := (generatedSpinSupport_fixed_iff q generatedEighthTensorColumn).mp
    (generatedEighth_Q_column_fixed q hq) t
  rw [ha, add_zero] at h
  have hs : qSign (spinPhase q t) = 1 :=
    mul_right_cancel₀ (generatedEighth_tensor_column_ne_zero t)
      (h.trans (one_mul (generatedEighthTensorColumn t)).symm)
  exact (qSign_eq_one_iff _).mp hs

/-- Zero actual translation and full-axis fixation imply the identity Q element. -/
theorem generatedEighth_Q_eq_one_of_translation_zero (q : Q)
    (hq : q ∈ generatedEighthAxisQStabilizer) (ha : spinTranslation q = 0) : q = 1 := by
  have hc : Multiplicative.toAdd q.coeff = 0 := by
    have h := generatedEighth_Q_phase_zero_of_translation_zero q hq ha 0
    simpa only [spinPhase, spinDot_zero_right, add_zero] using h
  have hm : spinModulation q = 0 := by
    funext i
    have h := generatedEighth_Q_phase_zero_of_translation_zero q hq ha (Pi.single i 1)
    simpa [spinPhase, hc, spinDot, Pi.single_apply, mul_ite] using h
  apply generatedAxisFourthQ_spin_coordinates_injective
  · change spinTranslation q = 0
    exact ha
  · change spinModulation q = 0
    exact hm
  · change Multiplicative.toAdd q.coeff = 0
    exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
