/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQSupportCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQSupportProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQPhaseCoordinates

/-! Genuine nonzero physical short coefficients constrain every original full-axis Q fixer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
-- Bind each covector entry to the entire original preferred short lift.
/-- The stated phase matrix is the actual modulation-translation covector of every selected lift. -/
theorem generatedTenth_Q_support_phase_matrix_finite : ∀ j : Fin 23, ∀ i : Fin 24,
    generatedTenthQSupportPhaseMatrix j i =
      Fin.append
        (spinModulation (generatedAxisGlobalShortQFinite (generatedTenthQSupportIndex j)))
        (spinTranslation (generatedAxisGlobalShortQFinite (generatedTenthQSupportIndex j))) i := by
  decide +kernel

/-- Every literal matrix equation is the actual original selected-short conjugation phase. -/
theorem generatedTenth_Q_support_phase_coordinates (q : Q) (j : Fin 23) :
    Multiplicative.toAdd (localAxisQPhase (generatedTenthQSupportIndex j) q) =
      (generatedTenthQSupportPhaseMatrix *ᵥ Multiplicative.toAdd q.base) j := by
  rw [generatedTenth_Q_phase_coordinates]
  change _ = generatedTenthQSupportPhaseMatrix j ⬝ᵥ Multiplicative.toAdd q.base
  apply congrArg (fun v : Fin 24 → ZMod 2 => v ⬝ᵥ Multiplicative.toAdd q.base)
  funext i
  have h := generatedTenth_Q_support_phase_matrix_finite j i
  rw [generatedAxisGlobalShortQFinite_actual] at h
  exact h.symm

/-- Every full-axis Q fixer annihilates all checked genuine nonzero short phase covectors. -/
theorem generatedTenth_Q_support_phases_zero (q : Q)
    (hq : rhoLocal (inclQ q) generatedTenthAxis = generatedTenthAxis) :
    generatedTenthQSupportPhaseMatrix *ᵥ Multiplicative.toAdd q.base = 0 := by
  funext j
  rw [← generatedTenth_Q_support_phase_coordinates]
  have hp := ((generatedFourthQ_full_fixed_iff q generatedTenthAxis).mp hq).1
    (generatedTenthQSupportIndex j) (generatedTenth_Q_support_nonzero j)
  rw [hp]
  rfl

/-- The remaining original free coordinates determine the entire quotient of every full-axis Q
  fixer. -/
theorem generatedTenth_Q_support_free_quotient (q : Q)
    (hq : rhoLocal (inclQ q) generatedTenthAxis = generatedTenthAxis) :
    generatedTenthQSupportFreeProjection *ᵥ
      (generatedTenthQSupportFreeMatrix *ᵥ Multiplicative.toAdd q.base) =
        Multiplicative.toAdd q.base :=
  generatedTenth_Q_support_free_determines _ (generatedTenth_Q_support_phases_zero q hq)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
