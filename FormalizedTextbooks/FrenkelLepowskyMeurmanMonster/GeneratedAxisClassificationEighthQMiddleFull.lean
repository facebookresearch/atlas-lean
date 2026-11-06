/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQSupportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddQStabilizer

/-! Actual original Pauli transport fixes every coordinate of the Eighth middle axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual vector between the local word and the last original triality. -/
def generatedEighthMiddleAxis : GriessSpace :=
  rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis

/-- The genuine extraspecial stabilizer of the complete middle vector. -/
def generatedEighthMiddleAxisQStabilizer : Subgroup Q :=
  (MulAction.stabilizer H generatedEighthMiddleAxis).comap inclQ

/-- Each initial Pauli element fixes the entire original odd axis. -/
theorem generatedEighth_pauli_initial_full_fixed (j : Fin 12) :
    rhoLocal (inclQ (generatedEighthSpinPauliInitial j)) generatedOddAxis =
      generatedOddAxis :=
  generatedOddSpinStateStabilizer_le_axis (generatedEighth_spin_pauli_initial_fixed j)

private theorem transported_fix (f : localFiberSubgroup) (q : Q) (x : GriessSpace)
    (hq : rhoLocal (inclQ q) x = x) :
    rhoLocal (inclQ (spinConjugation f.val.1 q)) (rhoLocal (localFiberIntoH f) x) =
      rhoLocal (localFiberIntoH f) x := by
  have hc : inclQ (spinConjugation f.val.1 q) =
      localFiberIntoH f * inclQ q * (localFiberIntoH f)⁻¹ := by
    change QuotientGroup.mk' localDiagonalSubgroup
      (localFiberIncl (spinConjugation f.val.1 q)) = _
    rw [localFiberIncl_conjugate, map_mul, map_mul, map_inv]
    rfl
  rw [hc, map_mul, map_mul, map_inv]
  simp only [LinearEquiv.mul_apply]
  change rhoLocal (localFiberIntoH f)
    (rhoLocal (inclQ q) ((rhoLocal (localFiberIntoH f)).symm
      (rhoLocal (localFiberIntoH f) x))) = _
  rw [LinearEquiv.symm_apply_apply, hq]

/-- All twelve transported Pauli elements fix the complete genuine middle vector. -/
theorem generatedEighth_pauli_final_full_fixed (j : Fin 12) :
    rhoLocal (inclQ (generatedEighthSpinPauliCache j 7)) generatedEighthMiddleAxis =
      generatedEighthMiddleAxis := by
  rw [← generatedEighth_spin_pauli_transport]
  exact transported_fix generatedEighthLocalFiber (generatedEighthSpinPauliInitial j)
    generatedOddAxis (generatedEighth_pauli_initial_full_fixed j)

/-- The genuine odd pure modulation fixes every middle coordinate. -/
theorem generatedEighth_middle_odd_modulation_full_fixed :
    rhoLocal (inclQ (cocodeQ (golayLabelCoefficients 3079)))
      generatedEighthMiddleAxis = generatedEighthMiddleAxis := by
  rw [← generatedEighth_spin_pauli_odd_modulation]
  simp only [map_mul, LinearEquiv.mul_apply, generatedEighth_pauli_final_full_fixed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
