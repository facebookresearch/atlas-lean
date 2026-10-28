/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinSupportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddQStabilizer

/-! Actual Pauli products fix every coordinate of the genuine middle axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual vector between the local word and the last original triality. -/
def generatedSixthMiddleAxis : GriessSpace :=
  rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis

/-- The genuine extraspecial stabilizer of the complete middle vector. -/
def generatedSixthMiddleAxisQStabilizer : Subgroup Q :=
  (MulAction.stabilizer H generatedSixthMiddleAxis).comap inclQ

/-- Each initial Pauli element fixes the entire original odd axis. -/
theorem generatedSixth_pauli_initial_full_fixed (j : Fin 12) :
    rhoLocal (inclQ (generatedSixthSpinPauliInitial j)) generatedOddAxis =
      generatedOddAxis :=
  generatedOddSpinStateStabilizer_le_axis (generatedSixth_spin_pauli_initial_fixed j)

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
theorem generatedSixth_pauli_final_full_fixed (j : Fin 12) :
    rhoLocal (inclQ (generatedSixthSpinPauliCache j 8)) generatedSixthMiddleAxis =
      generatedSixthMiddleAxis := by
  rw [← generatedSixth_spin_pauli_transport]
  exact transported_fix generatedSixthLocalFiber (generatedSixthSpinPauliInitial j)
    generatedOddAxis (generatedSixth_pauli_initial_full_fixed j)

/-- Every selected rank-nine Pauli product fixes all middle coordinates. -/
theorem generatedSixth_pauli_product_full_fixed (a : Fin 9 → ZMod 2) :
    rhoLocal (inclQ (generatedSixthSpinPauliProduct a)) generatedSixthMiddleAxis =
      generatedSixthMiddleAxis := by
  change generatedSixthSpinPauliProduct a ∈ generatedSixthMiddleAxisQStabilizer
  apply generatedSixthMiddleAxisQStabilizer.list_prod_mem
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  apply generatedSixthMiddleAxisQStabilizer.pow_mem
  exact generatedSixth_pauli_final_full_fixed (generatedSixthSpinPauliIndependent j)

/-- The three pure support modulations fix the complete middle vector. -/
theorem generatedSixth_support_modulation_full_fixed (j : Fin 3) :
    rhoLocal (inclQ (cocodeQ
      (golayLabelCoefficients (generatedSixthSpinSupportModulation j))))
      generatedSixthMiddleAxis = generatedSixthMiddleAxis := by
  rw [← generatedSixth_spin_support_pauli_certificate]
  change generatedSixthSpinSupportPauliProduct j ∈ generatedSixthMiddleAxisQStabilizer
  apply generatedSixthMiddleAxisQStabilizer.list_prod_mem
  intro q hq
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hq
  apply generatedSixthMiddleAxisQStabilizer.pow_mem
  exact generatedSixth_pauli_final_full_fixed k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
