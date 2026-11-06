/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSpinTranslationLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddQStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit

/-! Middle spin fixation suffices for genuine Pauli fixation of the full middle axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem transported_axis_fixed (f : localFiberSubgroup) (q : Q) (x : GriessSpace)
    (hq : rhoLocal (inclQ q) x = x) :
    rhoLocal (inclQ (spinConjugation f.val.1 q)) (rhoLocal (localFiberIntoH f) x) =
      rhoLocal (localFiberIntoH f) x := by
  rw [inclQ_spinConjugation, map_mul, map_mul, map_inv]
  simp only [LinearEquiv.mul_apply]
  change rhoLocal (localFiberIntoH f)
    (rhoLocal (inclQ q) ((rhoLocal (localFiberIntoH f)).symm
      (rhoLocal (localFiberIntoH f) x))) = _
  rw [LinearEquiv.symm_apply_apply, hq]

private theorem inverse_spin_fixed (s : SpinHolomorph) (q : Q) (f : SpinSpace)
    (hf : spinRepresentation q (s.val f) = s.val f) :
    spinRepresentation (spinConjugation s⁻¹ q) f = f := by
  rw [spinConjugation_representation]
  change s.val.symm (spinRepresentation q (s.val f)) = f
  rw [hf, LinearEquiv.symm_apply_apply]

/-- Every full-phase Pauli fixing the actual middle spin state fixes all its Griess coordinates. -/
theorem generatedSeventh_middle_spin_fixed_axis (q : Q)
    (hq : spinRepresentation q generatedSeventhSpinState = generatedSeventhSpinState) :
    rhoLocal (inclQ q)
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis) =
      rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis := by
  let s := generatedSeventhLocalFiber.val.1
  let q' := spinConjugation s⁻¹ q
  have hs : spinRepresentation q' (generatedOddSpinState 0 1 0) =
      generatedOddSpinState 0 1 0 := by
    exact inverse_spin_fixed s q (generatedOddSpinState 0 1 0) hq
  have ha : rhoLocal (inclQ q') generatedOddAxis = generatedOddAxis :=
    generatedOddSpinStateStabilizer_le_axis hs
  have hb : spinConjugation s q' = q := by
    change spinConjugation s ((spinConjugation s⁻¹) q) = q
    rw [map_inv]
    exact (spinConjugation s).apply_symm_apply q
  have h := transported_axis_fixed generatedSeventhLocalFiber q' generatedOddAxis ha
  rw [hb] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
