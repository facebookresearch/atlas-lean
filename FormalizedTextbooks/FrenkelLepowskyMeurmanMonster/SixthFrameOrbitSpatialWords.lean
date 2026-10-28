/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsLeech

/-! Literal original spatial-word actions, retaining the actual left-action convention. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Fourteen original monomial generators followed by the Xi transporter and its inverse. -/
def sixthFrameOrbitMonomialIsometry (k : Fin 16) : leechIsomSubgroup :=
  if h : k.val < 10 then
    golaySignIsometry (sourceGeneratedSignCode (sixthFrameOrbitSignLabels ⟨k.val, h⟩))
  else if h : k.val < 14 then (generatedSixthRawGenerator ⟨k.val - 10, by omega⟩).val.2
  else if k.val = 14 then leechRootedA2SixthXiTransportFiber.val.2
  else leechRootedA2SixthXiTransportFiber.val.2⁻¹

/-- The original actual B permutation evaluates to its checked forward coordinate table. -/
theorem sixthFrameOrbit_B_forward (i : Fin 24) :
    leechRootedA2SixthPermutationTransport.val i = sixthFrameOrbitBForward i := by
  rw [leechRootedA2SixthPermutationTransport, leechRootedA2GeneratingWord_apply]
  exact (sixthFrameOrbit_word_check i).1

/-- Its actual inverse is the checked inverse table, proved by applying the genuine permutation. -/
theorem sixthFrameOrbit_B_inverse (i : Fin 24) :
    leechRootedA2SixthPermutationTransport.val.symm i = sixthFrameOrbitBInverse i := by
  apply leechRootedA2SixthPermutationTransport.val.injective
  rw [Equiv.apply_symm_apply, leechRootedA2SixthPermutationTransport,
    leechRootedA2GeneratingWord_apply]
  exact (sixthFrameOrbit_word_check i).2.1.symm

/-- The actual C transporter evaluates to its original forward table. -/
theorem sixthFrameOrbit_C_forward (i : Fin 24) :
    leechRootedA2SixthXiTransport.val i = sixthFrameOrbitCForward i := by
  rw [leechRootedA2SixthXiTransport, leechRootedA2GeneratingWord_apply]
  exact (sixthFrameOrbit_word_check i).2.2.1

/-- Its actual inverse is the checked original inverse table. -/
theorem sixthFrameOrbit_C_inverse (i : Fin 24) :
    leechRootedA2SixthXiTransport.val.symm i = sixthFrameOrbitCInverse i := by
  apply leechRootedA2SixthXiTransport.val.injective
  rw [Equiv.apply_symm_apply, leechRootedA2SixthXiTransport, leechRootedA2GeneratingWord_apply]
  exact (sixthFrameOrbit_word_check i).2.2.2.1.symm

/-- The actual root-pair swap has its checked inverse coordinate table. -/
theorem sixthFrameOrbit_swap_inverse (i : Fin 24) :
    leechRootedA2SixthPermutationWordSwap.val.symm i = sixthFrameOrbitSwapInverse i := by
  apply leechRootedA2SixthPermutationWordSwap.val.injective
  rw [Equiv.apply_symm_apply, leechRootedA2SixthPermutationWordSwap,
    leechRootedA2GeneratingWord_apply]
  exact (sixthFrameOrbit_word_check i).2.2.2.2.symm

/-- Every conjugated target's actual physical coordinate action has the certified input index. -/
theorem sixthFrameOrbit_raw_permutation_apply (k : Fin 3) (f : Fin 24 → ℝ) (i : Fin 24) :
    (generatedSixthRawGenerator (Fin.castAdd 2 k)).val.2.val f i =
      f (sixthFrameOrbitSpatialInput ⟨k.val + 10, by omega⟩ i) := by
  let n : Fin 83 := (![(0 : Fin 83), 1, 3] : Fin 3 → Fin 83) k
  have hr : (generatedSixthRawGenerator (Fin.castAdd 2 k)).val.2 =
      generatedSixthPermutationTransportFiber.val.2 * (representativePermutationFiber n).val.2 *
        generatedSixthPermutationTransportFiber.val.2⁻¹ := by
    fin_cases k <;> rfl
  have hb : generatedSixthPermutationTransportFiber.val.2 =
      golayPermutationIsometry leechRootedA2SixthPermutationTransport :=
    leechRootedA2GeneratingWordFiber_spatial _
  rw [hr, hb]
  change (representativePermutationFiber n).val.2.val
    (fun j => f (leechRootedA2SixthPermutationTransport.val j))
    (leechRootedA2SixthPermutationTransport.val.symm i) = _
  rw [representativePermutationLeech_apply, sixthFrameOrbit_B_inverse,
    sixthFrameOrbit_B_forward, sixthFrameOrbit_conjugated_input_check]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
