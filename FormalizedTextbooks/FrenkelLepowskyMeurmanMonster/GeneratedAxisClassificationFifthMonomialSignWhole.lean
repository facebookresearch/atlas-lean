/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignPair
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalForm

/-! Exact support soundness for the full actual Q-corrected source sign action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Fixing the 56 actual outgoing octad families forces fixation of the entire short block. -/
theorem generatedFifth_sign_short_fixed_of_octads (k : Fin 12)
    (ho : ∀ j : Fin 56, ∀ e : Fin 64,
      (griessConwayEncode (rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber k))
        generatedFifthAxis)).2.1 (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) =
          (griessConwayEncode generatedFifthAxis).2.1
            (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e)))) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber k))
      generatedFifthAxis)).2.1 = (griessConwayEncode generatedFifthAxis).2.1 := by
  classical
  let X := (griessConwayEncode generatedFifthAxis).2.1
  let Y := (griessConwayEncode (rhoLocal
    (localFiberIntoH (generatedFifthSignCorrectedFiber k)) generatedFifthAxis)).2.1
  have hn : (∑ r, Y r ^ 2) = ∑ r, X r ^ 2 := by
    dsimp [Y, X]
    rw [generatedFourth_local_short]
    have h := localShortRepresentation_pairing (generatedFifthSignCorrectedFiber k) X X
    change (∑ r, localShortOperator (generatedFifthSignCorrectedFiber k) X r *
      localShortOperator (generatedFifthSignCorrectedFiber k) X r) = ∑ r, X r * X r at h
    simpa only [X, pow_two] using h
  apply generatedFourth_real_eq_of_norm_support X Y hn
  intro r hr
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · exact generatedFifth_sign_corrected_pair k s p
  · have hx : ∃ j : Fin 56, generatedFifthEvenRootOctad j = o := by
      by_contra h
      exact hr (generatedFifth_final_octad_zero o e h)
    obtain ⟨j, rfl⟩ := hx
    exact ho j e
  · exact False.elim (hr (generatedFifth_final_odd_zero d i))

/-- Complete matrix, short and tensor fixation gives the genuine original axis equality. -/
theorem generatedFifth_sign_full_fixed_of_short (k : Fin 12)
    (hs : (griessConwayEncode (rhoLocal
      (localFiberIntoH (generatedFifthSignCorrectedFiber k)) generatedFifthAxis)).2.1 =
        (griessConwayEncode generatedFifthAxis).2.1) :
    rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber k)) generatedFifthAxis =
      generatedFifthAxis := by
  apply Function.LeftInverse.injective griessConwayDecode_encode
  apply Prod.ext
  · exact generatedFifth_sign_corrected_matrix (generatedFifthSignCode k) 0
      (generatedFifthSignCorrection k)
  · exact Prod.ext hs (generatedFifth_sign_encoded_tensor_fixed k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
