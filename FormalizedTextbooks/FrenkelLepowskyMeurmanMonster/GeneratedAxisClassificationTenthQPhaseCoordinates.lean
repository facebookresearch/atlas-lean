/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisCharacters

/-! The actual short phase is the full original hyperbolic covector pairing. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Each original short phase pairs its full modulation-translation covector with the Q quotient. -/
theorem generatedTenth_Q_phase_coordinates (q : Q) (r : GriessShortIndex) :
    Multiplicative.toAdd (localAxisQPhase r q) =
      Fin.append (spinModulation (griessShortQ r)) (spinTranslation (griessShortQ r)) ⬝ᵥ
        Multiplicative.toAdd q.base := by
  rw [generatedFourthQShortBasis_character]
  unfold dotProduct
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  change spinDot (spinTranslation q) (spinModulation (griessShortQ r)) +
      spinDot (spinModulation q) (spinTranslation (griessShortQ r)) =
    (∑ i : Fin 12, spinModulation (griessShortQ r) i * spinTranslation q i) +
      ∑ i : Fin 12, spinTranslation (griessShortQ r) i * spinModulation q i
  apply congrArg₂ (fun a b : ZMod 2 => a + b)
  · unfold spinDot
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  · unfold spinDot
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
