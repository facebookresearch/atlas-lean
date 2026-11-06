/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthFamily

/-! Convenient forms of Ninth root bindings.

A binding may match root masks by any word in the six Ninth letters instead of an explicit
whole-axis fixer: every such word lies in the projected Ninth-axis stabilizer, hence is the
projection of an actual element fixing the whole Ninth axis. The mask equation itself is then a
finite computation with the proved letter columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every word in the six Ninth letters is the projection of an actual whole-axis fixer. -/
theorem generatedAxisGlobalTwelveNinthWord_lift (w : List (Fin 6)) :
    ∃ c : H, c ∈ generatedNinthLocalAxisStabilizer ∧
      projH c = generatedNinthLowerSpinThreeProjectionWord w := by
  have hw : generatedNinthLowerSpinThreeProjectionWord w ∈
      generatedNinthProjectedAxisStabilizer := by
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    exact generatedAxisGlobalTwelveNinthLetter_mem g
  obtain ⟨⟨c, hc⟩, he⟩ := hw
  exact ⟨c, hc, he⟩

/-- A Ninth root binding from a letter word carrying the root mask to the binary root of `h`. -/
theorem generatedAxisGlobalTwelveNinthRootBound_of_word (j : Fin 8) (h : H) (w : List (Fin 6))
    (hroot : co1BinaryAction (generatedNinthLowerSpinThreeProjectionWord w)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveNinthRootMask j)) =
        (generatedAxisGlobalBinaryRoot h).val)
    (hpos : sExtra (rhoLocal h generatedNinthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : sExtra⁻¹ (rhoLocal h generatedNinthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveNinthRootBound j := by
  obtain ⟨c, hc, he⟩ := generatedAxisGlobalTwelveNinthWord_lift w
  exact ⟨h, c, hc, by rw [he]; exact hroot, hpos, hneg⟩

/-- The mask form of a letter-word root matching: a finite equality of 24-bit masks. -/
theorem generatedAxisGlobalTwelveNinthWord_root_mask (j : Fin 8) (h : H) (w : List (Fin 6))
    (m : ℕ) (hm : (generatedAxisGlobalBinaryRoot h).val = monsterCo1GeometryBinaryMaskDecode m)
    (hw : generatedNinthLowerSpinThreeProjectionMaskWord w
      (generatedAxisGlobalTwelveNinthRootMask j) = m) :
    co1BinaryAction (generatedNinthLowerSpinThreeProjectionWord w)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveNinthRootMask j)) =
        (generatedAxisGlobalBinaryRoot h).val := by
  rw [generatedNinth_lower_spin_three_projection_word_action, hw, hm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
