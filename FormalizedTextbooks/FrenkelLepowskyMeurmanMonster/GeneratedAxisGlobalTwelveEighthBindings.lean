/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthFamily

/-! Convenient forms of Eighth root bindings.

A binding may match root masks by any word in the sixteen Eighth letters instead of an explicit
whole-axis fixer: every such word lies in the projected Eighth-axis stabilizer, hence is the
projection of an actual element fixing the whole Eighth axis. The mask equation itself is then a
finite computation with the literal letter columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every word in the sixteen Eighth letters is the projection of an actual whole-axis fixer. -/
theorem generatedAxisGlobalTwelveEighthWord_lift (w : List (Fin 16)) :
    ∃ c : H, c ∈ generatedEighthLocalAxisStabilizer ∧
      projH c = generatedAxisGlobalTwelveEighthWord w := by
  obtain ⟨⟨c, hc⟩, he⟩ := generatedAxisGlobalTwelveEighthWord_mem w
  exact ⟨c, hc, he⟩

/-- An Eighth root binding from a letter word carrying the root mask to the binary root of `h`. -/
theorem generatedAxisGlobalTwelveEighthRootBound_of_word (j : Fin 37) (h : H) (w : List (Fin 16))
    (hroot : co1BinaryAction (generatedAxisGlobalTwelveEighthWord w)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveEighthRootMask j)) =
        (generatedAxisGlobalBinaryRoot h).val)
    (hpos : sExtra (rhoLocal h generatedEighthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : sExtra⁻¹ (rhoLocal h generatedEighthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveEighthRootBound j := by
  obtain ⟨c, hc, he⟩ := generatedAxisGlobalTwelveEighthWord_lift w
  exact ⟨h, c, hc, by rw [he]; exact hroot, hpos, hneg⟩

/-- The mask form of a letter-word root matching: a finite equality of 24-bit masks. -/
theorem generatedAxisGlobalTwelveEighthWord_root_mask (j : Fin 37) (h : H) (w : List (Fin 16))
    (m : ℕ) (hm : (generatedAxisGlobalBinaryRoot h).val = monsterCo1GeometryBinaryMaskDecode m)
    (hw : eighthForestWordApply w (generatedAxisGlobalTwelveEighthRootMask j) = m) :
    co1BinaryAction (generatedAxisGlobalTwelveEighthWord w)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveEighthRootMask j)) =
        (generatedAxisGlobalBinaryRoot h).val := by
  rw [generatedAxisGlobalTwelveEighthWord_action, hw, hm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
