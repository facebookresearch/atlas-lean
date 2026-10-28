/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhBitsetCover
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhForestRoots

/-! Genuine Seventh-stabilizer coverage of the binary Ω orbit by the 23 type-four forest roots.

The four Seventh forest letters lie in the projected Seventh-axis stabilizer, so the checked
bitset forest places every singular mask in the projected-stabilizer orbit of a forest root. A
root met by a point of the binary Ω orbit is one of the 23 type-four roots, and every projected
element lifts to an actual whole-axis fixer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every point of the binary Ω orbit is an actual Seventh-stabilizer image of one of the 23
type-four forest roots. -/
theorem generatedAxisGlobalTwelveSeventhBinary_cover
    (hlong : ∀ i : Fin 23, monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveSeventhLongRootMask i) ∈ generatedAxisGlobalBinaryOrbit) :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 23, ∃ c : H,
      c ∈ generatedSeventhLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c ⟨_, hlong i⟩ = x := by
  intro x
  let b := (generatedAxisGlobalMaskFiniteEquiv 24).symm x.val
  have hb : monsterCo1GeometryBinaryMaskDecode b.val = x.val :=
    (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
  have hlt : b.val < 16777216 := b.isLt
  have hs : generatedAxisGlobalMaskSingular b.val = true := by
    rw [generatedAxisGlobalMaskSingular_iff, hb]
    exact generatedAxisGlobalBinary_squareQuad x
  obtain ⟨m, hm, c, hc, he⟩ := seventhBitset_reached generatedSeventhProjectedAxisStabilizer
    seventhForestLetter_mem b.val hlt hs
  rw [hb] at he
  obtain ⟨k, hk⟩ := (generatedAxisGlobalTwelveSeventhForestRootMasks_mem m).mp hm
  have hmx : monsterCo1GeometryBinaryMaskDecode (n := 24) m = co1BinaryAction c⁻¹ x.val := by
    rw [← he, map_inv]
    exact (LinearEquiv.symm_apply_apply _ _).symm
  have hmo : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveSeventhForestRootMask k) ∈ generatedAxisGlobalBinaryOrbit := by
    rw [hk, hmx]
    obtain ⟨g, hg⟩ := x.property
    refine ⟨c⁻¹ * g, ?_⟩
    change co1BinaryAction (c⁻¹ * g) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
    rw [map_mul, LinearEquiv.mul_apply]
    exact congrArg (co1BinaryAction c⁻¹) hg
  have h10 := generatedAxisGlobalTwelveSeventhForestRoot_mem_orbit k hmo
  let i : Fin 23 := ⟨k.val - 12, by omega⟩
  have hi : generatedAxisGlobalTwelveSeventhLongRootMask i = m := by
    have hk0 : k.val ≠ 0 := by omega
    have hk10 : ¬k.val < 12 := by omega
    simp only [generatedAxisGlobalTwelveSeventhForestRootMask, hk0, hk10, ↓reduceDIte] at hk
    exact hk
  obtain ⟨h, hh⟩ := hc
  refine ⟨i, h.val, h.property, ?_⟩
  apply Subtype.ext
  change co1BinaryAction (projH h.val) (monsterCo1GeometryBinaryMaskDecode (n := 24)
    (generatedAxisGlobalTwelveSeventhLongRootMask i)) = x.val
  have hh' : projH h.val = c := hh
  rw [hh', hi, he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
