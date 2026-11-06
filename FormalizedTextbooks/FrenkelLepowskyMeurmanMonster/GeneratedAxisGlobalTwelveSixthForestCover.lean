/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthBitsetCover
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthForestRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitMembership
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthLocalOrder

/-! Genuine Sixth-stabilizer coverage of the binary Ω orbit by the ten type-four forest roots.

The fifteen Sixth spatial generators lie in the projected Sixth-axis stabilizer, so the checked
bitset forest places every singular mask in the projected-stabilizer orbit of a forest root. A
root met by a point of the binary Ω orbit is one of the ten type-four roots, and every projected
element lifts to an actual whole-axis fixer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The fifteen Sixth spatial generators lie in the projected Sixth-axis stabilizer. -/
theorem generatedAxisGlobalTwelveSixthGenerator_projected_mem (k : Fin 15) :
    sixthFrameOrbitOriginalGenerator k ∈ generatedSixthProjectedAxisStabilizer :=
  sixthFrameOrbit_generators_mem_of_corrected generatedSixth_corrected_generator_projected_mem k

/-- Every point of the binary Ω orbit is an actual Sixth-stabilizer image of one of the ten
type-four forest roots. -/
theorem generatedAxisGlobalTwelveSixthBinary_cover
    (hlong : ∀ i : Fin 10, monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveSixthLongRootMask i) ∈ generatedAxisGlobalBinaryOrbit) :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 10, ∃ c : H,
      c ∈ generatedSixthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c ⟨_, hlong i⟩ = x := by
  intro x
  let b := (generatedAxisGlobalMaskFiniteEquiv 24).symm x.val
  have hb : monsterCo1GeometryBinaryMaskDecode b.val = x.val :=
    (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
  have hlt : b.val < 16777216 := b.isLt
  have hs : generatedAxisGlobalMaskSingular b.val = true := by
    rw [generatedAxisGlobalMaskSingular_iff, hb]
    exact generatedAxisGlobalBinary_squareQuad x
  obtain ⟨m, hm, c, hc, he⟩ := sixthBitset_reached generatedSixthProjectedAxisStabilizer
    generatedAxisGlobalTwelveSixthGenerator_projected_mem b.val hlt hs
  rw [hb] at he
  obtain ⟨k, hk⟩ := (generatedAxisGlobalTwelveSixthForestRootMasks_mem m).mp hm
  have hmx : monsterCo1GeometryBinaryMaskDecode (n := 24) m = co1BinaryAction c⁻¹ x.val := by
    rw [← he, map_inv]
    exact (LinearEquiv.symm_apply_apply _ _).symm
  have hmo : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveSixthForestRootMask k) ∈ generatedAxisGlobalBinaryOrbit := by
    rw [hk, hmx]
    obtain ⟨g, hg⟩ := x.property
    refine ⟨c⁻¹ * g, ?_⟩
    change co1BinaryAction (c⁻¹ * g) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
    rw [map_mul, LinearEquiv.mul_apply]
    exact congrArg (co1BinaryAction c⁻¹) hg
  have h10 := generatedAxisGlobalTwelveSixthForestRoot_mem_orbit k hmo
  let i : Fin 10 := ⟨k.val - 10, by omega⟩
  have hi : generatedAxisGlobalTwelveSixthLongRootMask i = m := by
    have hk0 : k.val ≠ 0 := by omega
    have hk10 : ¬k.val < 10 := by omega
    simp only [generatedAxisGlobalTwelveSixthForestRootMask, hk0, hk10, ↓reduceDIte] at hk
    exact hk
  obtain ⟨h, hh⟩ := hc
  refine ⟨i, h.val, h.property, ?_⟩
  apply Subtype.ext
  change co1BinaryAction (projH h.val) (monsterCo1GeometryBinaryMaskDecode (n := 24)
    (generatedAxisGlobalTwelveSixthLongRootMask i)) = x.val
  have hh' : projH h.val = c := hh
  rw [hh', hi, he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
