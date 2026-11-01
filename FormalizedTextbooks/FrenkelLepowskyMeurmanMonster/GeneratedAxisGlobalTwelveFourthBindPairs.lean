/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthBindSelf

/-! Class-specific reverse relations and the unmerged Fourth roots one, twelve and fourteen.

At an unmerged root the two triality images lie in different local classes. An identification
at any coset representative related to the root by a Fourth stabilizer word places one image of
the root in the identified class, without fixing the sign. Two such statements for two different
classes with disjoint local orbits bind both images. The identifications are hypotheses here;
none is asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem pairs_orbit_of_local {w y z : GriessSpace} (k : H)
    (hy : y ∈ MulAction.orbit H w) (he : y = rhoLocal k z) : z ∈ MulAction.orbit H w := by
  have h := MulAction.mem_orbit_of_mem_orbit k⁻¹ hy
  rw [he] at h
  change rhoLocal k⁻¹ (rhoLocal k z) ∈ _ at h
  rwa [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h

/-- One class membership at a related `k` gives one class membership at the forest root. -/
theorem generatedAxisGlobalTwelveFourth_reverse_pair_orbit (w : GriessSpace) (i : Fin 16)
    (k c : H) (hc : c ∈ generatedFourthLocalAxisStabilizer)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalTwelveFourthRoot i) =
      generatedAxisGlobalBinaryRoot k)
    (hk : sExtra (rhoLocal k generatedFourthAxis) ∈ MulAction.orbit H w ∨
      sExtra⁻¹ (rhoLocal k generatedFourthAxis) ∈ MulAction.orbit H w) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        MulAction.orbit H w ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        MulAction.orbit H w := by
  have hfix : rhoLocal c generatedFourthAxis = generatedFourthAxis := hc
  rcases generatedAxisGlobalTwelve_root_relation_pair generatedFourthAxis k
      (generatedAxisGlobalTwelveFourthRootLocal i) c hfix hroot with
    ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩ | ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩
  · rcases hk with hk | hk
    · exact Or.inl (pairs_orbit_of_local k1 hk h1)
    · exact Or.inr (pairs_orbit_of_local k2 hk h2)
  · rcases hk with hk | hk
    · exact Or.inr (pairs_orbit_of_local k1 hk h1)
    · exact Or.inl (pairs_orbit_of_local k2 hk h2)

/-- Local orbits of two vectors with different finite cardinalities are disjoint. -/
theorem generatedAxisGlobalTwelveFourth_orbit_disjoint_of_card {u w : GriessSpace} {m n : ℕ}
    (hu : Nat.card (MulAction.orbit H u) = m) (hw : Nat.card (MulAction.orbit H w) = n)
    (hmn : m ≠ n) : Disjoint (MulAction.orbit H u) (MulAction.orbit H w) := by
  refine (MulAction.orbit.eq_or_disjoint u w).resolve_left ?_
  intro he
  apply hmn
  rw [← hu, ← hw, he]

/-- Two one-sign statements for disjoint classes bind both triality images. -/
theorem generatedAxisGlobalTwelveFourth_both_of_disjoint {ι : Type*} (v : ι → GriessSpace)
    {a b : GriessSpace} {i j : ι}
    (hdisj : Disjoint (MulAction.orbit H (v i)) (MulAction.orbit H (v j)))
    (hi : a ∈ MulAction.orbit H (v i) ∨ b ∈ MulAction.orbit H (v i))
    (hj : a ∈ MulAction.orbit H (v j) ∨ b ∈ MulAction.orbit H (v j)) :
    a ∈ generatedLocalOrbitUnion v ∧ b ∈ generatedLocalOrbitUnion v := by
  have hmem : ∀ {x : GriessSpace} {l : ι}, x ∈ MulAction.orbit H (v l) →
      x ∈ generatedLocalOrbitUnion v := by
    intro x l hx
    obtain ⟨t, ht⟩ := hx
    exact ⟨l, t, ht⟩
  rcases hi with ha | hb <;> rcases hj with ha' | hb'
  · exact absurd ha' (Set.disjoint_left.mp hdisj ha)
  · exact ⟨hmem ha, hmem hb'⟩
  · exact ⟨hmem ha', hmem hb⟩
  · exact absurd hb' (Set.disjoint_left.mp hdisj hb)

/-- One-xi coset representative words at the unmerged roots one and twelve. -/
def generatedAxisGlobalTwelveFourthPairWord : Fin 2 → List (Fin 10) :=
  ![[0, 7, 9, 7], [0, 7, 3, 7]]

/-- The corresponding actual local elements. -/
def generatedAxisGlobalTwelveFourthPairLocal (i : Fin 2) : H :=
  ((generatedAxisGlobalTwelveFourthPairWord i).map generatedAxisGlobalOddSourceLocalLetter).prod

/-- The forest roots of the two representatives. -/
def generatedAxisGlobalTwelveFourthPairRoot : Fin 2 → Fin 16 := ![1, 12]

/-- Binary root masks of the two representatives. -/
def generatedAxisGlobalTwelveFourthPairMask : Fin 2 → ℕ := ![4614144, 4587520]

/-- Generator words carrying each forest root to the binary root of its representative. -/
def generatedAxisGlobalTwelveFourthPairPath : Fin 2 → List (Fin 5) :=
  ![[0, 2, 3, 1, 2, 0], [0, 3]]

set_option maxHeartbeats 20000000 in
-- Evaluate two source words and two generator words on their masks.
/-- The finite mask identities for the two representatives. -/
theorem generatedAxisGlobalTwelveFourthPair_certificate : ∀ i : Fin 2,
    (generatedAxisGlobalTwelveFourthPairWord i).foldr (fun l x =>
        generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
      (generatedAxisGlobalTwelveFourthPairMask i) = 2048 ∧
    (generatedAxisGlobalTwelveFourthPairPath i).foldr (fun k m =>
        generatedAxisGlobalMaskColumnAction (generatedAxisGlobalTwelveFourthBinaryColumns k) m)
      (generatedAxisGlobalTwelveFourthRootMask (generatedAxisGlobalTwelveFourthPairRoot i)) =
      generatedAxisGlobalTwelveFourthPairMask i := by
  decide +kernel

/-- Each representative is related to its forest root by an actual Fourth stabilizer word. -/
theorem generatedAxisGlobalTwelveFourthPair_relation (i : Fin 2) :
    generatedAxisGlobalBinaryAct
        (generatedAxisGlobalTwelveFourthGeneratorWord (generatedAxisGlobalTwelveFourthPairPath i))
        (generatedAxisGlobalTwelveFourthRoot (generatedAxisGlobalTwelveFourthPairRoot i)) =
      generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveFourthPairLocal i) := by
  apply Subtype.ext
  rw [generatedAxisGlobalTwelveFourthGeneratorWord_binary _ _ _
      (generatedAxisGlobalTwelveFourthRoot_val _),
    (generatedAxisGlobalTwelveFourthPair_certificate i).2,
    generatedAxisGlobalTwelveFourthPairLocal,
    generatedAxisGlobalTwelveFourth_sourceWord_root _ _
      (generatedAxisGlobalTwelveFourthPair_certificate i).1]

/-- The Fourth and Fifth local orbits are disjoint (both lengths are closed). -/
theorem generatedAxisGlobalTwelveFourth_fifth_disjoint :
    Disjoint (MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3))
      (MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 4)) :=
  generatedAxisGlobalTwelveFourth_orbit_disjoint_of_card (generatedCountedAxisOrbit_card 3)
    generatedFifth_local_axis_orbit_card (by decide)

/-- The Seventh and Sixth local orbits are disjoint (both lengths are closed). -/
theorem generatedAxisGlobalTwelveFourth_seventh_sixth_disjoint :
    Disjoint (MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 6))
      (MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 5)) :=
  generatedAxisGlobalTwelveFourth_orbit_disjoint_of_card generatedSeventhLocalAxisOrbit_card
    generatedSixth_local_axis_orbit_card (by decide)

/-- A self-identification at the root-one representative puts one image at root one in the
Fourth class. -/
theorem generatedAxisGlobalTwelveFourth_root1_fourth_of_self
    (hid : ∃ g : H, sExtra (rhoLocal (generatedAxisGlobalTwelveFourthPairLocal 0)
      generatedFourthAxis) = rhoLocal g generatedFourthAxis) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3) ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3) := by
  obtain ⟨g, hg⟩ := hid
  exact generatedAxisGlobalTwelveFourth_reverse_pair_orbit _ 1 _ _
    (generatedAxisGlobalTwelveFourthGeneratorWord_mem _)
    (generatedAxisGlobalTwelveFourthPair_relation 0) (Or.inl ⟨g, hg.symm⟩)

/-- A self-identification at the root-twelve representative puts one image at root twelve in
the Fourth class. -/
theorem generatedAxisGlobalTwelveFourth_root12_fourth_of_self
    (hid : ∃ g : H, sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthPairLocal 1)
      generatedFourthAxis) = rhoLocal g generatedFourthAxis) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3) ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3) := by
  obtain ⟨g, hg⟩ := hid
  exact generatedAxisGlobalTwelveFourth_reverse_pair_orbit _ 12 _ _
    (generatedAxisGlobalTwelveFourthGeneratorWord_mem _)
    (generatedAxisGlobalTwelveFourthPair_relation 1) (Or.inr ⟨g, hg.symm⟩)

/-- Root one: one image Fourth-class and one image Fifth-class bind both images. -/
theorem generatedAxisGlobalTwelveFourth_root1_of_classes
    (hF : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3) ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3))
    (hV : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 4) ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 4)) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelveFourth_both_of_disjoint _
    generatedAxisGlobalTwelveFourth_fifth_disjoint hF hV

/-- Root twelve: one image Fourth-class and the forward image Odd-class bind the inverse image. -/
theorem generatedAxisGlobalTwelveFourth_root12_of_classes
    (hF : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3) ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3))
    (hodd : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
      MulAction.orbit H generatedOddAxis) :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (generatedAxisGlobalTwelveFourth_both_of_disjoint generatedAxisGlobalTwelveRepresentative
    (i := 3) (j := 2) generatedAxisGlobalTwelveFourth_odd_disjoint hF (Or.inl hodd)).2

/-- Root fourteen: one image Seventh-class and one image Sixth-class bind both images. -/
theorem generatedAxisGlobalTwelveFourth_root14_of_classes
    (h7 : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 14) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 6) ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 14) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 6))
    (h6 : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 14) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 5) ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 14) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 5)) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 14) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 14) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelveFourth_both_of_disjoint _
    generatedAxisGlobalTwelveFourth_seventh_sixth_disjoint h7 h6

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
