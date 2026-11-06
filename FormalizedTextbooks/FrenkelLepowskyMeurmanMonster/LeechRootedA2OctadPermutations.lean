/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2OctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadTransitivity

/-! Actual Mathieu permutations of the octads containing a fixed coordinate pair. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- An actual octad containing0 and1 moves to the standard octad while fixing both coordinates. -/
theorem leechRootedA2Octad_permutation_to_standard (d : Fin 759)
    (h0 : (golayEncodedMask (golayOctadLabel d).val).testBit 0 = true)
    (h1 : (golayEncodedMask (golayOctadLabel d).val).testBit 1 = true) :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = 0 ∧ p.val 1 = 1 ∧
      golayPermute p.val (golayEncoder (golayLabelCoefficients (golayOctadLabel d))) =
        golayStandardOctad := by
  let c := golayEncoder (golayLabelCoefficients (golayOctadLabel d))
  have hc : c ∈ golayCode := ⟨_, rfl⟩
  have hw : ∑ i, (c i).val = 8 := by
    simp_rw [c, golayLabelEncoder_match]
    exact (golayMaskSupport_card _).symm.trans (golayOctad_support_card d)
  let a : Fin 5 → Fin 24 := fun j => golayOctadCoordinate d (Fin.castAdd 3 j)
  let b : Fin 5 → Fin 24 := fun j => Fin.castAdd 19 j
  have ha : Function.Injective a :=
    (golayOctadCoordinate_injective d).comp (by
      intro j k h
      exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h))
  have hb : Function.Injective b := by
    intro j k h
    exact Fin.ext (congrArg (fun i : Fin 24 => i.val) h)
  obtain ⟨p, hp⟩ := golayAutomorphism_five_transitive a b ha hb
  have hfirst := leechRootedA2Octad_first_coordinates d h0 h1
  have hp0 : p.val 0 = 0 := by
    have he := hp 0
    change p.val (golayOctadCoordinate d 0) = 0 at he
    rwa [hfirst.1] at he
  have hp1 : p.val 1 = 1 := by
    have he := hp 1
    change p.val (golayOctadCoordinate d 1) = 1 at he
    rwa [hfirst.2] at he
  refine ⟨p, hp0, hp1, golayOctad_unique_through_first_five _ _
    ((p.property c).mp hc) golayStandardOctad_mem ?_ golayStandardOctad_weight ?_⟩
  · exact (Equiv.sum_comp p.val.symm (fun i => (c i).val)).trans hw
  · intro i hi
    let j : Fin 5 := ⟨i.val, hi⟩
    have hbi : b j = i := Fin.ext rfl
    have hpi : p.val.symm i = a j := by
      rw [← hbi, ← hp j, p.val.symm_apply_apply]
    refine ⟨?_, ?_⟩
    · change c (p.val.symm i) = 1
      rw [hpi]
      change golayEncoder (golayLabelCoefficients (golayOctadLabel d))
        (golayOctadCoordinate d (Fin.castAdd 3 j)) = 1
      apply ZMod.val_injective
      rw [golayLabelEncoder_match, golayOctadCoordinate_mem]
      rfl
    · simp [golayStandardOctad, show i.val < 8 by omega]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
