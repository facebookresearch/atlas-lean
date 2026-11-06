/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSelectedOctad
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadTransitivity

/-! Genuine five-point Mathieu transitivity transports the selected octad while fixing
all three original seventh triangle coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Two actual octads containing any five distinct coordinates are equal. -/
theorem leechSeventh_octad_unique_five (c d : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hd : d ∈ golayCode)
    (hwc : ∑ i, (c i).val = 8) (hwd : ∑ i, (d i).val = 8)
    (a : Fin 5 → Fin 24) (ha : Function.Injective a)
    (hcd : ∀ j, c (a j) = 1 ∧ d (a j) = 1) : c = d := by
  obtain ⟨q, hq⟩ := golayAutomorphism_maps_firstFive a ha
  have he : golayPermute q.val⁻¹ c = golayPermute q.val⁻¹ d := by
    apply golayOctad_unique_through_first_five _ _ ((q⁻¹).property c |>.mp hc)
      ((q⁻¹).property d |>.mp hd)
    · exact (Equiv.sum_comp q.val (fun i => (c i).val)).trans hwc
    · exact (Equiv.sum_comp q.val (fun i => (d i).val)).trans hwd
    · intro i hi
      let j : Fin 5 := ⟨i.val, hi⟩
      have hj : Fin.castAdd 19 j = i := Fin.ext rfl
      have hqi : q.val i = a j := by rw [← hj, hq j]
      change c (q.val i) = 1 ∧ d (q.val i) = 1
      rw [hqi]
      exact hcd j
  have h := congrArg (golayPermute q.val) he
  simpa only [← golayPermute_mul, mul_inv_cancel, golayPermute_one] using h

set_option maxHeartbeats 4000000 in
-- Five literal coordinates are matched against the original selected octad addresses.
/-- An actual Golay permutation transports the selected octad to the seventh section,
while fixing each distinguished triangle coordinate. -/
theorem leechSeventh_octad_triangle_transport : ∃ p : golayAutomorphismSubgroup,
    p.val 16 = 16 ∧ p.val 17 = 17 ∧ p.val 19 = 19 ∧
      golayPermute p.val (golayOctadWord generatedFifthFlagOctad) =
        golayOctadWord generatedSeventhSectionOctad := by
  let a : Fin 5 → Fin 24 := ![16, 17, 19, 0, 1]
  let b : Fin 5 → Fin 24 := ![16, 17, 19, 12, 13]
  have ha : Function.Injective a := by decide +kernel
  have hb : Function.Injective b := by decide +kernel
  obtain ⟨p, hp⟩ := golayAutomorphism_five_transitive a b ha hb
  refine ⟨p, hp 0, hp 1, hp 2, ?_⟩
  let c := golayOctadWord generatedFifthFlagOctad
  let d := golayOctadWord generatedSeventhSectionOctad
  have hc : c ∈ golayCode := golayOctadWord_mem_code _
  have hd : d ∈ golayCode := golayOctadWord_mem_code _
  have hwc : ∑ i, (c i).val = 8 := golayOctadWord_weight _
  have hwd : ∑ i, (d i).val = 8 := golayOctadWord_weight _
  have hpc : golayPermute p.val c ∈ golayCode := (p.property c).mp hc
  have hwp : ∑ i, (golayPermute p.val c i).val = 8 := by
    exact (Equiv.sum_comp p.val.symm (fun i => (c i).val)).trans hwc
  have hboth : ∀ j, golayPermute p.val c (b j) = 1 ∧ d (b j) = 1 := by
    intro j
    constructor
    · change c (p.val.symm (b j)) = 1
      rw [← hp j, p.val.symm_apply_apply]
      change golayOctadWord generatedFifthFlagOctad (a j) = 1
      rw [generatedFifth_flag_word_coordinate]
      revert j
      decide +kernel
    · change golayOctadWord generatedSeventhSectionOctad (b j) = 1
      rw [golayOctadWord, generatedSeventh_section_octad_label, golayLabelEncoder_boolean]
      revert j
      decide +kernel
  exact leechSeventh_octad_unique_five (golayPermute p.val c) d hpc hd hwp hwd b hb hboth

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
