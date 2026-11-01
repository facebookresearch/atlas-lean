/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhTriangleMembership

/-! Genuine five-coordinate Mathieu transitivity within the seventh triangle stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Pointwise
set_option backward.isDefEq.respectTransparency false

/-- The five actual section coordinates outside the distinguished triangle. -/
def generatedSeventhFiveFrameCoordinates : Finset (Fin 24) := {12, 13, 14, 15, 18}

private def companion (t : Fin 24) : Fin 24 := if t = 12 then 13 else 12
private def addresses (t : Fin 24) : Fin 5 → Fin 24 := ![16, 17, 19, t, companion t]

private theorem addresses_injective : ∀ t : Fin 24,
    t ∈ generatedSeventhFiveFrameCoordinates → Function.Injective (addresses t) := by
  unfold generatedSeventhFiveFrameCoordinates addresses companion
  decide +kernel

private theorem addresses_in_octad (t : Fin 24) (ht : t ∈ generatedSeventhFiveFrameCoordinates) :
    ∀ j : Fin 5, golayOctadWord generatedSeventhSectionOctad (addresses t j) = 1 := by
  rw [golayOctadWord, generatedSeventh_section_octad_label]
  simp_rw [golayLabelEncoder_boolean]
  revert t
  unfold generatedSeventhFiveFrameCoordinates addresses companion
  decide +kernel

/-- Every complementary coordinate moves to any other by an actual triangle fixer. -/
theorem generatedSeventh_triangle_five_transitive (t u : Fin 24)
    (ht : t ∈ generatedSeventhFiveFrameCoordinates)
    (hu : u ∈ generatedSeventhFiveFrameCoordinates) :
    ∃ p : generatedSeventhTrianglePermutationSubgroup, p.val.val t = u := by
  obtain ⟨p, hp⟩ := golayAutomorphism_five_transitive (addresses t) (addresses u)
    (addresses_injective t ht) (addresses_injective u hu)
  have h0 : p.val 16 = 16 := hp 0
  have h1 : p.val 17 = 17 := hp 1
  have h2 : p.val 19 = 19 := hp 2
  have h3 : p.val t = u := hp 3
  let w := golayOctadWord generatedSeventhSectionOctad
  have hw : ∑ i, (w i).val = 8 := golayOctadWord_weight _
  have hcw : w ∈ golayCode := golayOctadWord_mem_code _
  have hpw : golayPermute p.val w ∈ golayCode := (p.property w).mp hcw
  have hpwt : ∑ i, (golayPermute p.val w i).val = 8 :=
    (Equiv.sum_comp p.val.symm (fun i => (w i).val)).trans hw
  have hboth : ∀ j, golayPermute p.val w (addresses u j) = 1 ∧ w (addresses u j) = 1 := by
    intro j
    constructor
    · change w (p.val.symm (addresses u j)) = 1
      rw [← hp j, p.val.symm_apply_apply]
      exact addresses_in_octad t ht j
    · exact addresses_in_octad u hu j
  have ho : golayPermute p.val w = w :=
    leechSeventh_octad_unique_five _ _ hpw hcw hpwt hw (addresses u)
      (addresses_injective u hu) hboth
  have htri : p • generatedSeventhTriangleCoordinates = generatedSeventhTriangleCoordinates := by
    rw [generatedSeventhTriangleCoordinates, Finset.smul_finset_def, Finset.image_insert,
      Finset.image_insert, Finset.image_singleton]
    change ({p.val 16, p.val 17, p.val 19} : Finset (Fin 24)) = _
    rw [h0, h1, h2]
  exact ⟨⟨p, (generatedSeventh_triangle_permutation_mem_iff p).mpr ⟨ho, htri⟩⟩, h3⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
