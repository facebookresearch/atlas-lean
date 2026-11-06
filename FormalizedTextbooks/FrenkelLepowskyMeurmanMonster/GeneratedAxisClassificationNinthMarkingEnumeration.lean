/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortBaseRecognition

/-! The explicit144-label enumeration is precisely the original candidate marking catalogue.
All its labels represent different actual short classes; no actual octad coefficient is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- The explicit original marking-label table has no repeated address. -/
theorem generatedNinthMarkingLabel_injective : Function.Injective generatedNinthMarkingLabel := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The explicit table contains exactly the three families of candidate original markings. -/
theorem generatedNinth_marking_label_image :
    Finset.univ.image generatedNinthMarkingLabel = generatedNinthShortMarkings := by
  decide +kernel

/-- The table exhausts exactly the original candidate marking catalogue as a set. -/
theorem generatedNinth_marking_label_range :
    Set.range generatedNinthMarkingLabel =
      (generatedNinthShortMarkings : Set GriessShortIndex) := by
  rw [← generatedNinth_marking_label_image]
  ext r
  simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image, Finset.mem_univ,
    true_and]

/-- The144 enumerated preferred lifts have different actual binary short-vector classes. -/
theorem generatedNinth_marking_short_base_injective :
    Function.Injective (fun k : Fin 144 => (griessShortQ (generatedNinthMarkingLabel k)).base) :=
  generatedNinth_short_Q_base_injective.comp generatedNinthMarkingLabel_injective

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
