/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowComplete
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotBounds
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingClasses

/-! The complete original signed source replay identifies all actual octad markings. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exactly the eight original marked signs in the distinguished octad have absolute
coefficient one eighth, using every original source-row certificate. -/
theorem generatedNinth_actual_octad_marking_iff (o : Fin 759) (e : Fin 64) :
    |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
      o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns :=
  generatedNinth_final_octad_marking_iff_of_certificates
    generatedNinth_short_row_certificate_all o e

/-- The full actual large-coefficient short-class carrier equals the original catalogue. -/
theorem generatedNinth_actual_marked_short_classes_eq :
    griessShortClass '' {r : GriessShortIndex |
      |(griessConwayEncode generatedNinthAxis).2.1 r| = 1 / 8} =
        generatedNinthMarkedShortClasses :=
  generatedNinth_marked_short_classes_eq_of_octad_comparison
    generatedNinth_actual_octad_marking_iff

/-- The full actual large-coefficient carrier has exactly 144 short lattice classes. -/
theorem generatedNinth_actual_marked_short_classes_card :
    Nat.card (griessShortClass '' {r : GriessShortIndex |
      |(griessConwayEncode generatedNinthAxis).2.1 r| = 1 / 8}) = 144 := by
  rw [generatedNinth_actual_marked_short_classes_eq]
  exact generatedNinth_marked_short_classes_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
