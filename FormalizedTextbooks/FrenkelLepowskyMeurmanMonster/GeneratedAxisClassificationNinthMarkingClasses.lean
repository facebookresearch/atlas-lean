/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingEnumeration

/-! The candidate marking catalogue determines144 distinct actual short lattice classes.
Their identification as all actual large-coefficient classes retains the missing octad
comparison explicitly. No spatial stabilizer or orbit order is asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The intrinsic lattice class at every enumerated original candidate marking. -/
def generatedNinthMarkingClass (k : Fin 144) : LeechModTwo :=
  griessShortClass (generatedNinthMarkingLabel k)

/-- The original candidate marking labels give different actual lattice classes. -/
theorem generatedNinthMarkingClass_injective : Function.Injective generatedNinthMarkingClass :=
  griessShortClass_injective.comp generatedNinthMarkingLabel_injective

/-- The actual short lattice classes of the original candidate marking catalogue. -/
def generatedNinthMarkedShortClasses : Set LeechModTwo :=
  griessShortClass '' (generatedNinthShortMarkings : Set GriessShortIndex)

/-- The144 class enumeration exhausts the original candidate marking classes. -/
theorem generatedNinth_marking_class_range :
    Set.range generatedNinthMarkingClass = generatedNinthMarkedShortClasses := by
  rw [generatedNinthMarkedShortClasses, ← generatedNinth_marking_label_range]
  exact Set.range_comp griessShortClass generatedNinthMarkingLabel

/-- There are exactly144 different actual lattice classes in the candidate marking catalogue. -/
theorem generatedNinth_marked_short_classes_card :
    Nat.card generatedNinthMarkedShortClasses = 144 := by
  rw [← generatedNinth_marking_class_range,
    ← Nat.card_congr (Equiv.ofInjective generatedNinthMarkingClass
      generatedNinthMarkingClass_injective), Nat.card_fin]

/-- The complete actual large-coefficient class set is the candidate class catalogue once
the exact original octad comparison has been supplied. -/
theorem generatedNinth_marked_short_classes_eq_of_octad_comparison
    (hoctad : ∀ (o : Fin 759) (e : Fin 64),
      |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
        o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns) :
    griessShortClass '' {r : GriessShortIndex |
      |(griessConwayEncode generatedNinthAxis).2.1 r| = 1 / 8} =
        generatedNinthMarkedShortClasses := by
  unfold generatedNinthMarkedShortClasses
  congr 1
  ext r
  exact generatedNinth_short_marking_iff_of_octad_comparison hoctad r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
