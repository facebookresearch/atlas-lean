/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCatalogue
public import Mathlib.SetTheory.Cardinal.Finite

/-! Counting actual large short-coordinate coefficients from the exact original catalogue.
The octad comparison is the sole explicit missing comparison in this counting helper. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual large short-coordinate labels have cardinal144 once the exact actual octad
comparison has been supplied. -/
theorem generatedNinth_short_marking_card_of_octad_comparison
    (hoctad : ∀ (o : Fin 759) (e : Fin 64),
      |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
        o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns) :
    Nat.card {r : GriessShortIndex //
      |(griessConwayEncode generatedNinthAxis).2.1 r| = 1 / 8} = 144 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (generatedNinth_short_marking_iff_of_octad_comparison hoctad))]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    generatedNinth_short_markings_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
