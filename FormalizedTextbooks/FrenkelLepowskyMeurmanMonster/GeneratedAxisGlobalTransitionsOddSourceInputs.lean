/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryCover
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddForestCover

/-! The nine genuine binary roots are the roots of explicit original local words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Checked finite descent edges give coverage using the explicit original local word roots. -/
theorem generatedAxisGlobalOddSourceRootLocalWord_cover_of_forest
    (hedges : ∀ b : Fin (2 ^ 24), ∃ e : ℕ, generatedAxisGlobalOddForestStep e b.val) :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 9, ∃ c : H,
      c ∈ generatedOddLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalOddSourceRootLocalWord i)) = x := by
  intro x
  obtain ⟨i, c, hc, he⟩ := generatedAxisGlobalOddBinary_cover_of_forest hedges x
  exact ⟨i, c, hc, by rw [generatedAxisGlobalOddSourceRootLocalWord_root]; exact he⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
