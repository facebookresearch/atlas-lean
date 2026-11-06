/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortFixation

/-! Actual whole-axis attainment for the original reduced Mathieu generators. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The four original corrected fibers fix every actual canonical short coordinate. -/
theorem generatedRootEight_four_actual_short_fixation (g : Fin 4) :
    localShortRepresentation (generatedRootEightMathieuReducedShortFiber g)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 :=
  generatedRootEight_mathieu_reduced_short_fixation g
    generatedRootEight_canonical_short_actual

/-- Each original reduced Mathieu generator attains a genuine whole-axis fixer;
the selectable sign is an actual central Q element. -/
theorem generatedRootEight_mathieu_reduced_actual_whole_axis_fixer (j : Fin 2) :
    ∃ c : ZMod 2,
      rhoLocal (inclQ (qCentral c) * generatedRootEightMathieuReducedCertifiedLocal j)
        generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis :=
  generatedRootEight_mathieu_reduced_whole_axis_fixers_of_short_binding j
    generatedRootEight_canonical_short_actual

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
