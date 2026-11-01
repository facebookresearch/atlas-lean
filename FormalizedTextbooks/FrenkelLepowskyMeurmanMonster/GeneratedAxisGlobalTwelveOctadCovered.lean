/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadOddLink
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadDiagonalDestination

/-! Unconditional coverage of the Octad family: every actual transition from the listed Octad
representative lies in the twelve-family catalogue union. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Every actual Octad-family transition lies in the twelve-family catalogue union. -/
theorem generatedAxisGlobalTwelve_octad_covered : GeneratedAxisGlobalTwelveFamilyCovered 1 :=
  generatedAxisGlobalTwelve_octad_covered_of generatedAxisGlobalTwelveOctad_diagonalBound

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
