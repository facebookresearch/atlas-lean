/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Cyclic longest-word consequences of the original independent Y555 relations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationLongestWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555ArmRotation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The second-arm longest involution, obtained by the genuine cyclic source automorphism. -/
def y555LocalF2 : BimonsterPresentation := y555CycleHom y555LocalF1

/-- Its F21 spelling is the ninth power of seven exact original source generators. -/
theorem y555LocalF2_word21 : y555LocalF2 =
    ((PresentedGroup.of none : BimonsterPresentation) * PresentedGroup.of (some (1, 0)) *
      PresentedGroup.of (some (0, 0)) * PresentedGroup.of (some (2, 0)) *
      PresentedGroup.of (some (1, 1)) * PresentedGroup.of (some (0, 1)) *
      PresentedGroup.of (some (1, 2))) ^ 9 := by
  rw [y555LocalF2, y555LocalF1_word13]
  have hb := y555Source_generator_commute (some (2, 0)) (some (0, 0)) (by decide)
  simp [y555LocalRestrictedWord, y555LocalF1Support13, y555CycleHom_generator,
    y322Vertex, y555VertexCycle, y555ArmCycle, map_pow, mul_assoc, hb.left_comm]

/-- The actual second-arm longest involution commutes with the first-arm d-generator. -/
theorem y555LocalF2_commute_d1 :
    Commute y555LocalF2 (PresentedGroup.of (some (0, 2))) := by
  have h := (y555LocalF1_commute (some (2, 2)) (by decide)).map y555CycleHom
  have hv : y555VertexCycle (some (2, 2)) = some (0, 2) := by decide +kernel
  simpa only [y555LocalF2, y555CycleHom_generator, hv] using h

/-- The second-arm longest word is an actual source involution. -/
theorem y555LocalF2_square : y555LocalF2 * y555LocalF2 = 1 := by
  simpa only [y555LocalF2, map_mul, map_one] using congrArg y555CycleHom y555LocalF1_square

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
