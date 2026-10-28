/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMatrixBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthPairBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthOctadBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthOdd

/-! The Tenth local family: no actual signed-short axis is orthogonal to the actual Tenth
prototype.

The Tenth matrix dominates `17/64 I`, so every contraction against an actual short vector is at
least `17/16`, while every short coordinate has absolute value at most `1/4`: pair rows at most
`3/32` (exact rational check), octad rows at most `1/4` (octad triality of the checked incoming
packet blocks), and odd rows at most `3/32` (the eight certified root-two tensor factors). -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- No actual signed-short axis is orthogonal to the actual Tenth prototype. -/
theorem generatedFeasibleAmbient_tenth_form_ne (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c) generatedTenthAxis ≠ 0 := by
  apply generatedFeasibleAmbientTenth_form_ne_of_abs
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · exact (generatedFeasibleAmbientTenth_pair_abs s p).trans (by norm_num)
  · exact generatedFeasibleAmbientTenth_octad_abs o e
  · exact (generatedFeasibleAmbientTenth_odd_abs d i).trans (by norm_num)

/-- No actual signed-short axis is orthogonal to the actual Tenth prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_tenth :
    generatedFeasibleAmbientAxisZeroCount generatedTenthAxis = 0 := by
  unfold generatedFeasibleAmbientAxisZeroCount
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨⟨r, c⟩, h⟩
  exact generatedFeasibleAmbient_tenth_form_ne r c h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
