/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator

/-! Executable finite numerators are bound to the genuine cached short coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sixteen times the genuine final-axis coefficient of a physical cached short row. -/
def generatedFifthXiShortCachedNumerator : generatedFifthXiShortCachedLabel → ℤ
  | Sum.inl (s, p) => generatedFifthFinalPairNumerator s p.val.1 p.val.2
  | Sum.inr (j, e) => generatedFifthFinalOctadNumerator j e

/-- Every executable cached numerator is the actual original final-axis short coefficient. -/
theorem generatedFifthXiShortCachedNumerator_actual (r : generatedFifthXiShortCachedLabel) :
    (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r)) =
      (generatedFifthXiShortCachedNumerator r : ℝ) / 16 := by
  rcases r with ⟨s, p⟩ | ⟨j, e⟩
  · simpa only [generatedFifthXiShortCachedEven, generatedFifthXiEvenShortIndex,
      generatedFifthXiShortCachedNumerator, griessPairIndex_coordinates, p.property, ite_true]
      using generatedFifth_final_pair_numerator s
        (griessPairIndex p.val.1 p.val.2 (ne_of_lt p.property))
  · exact generatedFifth_final_octad_numerator j e

/-- A finite signed integer equation gives the genuine final-axis coefficient equation. -/
theorem generatedFifthXiShortCachedNumerator_signed
    (r s : generatedFifthXiShortCachedLabel) (p : ZMod 2)
    (h : (if p = 0 then (1 : ℤ) else -1) * generatedFifthXiShortCachedNumerator r =
      generatedFifthXiShortCachedNumerator s) :
    qSign p * (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r)) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) := by
  rw [generatedFifthXiShortCachedNumerator_actual,
    generatedFifthXiShortCachedNumerator_actual]
  have hr : (if p = 0 then (1 : ℝ) else -1) *
        (generatedFifthXiShortCachedNumerator r : ℝ) =
      (generatedFifthXiShortCachedNumerator s : ℝ) := by
    exact_mod_cast h
  change (if p = 0 then (1 : ℝ) else -1) *
    ((generatedFifthXiShortCachedNumerator r : ℝ) / 16) = _
  rw [← mul_div_assoc, hr]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
