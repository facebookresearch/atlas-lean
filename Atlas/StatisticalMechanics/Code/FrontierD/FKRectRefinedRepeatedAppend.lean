/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedRepeatedInteraction









open Finset

namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

variable {L : Nat} [Fact (8 < L)]



theorem fkRectRefinedRawInteraction_repeatTranslated_append_right
    (x : List (ons_Dart L))
    (a b : List FKRectIntegralSquareDart)
    (u : Int × Int) (n : Nat) :
    fkRectRefinedRawInteraction x
        ((fkRectRepeatTranslatedDartPath (a ++ b) u n).map
          (fkRectIntegralSquareDartMod L)) =
      fkRectRefinedRawInteraction x
          ((fkRectRepeatTranslatedDartPath a u n).map
            (fkRectIntegralSquareDartMod L)) +
        fkRectRefinedRawInteraction x
          ((fkRectRepeatTranslatedDartPath b u n).map
            (fkRectIntegralSquareDartMod L)) := by
  rw [fkRectRefinedRawInteraction_repeatTranslated_right,
    fkRectRefinedRawInteraction_repeatTranslated_right,
    fkRectRefinedRawInteraction_repeatTranslated_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [List.map_append, List.map_append,
    fkRectRefinedRawInteraction_append_right]



theorem fkRectRefinedRawInteraction_repeatTranslated_append_left
    (a b : List FKRectIntegralSquareDart)
    (u : Int × Int) (n : Nat)
    (x : List (ons_Dart L)) :
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath (a ++ b) u n).map
          (fkRectIntegralSquareDartMod L)) x =
      fkRectRefinedRawInteraction
          ((fkRectRepeatTranslatedDartPath a u n).map
            (fkRectIntegralSquareDartMod L)) x +
        fkRectRefinedRawInteraction
          ((fkRectRepeatTranslatedDartPath b u n).map
            (fkRectIntegralSquareDartMod L)) x := by
  rw [fkRectRefinedRawInteraction_repeatTranslated_left,
    fkRectRefinedRawInteraction_repeatTranslated_left,
    fkRectRefinedRawInteraction_repeatTranslated_left,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [List.map_append, List.map_append,
    fkRectRefinedRawInteraction_append_left]

end

end StatMech.FrontierD
