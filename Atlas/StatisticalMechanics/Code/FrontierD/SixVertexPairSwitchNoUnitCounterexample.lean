/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDisagreementDecomposition











open Finset

namespace StatMech.FrontierD

def sixVertexFourByTwoTorus : EvenTorus where
  width := 4
  height := 2
  width_pos := by norm_num
  height_pos := by norm_num
  width_even := by norm_num
  height_even := by norm_num


def sixVertexFourByTwoLowArrows :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal _ := false
  vertical _ := false



def sixVertexFourByTwoHighArrows :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := decide (v.1.val % 2 = v.2.val % 2)
  vertical v := decide (v.1.val % 2 ≠ v.2.val % 2)

local instance sixVertexArrowsIceRuleDecidable
    {T : EvenTorus} (omega : SixVertexArrows T) :
    Decidable omega.IceRule :=
  inferInstanceAs (Decidable (∀ v, omega.incomingCount v = 2))

theorem sixVertexFourByTwoLowArrows_ice :
    sixVertexFourByTwoLowArrows.IceRule := by
  decide +revert

theorem sixVertexFourByTwoHighArrows_ice :
    sixVertexFourByTwoHighArrows.IceRule := by
  decide +revert

theorem sixVertexFourByTwoLowArrows_seamCount :
    sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus
      sixVertexFourByTwoLowArrows
      (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 := by
  decide +revert

theorem sixVertexFourByTwoHighArrows_seamCount :
    sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus
      sixVertexFourByTwoHighArrows
      (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 := by
  decide +revert



theorem sixVertexFourByTwo_localDisagreementDegree_two
    (v : sixVertexFourByTwoTorus.Vertex) :
    (∑ d, if sixVertexLocalIncomingPattern sixVertexFourByTwoLowArrows v d ≠
        sixVertexLocalIncomingPattern sixVertexFourByTwoHighArrows v d
      then 1 else 0) = 2 := by
  decide +revert



abbrev SixVertexFourByTwoReducedMask := Fin 8 → Bool

def sixVertexFourByTwoReducedArrows
    (r : SixVertexFourByTwoReducedMask) :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v :=
    if v.2.val = 0 then
      if v.1.val = 0 then r 0 else if v.1.val = 2 then r 1 else false
    else
      if v.1.val = 1 then r 2 else if v.1.val = 3 then r 3 else false
  vertical v :=
    if v.2.val = 0 then
      if v.1.val = 1 then r 4 else if v.1.val = 3 then r 5 else false
    else
      if v.1.val = 0 then r 6 else if v.1.val = 2 then r 7 else false

def sixVertexFourByTwoVertex (x : Fin 4) (y : Fin 2) :
    sixVertexFourByTwoTorus.Vertex :=
  (⟨x.val, by change x.val < 4; exact x.isLt⟩,
    ⟨y.val, by change y.val < 2; exact y.isLt⟩)

def sixVertexFourByTwoReducedMaskOf
    (mask : SixVertexArrows sixVertexFourByTwoTorus) :
    SixVertexFourByTwoReducedMask :=
  fun i =>
    if i.val = 0 then mask.horizontal (sixVertexFourByTwoVertex 0 0)
    else if i.val = 1 then mask.horizontal (sixVertexFourByTwoVertex 2 0)
    else if i.val = 2 then mask.horizontal (sixVertexFourByTwoVertex 1 1)
    else if i.val = 3 then mask.horizontal (sixVertexFourByTwoVertex 3 1)
    else if i.val = 4 then mask.vertical (sixVertexFourByTwoVertex 1 0)
    else if i.val = 5 then mask.vertical (sixVertexFourByTwoVertex 3 0)
    else if i.val = 6 then mask.vertical (sixVertexFourByTwoVertex 0 1)
    else mask.vertical (sixVertexFourByTwoVertex 2 1)

theorem sixVertexFourByTwo_switchFirst_eq_reduced
    (mask : SixVertexArrows sixVertexFourByTwoTorus) :
    sixVertexTorusSwitchFirst mask
        sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows =
      sixVertexFourByTwoReducedArrows
        (sixVertexFourByTwoReducedMaskOf mask) := by
  apply SixVertexArrows.ext
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;>
      simp [sixVertexTorusSwitchFirst, sixVertexFourByTwoLowArrows,
        sixVertexFourByTwoHighArrows, sixVertexFourByTwoReducedMaskOf,
        sixVertexFourByTwoReducedArrows, sixVertexFourByTwoVertex]
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;>
      simp [sixVertexTorusSwitchFirst, sixVertexFourByTwoLowArrows,
        sixVertexFourByTwoHighArrows, sixVertexFourByTwoReducedMaskOf,
        sixVertexFourByTwoReducedArrows, sixVertexFourByTwoVertex]

set_option maxRecDepth 10000 in
theorem sixVertexFourByTwo_reduced_no_ice_to_middle
    (r : SixVertexFourByTwoReducedMask) :
    ¬ ((sixVertexFourByTwoReducedArrows r).IceRule /\
      sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByTwoTorus
          (sixVertexFourByTwoReducedArrows r)
          (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1) := by
  decide +revert



theorem sixVertexFourByTwo_no_icePairSwitch_to_middle
    (mask : SixVertexArrows sixVertexFourByTwoTorus) :
    ¬ ((sixVertexTorusSwitchFirst mask
          sixVertexFourByTwoLowArrows
          sixVertexFourByTwoHighArrows).IceRule /\
      (sixVertexTorusSwitchSecond mask
          sixVertexFourByTwoLowArrows
          sixVertexFourByTwoHighArrows).IceRule /\
      sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByTwoTorus
          (sixVertexTorusSwitchFirst mask
            sixVertexFourByTwoLowArrows
            sixVertexFourByTwoHighArrows)
          (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1) := by
  intro hbad
  have hfirst := sixVertexFourByTwo_reduced_no_ice_to_middle
    (sixVertexFourByTwoReducedMaskOf mask)
  apply hfirst
  rw [← sixVertexFourByTwo_switchFirst_eq_reduced]
  exact ⟨hbad.1, hbad.2.2⟩

end StatMech.FrontierD
