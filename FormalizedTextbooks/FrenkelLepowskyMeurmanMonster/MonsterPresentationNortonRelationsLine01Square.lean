/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- All original preferred short returns establish the actual first Norton line-ratio square. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortIdentity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TwentyThreeReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairReturns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OctadThreeReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeFiveReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeSevenReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeNineReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeTenReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeSixteenReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeSeventeenReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeEighteenReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeNineteenReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeTwentyReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeTwentyOneReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CodeTwentyTwoReturn

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every one of the twenty-three original preferred short vectors has its whole actual return. -/
theorem monsterNortonLineZeroOneSquare_all_evenShort_returns (k : Fin 23) :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis k)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis k) := by
  fin_cases k
  · exact monsterNortonLineZeroOneSquare_pair_returns 0
  · exact monsterNortonLineZeroOneSquare_pair_returns 1
  · exact monsterNortonLineZeroOneSquare_pair_returns 2
  · exact monsterNortonLineZeroOneSquare_pair_returns 3
  · exact monsterNortonLineZeroOneSquare_pair_returns 4
  · exact monsterNortonLineZeroOneSquare_pair_returns 5
  · exact monsterNortonLineZeroOneSquare_pair_returns 6
  · exact monsterNortonLineZeroOneSquare_pair_returns 7
  · exact monsterNortonLineZeroOneSquare_pair_returns 8
  · exact monsterNortonLineZeroOneSquare_pair_returns 9
  · exact monsterNortonLineZeroOne_codeTen_return
  · exact monsterNortonLineZeroOneSquare_pair_returns 10
  · exact monsterNortonLineZeroOneSquare_octad_three_return
  · exact monsterNortonLineZeroOne_codeFive_return
  · exact monsterNortonLineZeroOne_codeSeven_return
  · exact monsterNortonLineZeroOne_codeNine_return
  · exact monsterNortonLineZeroOne_codeSixteen_return
  · exact monsterNortonLineZeroOne_codeSeventeen_return
  · exact monsterNortonLineZeroOne_codeEighteen_return
  · exact monsterNortonLineZeroOne_codeNineteen_return
  · exact monsterNortonLineZeroOne_codeTwenty_return
  · exact monsterNortonLineZeroOne_codeTwentyOne_return
  · exact monsterNortonLineZeroOne_codeTwentyTwo_return

/-- The literal actual first Norton line difference has square one in the generated group. -/
theorem monsterNortonLineZeroOne_square :
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2 = 1 :=
  monsterNortonGenerated_evenShort_identity _
    monsterNortonLineZeroOneSquare_all_evenShort_returns
    monsterNortonLineZeroOneSquare_twentyThreeTensor_fixed

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
