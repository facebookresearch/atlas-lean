/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A literal target generator lies in the twenty-four-point span by prior source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation027
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation038
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation045
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation048
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation057
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation064
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation071
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation075
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation086
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation091
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation112
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation117
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation129
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation131
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation141
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation154
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation191
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation195
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation203
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation208
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation261
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation436
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation480
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation485
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation488
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation489
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation492
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation529
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation574
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation579
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation612
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation632

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Verify the final sparse row using only prior proved original-source equations.
/-- Target point 192 belongs to the proposed source span by the exact finite source certificate. -/
theorem monsterCo1GeometryVectorTarget192 :
    monsterCo1GeometryVectorValue 192 ∈ monsterCo1GeometryVectorBasisSpan := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow0, monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow8, monsterCo1GeometryVectorRow10,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow23,
      monsterCo1GeometryVectorRow27, monsterCo1GeometryVectorRow38,
      monsterCo1GeometryVectorRow45, monsterCo1GeometryVectorRow48,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow55,
      monsterCo1GeometryVectorRow57, monsterCo1GeometryVectorRow64,
      monsterCo1GeometryVectorRow71, monsterCo1GeometryVectorRow75,
      monsterCo1GeometryVectorRow86, monsterCo1GeometryVectorRow91,
      monsterCo1GeometryVectorRow112, monsterCo1GeometryVectorRow117,
      monsterCo1GeometryVectorRow129, monsterCo1GeometryVectorRow131,
      monsterCo1GeometryVectorRow141, monsterCo1GeometryVectorRow149,
      monsterCo1GeometryVectorRow154, monsterCo1GeometryVectorRow191,
      monsterCo1GeometryVectorRow195, monsterCo1GeometryVectorRow203,
      monsterCo1GeometryVectorRow208, monsterCo1GeometryVectorRow261,
      monsterCo1GeometryVectorRow287, monsterCo1GeometryVectorRow436,
      monsterCo1GeometryVectorRow480, monsterCo1GeometryVectorRow485,
      monsterCo1GeometryVectorRow488, monsterCo1GeometryVectorRow489,
      monsterCo1GeometryVectorRow492, monsterCo1GeometryVectorRow529,
      monsterCo1GeometryVectorRow574, monsterCo1GeometryVectorRow579,
      monsterCo1GeometryVectorRow612, monsterCo1GeometryVectorRow632] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact monsterCo1GeometryVectorEquation0
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation8
    · exact monsterCo1GeometryVectorEquation10
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation23
    · exact monsterCo1GeometryVectorEquation27
    · exact monsterCo1GeometryVectorEquation38
    · exact monsterCo1GeometryVectorEquation45
    · exact monsterCo1GeometryVectorEquation48
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation55
    · exact monsterCo1GeometryVectorEquation57
    · exact monsterCo1GeometryVectorEquation64
    · exact monsterCo1GeometryVectorEquation71
    · exact monsterCo1GeometryVectorEquation75
    · exact monsterCo1GeometryVectorEquation86
    · exact monsterCo1GeometryVectorEquation91
    · exact monsterCo1GeometryVectorEquation112
    · exact monsterCo1GeometryVectorEquation117
    · exact monsterCo1GeometryVectorEquation129
    · exact monsterCo1GeometryVectorEquation131
    · exact monsterCo1GeometryVectorEquation141
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation154
    · exact monsterCo1GeometryVectorEquation191
    · exact monsterCo1GeometryVectorEquation195
    · exact monsterCo1GeometryVectorEquation203
    · exact monsterCo1GeometryVectorEquation208
    · exact monsterCo1GeometryVectorEquation261
    · exact monsterCo1GeometryVectorEquation287
    · exact monsterCo1GeometryVectorEquation436
    · exact monsterCo1GeometryVectorEquation480
    · exact monsterCo1GeometryVectorEquation485
    · exact monsterCo1GeometryVectorEquation488
    · exact monsterCo1GeometryVectorEquation489
    · exact monsterCo1GeometryVectorEquation492
    · exact monsterCo1GeometryVectorEquation529
    · exact monsterCo1GeometryVectorEquation574
    · exact monsterCo1GeometryVectorEquation579
    · exact monsterCo1GeometryVectorEquation612
    · exact monsterCo1GeometryVectorEquation632
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [192, 2, 3, 7, 8,
      10, 11, 12, 13, 15, 16] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0,
      monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow8,
      monsterCo1GeometryVectorRow10, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow18,
      monsterCo1GeometryVectorRow23, monsterCo1GeometryVectorRow27,
      monsterCo1GeometryVectorRow38, monsterCo1GeometryVectorRow45,
      monsterCo1GeometryVectorRow48, monsterCo1GeometryVectorRow52,
      monsterCo1GeometryVectorRow55, monsterCo1GeometryVectorRow57,
      monsterCo1GeometryVectorRow64, monsterCo1GeometryVectorRow71,
      monsterCo1GeometryVectorRow75, monsterCo1GeometryVectorRow86,
      monsterCo1GeometryVectorRow91, monsterCo1GeometryVectorRow112,
      monsterCo1GeometryVectorRow117, monsterCo1GeometryVectorRow129,
      monsterCo1GeometryVectorRow131, monsterCo1GeometryVectorRow141,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow154,
      monsterCo1GeometryVectorRow191, monsterCo1GeometryVectorRow195,
      monsterCo1GeometryVectorRow203, monsterCo1GeometryVectorRow208,
      monsterCo1GeometryVectorRow261, monsterCo1GeometryVectorRow287,
      monsterCo1GeometryVectorRow436, monsterCo1GeometryVectorRow480,
      monsterCo1GeometryVectorRow485, monsterCo1GeometryVectorRow488,
      monsterCo1GeometryVectorRow489, monsterCo1GeometryVectorRow492,
      monsterCo1GeometryVectorRow529, monsterCo1GeometryVectorRow574,
      monsterCo1GeometryVectorRow579, monsterCo1GeometryVectorRow612,
      monsterCo1GeometryVectorRow632] hp
    decide +kernel
  apply monsterCo1GeometryVectorRowEval_leading_mem _ _ 192 [2, 3, 7, 8, 10, 11, 12, 13,
      15, 16] _ hs
  have hb : ∀ j ∈ ([2, 3, 7, 8, 10, 11, 12, 13, 15, 16] : List (Fin 867)), j.val < 24 := by
      decide +kernel
  exact fun j hj => monsterCo1GeometryVectorBasis_mem j (hb j hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
