/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact finite original-source replay proves the twenty-four-point Conway module span. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions32
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorOperatorsFive
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget002
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget003
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget009
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget016
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget019
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget022
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget024
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget025
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget029
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget032
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget034
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget042
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget072
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget076
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget078
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget079
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget083
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget099
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget104
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget106
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget114
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget121
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget165
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget171
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget172
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget173
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget174
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget175
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget176
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget177
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget178
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget179
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget180
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget181
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget182
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget183
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget184
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget185
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget186
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget187
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget188
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget189
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget190
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget191
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget192
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget193
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget194
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget195
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget196
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget197
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget198
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget199
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget200
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget201
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget202
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget203
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget204
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget205
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget206
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget207
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget208
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget209
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget210
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget211
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget212
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget213
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget214
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget215
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorTarget216

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Reuse every checked actual action binding and every checked original-source target relation.
/-- Every actual five-generator image of all twenty-four source basis points lies in their span. -/
theorem monsterCo1GeometryVectorBasis_image_mem (k : Fin 5) (j : Fin 24) :
    monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator k • monsterCo1GeometryVectorBasisPoint j) ∈
        monsterCo1GeometryVectorBasisSpan := by
  fin_cases k <;> fin_cases j <;> dsimp only
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 0) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint0) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction0]
    exact monsterCo1GeometryVectorTarget1
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 1) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint1) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction1]
    exact monsterCo1GeometryVectorTarget24
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 2) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint2) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction2]
    exact monsterCo1GeometryVectorTarget4
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 3) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint3) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction3]
    exact monsterCo1GeometryVectorTarget7
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 4) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint4) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction4]
    exact monsterCo1GeometryVectorTarget8
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 5) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint5) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction5]
    exact monsterCo1GeometryVectorTarget29
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 6) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint6) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction6]
    exact monsterCo1GeometryVectorTarget171
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 7) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint7) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction7]
    exact monsterCo1GeometryVectorTarget34
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 8) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint8) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction8]
    exact monsterCo1GeometryVectorTarget2
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 9) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint9) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction9]
    exact monsterCo1GeometryVectorTarget78
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 10) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint10) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction10]
    exact monsterCo1GeometryVectorTarget79
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 11) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint11) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction11]
    exact monsterCo1GeometryVectorTarget172
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 12) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint12) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction12]
    exact monsterCo1GeometryVectorTarget17
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 13) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint13) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction13]
    exact monsterCo1GeometryVectorTarget44
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 14) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint14) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction14]
    exact monsterCo1GeometryVectorTarget173
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 15) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint15) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction15]
    exact monsterCo1GeometryVectorTarget18
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 16) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint16) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction16]
    exact monsterCo1GeometryVectorTarget174
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 17) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint17) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction17]
    exact monsterCo1GeometryVectorTarget99
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 18) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint18) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction18]
    exact monsterCo1GeometryVectorTarget175
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 19) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint19) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction19]
    exact monsterCo1GeometryVectorTarget176
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 20) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint20) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction20]
    exact monsterCo1GeometryVectorTarget23
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 21) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint21) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction21]
    exact monsterCo1GeometryVectorTarget177
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 22) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint22) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction22]
    exact monsterCo1GeometryVectorTarget178
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 0 • monsterCo1GeometryVectorBasisPoint 23) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 0]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint23) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction23]
    exact monsterCo1GeometryVectorTarget179
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 0) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint0) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction189]
    exact monsterCo1GeometryVectorTarget0
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 1) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint1) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction190]
    exact monsterCo1GeometryVectorTarget1
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 2) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint2) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction191]
    exact monsterCo1GeometryVectorTarget25
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 3) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint3) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction192]
    exact monsterCo1GeometryVectorTarget3
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 4) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint4) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction193]
    exact monsterCo1GeometryVectorTarget9
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 5) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint5) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction194]
    exact monsterCo1GeometryVectorTarget5
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 6) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint6) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction195]
    exact monsterCo1GeometryVectorTarget32
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 7) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint7) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction196]
    exact monsterCo1GeometryVectorTarget13
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 8) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint8) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction197]
    exact monsterCo1GeometryVectorTarget78
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 9) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint9) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction198]
    exact monsterCo1GeometryVectorTarget4
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 10) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint10) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction199]
    exact monsterCo1GeometryVectorTarget106
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 11) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint11) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction200]
    exact monsterCo1GeometryVectorTarget15
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 12) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint12) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction201]
    exact monsterCo1GeometryVectorTarget12
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 13) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint13) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction202]
    exact monsterCo1GeometryVectorTarget7
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 14) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint14) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction203]
    exact monsterCo1GeometryVectorTarget180
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 15) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint15) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction204]
    exact monsterCo1GeometryVectorTarget11
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 16) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint16) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction205]
    exact monsterCo1GeometryVectorTarget16
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 17) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint17) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction206]
    exact monsterCo1GeometryVectorTarget181
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 18) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint18) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction207]
    exact monsterCo1GeometryVectorTarget182
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 19) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint19) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction208]
    exact monsterCo1GeometryVectorTarget183
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 20) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint20) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction209]
    exact monsterCo1GeometryVectorTarget20
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 21) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint21) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction210]
    exact monsterCo1GeometryVectorTarget184
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 22) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint22) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction211]
    exact monsterCo1GeometryVectorTarget185
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 1 • monsterCo1GeometryVectorBasisPoint 23) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 1]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint23) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction212]
    exact monsterCo1GeometryVectorTarget186
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 0) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint0) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction330]
    exact monsterCo1GeometryVectorTarget0
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 1) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint1) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction331]
    exact monsterCo1GeometryVectorTarget1
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 2) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint2) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction332]
    exact monsterCo1GeometryVectorTarget25
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 3) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint3) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction333]
    exact monsterCo1GeometryVectorTarget3
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 4) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint4) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction334]
    exact monsterCo1GeometryVectorTarget10
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 5) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint5) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction335]
    exact monsterCo1GeometryVectorTarget29
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 6) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint6) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction336]
    exact monsterCo1GeometryVectorTarget32
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 7) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint7) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction337]
    exact monsterCo1GeometryVectorTarget187
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 8) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint8) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction338]
    exact monsterCo1GeometryVectorTarget79
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 9) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint9) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction339]
    exact monsterCo1GeometryVectorTarget106
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 10) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint10) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction340]
    exact monsterCo1GeometryVectorTarget4
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 11) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint11) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction341]
    exact monsterCo1GeometryVectorTarget188
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 12) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint12) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction342]
    exact monsterCo1GeometryVectorTarget42
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 13) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint13) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction343]
    exact monsterCo1GeometryVectorTarget189
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 14) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint14) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction344]
    exact monsterCo1GeometryVectorTarget190
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 15) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint15) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction345]
    exact monsterCo1GeometryVectorTarget191
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 16) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint16) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction346]
    exact monsterCo1GeometryVectorTarget192
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 17) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint17) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction347]
    exact monsterCo1GeometryVectorTarget193
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 18) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint18) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction348]
    exact monsterCo1GeometryVectorTarget194
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 19) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint19) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction349]
    exact monsterCo1GeometryVectorTarget195
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 20) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint20) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction350]
    exact monsterCo1GeometryVectorTarget196
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 21) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint21) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction351]
    exact monsterCo1GeometryVectorTarget197
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 22) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint22) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction352]
    exact monsterCo1GeometryVectorTarget198
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 2 • monsterCo1GeometryVectorBasisPoint 23) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 2]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint23) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction353]
    exact monsterCo1GeometryVectorTarget199
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 0) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint0) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction467]
    exact monsterCo1GeometryVectorTarget0
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 1) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint1) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction468]
    exact monsterCo1GeometryVectorTarget2
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 2) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint2) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction469]
    exact monsterCo1GeometryVectorTarget5
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 3) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint3) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction470]
    exact monsterCo1GeometryVectorTarget200
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 4) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint4) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction471]
    exact monsterCo1GeometryVectorTarget76
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 5) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint5) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction472]
    exact monsterCo1GeometryVectorTarget83
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 6) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint6) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction473]
    exact monsterCo1GeometryVectorTarget12
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 7) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint7) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction474]
    exact monsterCo1GeometryVectorTarget14
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 8) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint8) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction475]
    exact monsterCo1GeometryVectorTarget72
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 9) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint9) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction476]
    exact monsterCo1GeometryVectorTarget121
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 10) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint10) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction477]
    exact monsterCo1GeometryVectorTarget114
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 11) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint11) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction478]
    exact monsterCo1GeometryVectorTarget16
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 12) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint12) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction479]
    exact monsterCo1GeometryVectorTarget201
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 13) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint13) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction480]
    exact monsterCo1GeometryVectorTarget202
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 14) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint14) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction481]
    exact monsterCo1GeometryVectorTarget203
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 15) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint15) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction482]
    exact monsterCo1GeometryVectorTarget192
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 16) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint16) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction483]
    exact monsterCo1GeometryVectorTarget19
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 17) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint17) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction484]
    exact monsterCo1GeometryVectorTarget21
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 18) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint18) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction485]
    exact monsterCo1GeometryVectorTarget204
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 19) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint19) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction486]
    exact monsterCo1GeometryVectorTarget205
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 20) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint20) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction487]
    exact monsterCo1GeometryVectorTarget206
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 21) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint21) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction488]
    exact monsterCo1GeometryVectorTarget207
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 22) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint22) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction489]
    exact monsterCo1GeometryVectorTarget208
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 3 • monsterCo1GeometryVectorBasisPoint 23) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 3]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint23) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction490]
    exact monsterCo1GeometryVectorTarget209
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 0) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint0) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction745]
    exact monsterCo1GeometryVectorTarget0
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 1) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint1) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction746]
    exact monsterCo1GeometryVectorTarget3
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 2) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint2) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction747]
    exact monsterCo1GeometryVectorTarget6
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 3) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint3) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction748]
    exact monsterCo1GeometryVectorTarget1
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 4) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint4) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction749]
    exact monsterCo1GeometryVectorTarget11
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 5) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint5) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction750]
    exact monsterCo1GeometryVectorTarget210
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 6) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint6) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction751]
    exact monsterCo1GeometryVectorTarget2
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 7) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint7) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction752]
    exact monsterCo1GeometryVectorTarget7
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 8) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint8) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction753]
    exact monsterCo1GeometryVectorTarget104
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 9) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint9) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction754]
    exact monsterCo1GeometryVectorTarget15
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 10) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint10) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction755]
    exact monsterCo1GeometryVectorTarget165
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 11) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint11) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction756]
    exact monsterCo1GeometryVectorTarget4
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 12) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint12) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction757]
    exact monsterCo1GeometryVectorTarget211
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 13) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint13) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction758]
    exact monsterCo1GeometryVectorTarget13
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 14) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint14) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction759]
    exact monsterCo1GeometryVectorTarget212
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 15) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint15) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction760]
    exact monsterCo1GeometryVectorTarget9
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 16) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint16) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction761]
    exact monsterCo1GeometryVectorTarget20
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 17) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint17) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction762]
    exact monsterCo1GeometryVectorTarget213
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 18) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint18) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction763]
    exact monsterCo1GeometryVectorTarget22
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 19) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint19) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction764]
    exact monsterCo1GeometryVectorTarget214
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 20) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint20) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction765]
    exact monsterCo1GeometryVectorTarget16
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 21) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint21) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction766]
    exact monsterCo1GeometryVectorTarget215
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 22) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint22) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction767]
    exact monsterCo1GeometryVectorTarget18
  · change monsterCo1GeometryUniversalPoint
      (monsterCo1FiveGenerator 4 • monsterCo1GeometryVectorBasisPoint 23) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [← monsterCo1GeometryVectorFiveOperator_actual 4]
    change monsterCo1GeometryUniversalPoint
      (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint23) ∈
        monsterCo1GeometryVectorBasisSpan
    rw [monsterCo1GeometryVectorAction768]
    exact monsterCo1GeometryVectorTarget216
/-- The twenty-four literal actual source point generators span the entire independent
universal module, by the full checked original-line replay and actual Conway generation. -/
theorem monsterCo1GeometryVectorBasisSpan_eq_top : monsterCo1GeometryVectorBasisSpan = ⊤ := by
  have hb : monsterCo1GeometryBasePoint = monsterCo1GeometryVectorBasisPoint 0 := by
    apply Subtype.ext
    change monsterCo1GeometryBasePoint.val = monsterCo1GeometryVectorPoint0.val
    rw [monsterCo1GeometryBasePoint_binary, monsterCo1GeometryVectorPoint0_binary]
    decide +kernel
  apply monsterCo1GeometryUniversal_pointSpan_eq_top monsterCo1GeometryVectorBasisPoint
  · rw [hb]
    exact Submodule.subset_span ⟨0, rfl⟩
  · exact monsterCo1GeometryVectorBasis_image_mem

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
