/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source basis-point transport and its complete checked binary matrix. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorOperatorsFive
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTransportWordProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTransportColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBaseCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitSpan

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual lattice word for source basis point 22. -/
def monsterCo1GeometryVectorPoint22Transport : Co1 :=
  QuotientGroup.mk (omegaOrbitWordIsometry (omegaOrbitWords 22))

/-- Complete displayed binary matrix of actual transport 22. -/
def monsterCo1GeometryVectorPoint22Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0],
    ![0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1],
    ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0],
    ![0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    ![1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0],
    ![0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0],
    ![1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1]]

/-- Complete prefix matrix 1 of original actual source word 22. -/
def monsterCo1GeometryVectorPoint22WordMatrix1 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Complete prefix matrix 2 of original actual source word 22. -/
def monsterCo1GeometryVectorPoint22WordMatrix2 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1],
    ![1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1],
    ![1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1],
    ![1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Complete prefix matrix 3 of original actual source word 22. -/
def monsterCo1GeometryVectorPoint22WordMatrix3 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1],
    ![1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1],
    ![1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1],
    ![1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Complete prefix matrix 4 of original actual source word 22. -/
def monsterCo1GeometryVectorPoint22WordMatrix4 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0],
    ![0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1],
    ![1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    ![1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Complete prefix matrix 5 of original actual source word 22. -/
def monsterCo1GeometryVectorPoint22WordMatrix5 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    ![0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1],
    ![1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0],
    ![1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1],
    ![0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1],
    ![0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0],
    ![1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Complete prefix matrix 6 of original actual source word 22. -/
def monsterCo1GeometryVectorPoint22WordMatrix6 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0],
    ![1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1],
    ![1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1],
    ![0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    ![1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0],
    ![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0],
    ![1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1],
    ![0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1],
    ![0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0],
    ![0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 22 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint22Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint22Transport v =
      monsterCo1GeometryVectorPoint22Matrix *ᵥ v := by
  have hm0 : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hm1 : monsterCo1GeometryVectorPoint22WordMatrix1 = monsterCo1GeometryBinaryMaskMatrix
      ![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
        16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632] := by
        decide +kernel
  have hc1 : omegaOrbitBinaryMatrices 0 * (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
    monsterCo1GeometryVectorPoint22WordMatrix1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 0))
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608]
      ![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
        16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632]
      ((monsterCo1GeometryVectorFiveOperator_matrix 0).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 0)))
      hm0 hm1 (by decide +kernel)
  have hm2 : monsterCo1GeometryVectorPoint22WordMatrix2 = monsterCo1GeometryBinaryMaskMatrix
      ![57504, 8441984, 8450944, 8450432, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
        8445952, 4203168, 13684367, 1049249, 2106784, 3155872, 12811348, 12762360, 13147381,
        13392985, 9495771, 9495671, 4524557, 8389632] := by decide +kernel
  have hc2 : omegaOrbitBinaryMatrices 3 * monsterCo1GeometryVectorPoint22WordMatrix1 =
    monsterCo1GeometryVectorPoint22WordMatrix2 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 3))
      ![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
        16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632]
      ![57504, 8441984, 8450944, 8450432, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
        8445952, 4203168, 13684367, 1049249, 2106784, 3155872, 12811348, 12762360, 13147381,
        13392985, 9495771, 9495671, 4524557, 8389632]
      ((monsterCo1GeometryVectorFiveOperator_matrix 3).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 3)))
      hm1 hm2 (by decide +kernel)
  have hm3 : monsterCo1GeometryVectorPoint22WordMatrix3 = monsterCo1GeometryBinaryMaskMatrix
      ![161, 12635279, 15788942, 14739854, 8445968, 8446000, 8446144, 8446016, 8421584,
        8405104, 8389632, 4524557, 5250063, 1105921, 2155520, 3204096, 12811348, 12762360,
        13147381, 13392985, 9495771, 9495671, 338093, 58368] := by decide +kernel
  have hc3 : omegaOrbitBinaryMatrices 0 * monsterCo1GeometryVectorPoint22WordMatrix2 =
    monsterCo1GeometryVectorPoint22WordMatrix3 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 0))
      ![57504, 8441984, 8450944, 8450432, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
        8445952, 4203168, 13684367, 1049249, 2106784, 3155872, 12811348, 12762360, 13147381,
        13392985, 9495771, 9495671, 4524557, 8389632]
      ![161, 12635279, 15788942, 14739854, 8445968, 8446000, 8446144, 8446016, 8421584,
        8405104, 8389632, 4524557, 5250063, 1105921, 2155520, 3204096, 12811348, 12762360,
        13147381, 13392985, 9495771, 9495671, 338093, 58368]
      ((monsterCo1GeometryVectorFiveOperator_matrix 0).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 0)))
      hm2 hm3 (by decide +kernel)
  have hm4 : monsterCo1GeometryVectorPoint22WordMatrix4 = monsterCo1GeometryBinaryMaskMatrix
      ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584,
        8405104, 8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046,
        5824133, 16563192, 1691, 11583990, 338093, 58368] := by decide +kernel
  have hc4 : omegaOrbitBinaryMatrices 1 * monsterCo1GeometryVectorPoint22WordMatrix3 =
    monsterCo1GeometryVectorPoint22WordMatrix4 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 1))
      ![161, 12635279, 15788942, 14739854, 8445968, 8446000, 8446144, 8446016, 8421584,
        8405104, 8389632, 4524557, 5250063, 1105921, 2155520, 3204096, 12811348, 12762360,
        13147381, 13392985, 9495771, 9495671, 338093, 58368]
      ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584,
        8405104, 8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046,
        5824133, 16563192, 1691, 11583990, 338093, 58368]
      ((monsterCo1GeometryVectorFiveOperator_matrix 1).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 1)))
      hm3 hm4 (by decide +kernel)
  have hm5 : monsterCo1GeometryVectorPoint22WordMatrix5 = monsterCo1GeometryBinaryMaskMatrix
      ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
        12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978,
        5389864, 12384167, 9523772, 6568274, 338093, 58368] := by decide +kernel
  have hc5 : omegaOrbitBinaryMatrices 4 * monsterCo1GeometryVectorPoint22WordMatrix4 =
    monsterCo1GeometryVectorPoint22WordMatrix5 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 4))
      ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584,
        8405104, 8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046,
        5824133, 16563192, 1691, 11583990, 338093, 58368]
      ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
        12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978,
        5389864, 12384167, 9523772, 6568274, 338093, 58368]
      ((monsterCo1GeometryVectorFiveOperator_matrix 4).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 4)))
      hm4 hm5 (by decide +kernel)
  have hm6 : monsterCo1GeometryVectorPoint22WordMatrix6 = monsterCo1GeometryBinaryMaskMatrix
      ![12929074, 6220808, 10382183, 10406231, 12601423, 12627006, 12610767, 12610590,
        12635279, 12635182, 58368, 338093, 13552872, 13969570, 2443469, 3533053, 8646666,
        1593978, 5389864, 12384167, 9523772, 6568274, 5476570, 9495040] := by decide +kernel
  have hc6 : omegaOrbitBinaryMatrices 0 * monsterCo1GeometryVectorPoint22WordMatrix5 =
    monsterCo1GeometryVectorPoint22WordMatrix6 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 0))
      ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
        12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978,
        5389864, 12384167, 9523772, 6568274, 338093, 58368]
      ![12929074, 6220808, 10382183, 10406231, 12601423, 12627006, 12610767, 12610590,
        12635279, 12635182, 58368, 338093, 13552872, 13969570, 2443469, 3533053, 8646666,
        1593978, 5389864, 12384167, 9523772, 6568274, 5476570, 9495040]
      ((monsterCo1GeometryVectorFiveOperator_matrix 0).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 0)))
      hm5 hm6 (by decide +kernel)
  have hm7 : monsterCo1GeometryVectorPoint22Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![161, 12635279, 12911475, 12951875, 6187208, 10159226, 6196248, 10159114, 6220808,
        10200122, 17968, 338093, 13679119, 9496113, 7583098, 6535034, 14194718, 13377038,
        4405967, 2283296, 8406763, 3162406, 5476570, 9495040] := by decide +kernel
  have hc7 : omegaOrbitBinaryMatrices 4 * monsterCo1GeometryVectorPoint22WordMatrix6 =
    monsterCo1GeometryVectorPoint22Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 4))
      ![12929074, 6220808, 10382183, 10406231, 12601423, 12627006, 12610767, 12610590,
        12635279, 12635182, 58368, 338093, 13552872, 13969570, 2443469, 3533053, 8646666,
        1593978, 5389864, 12384167, 9523772, 6568274, 5476570, 9495040]
      ![161, 12635279, 12911475, 12951875, 6187208, 10159226, 6196248, 10159114, 6220808,
        10200122, 17968, 338093, 13679119, 9496113, 7583098, 6535034, 14194718, 13377038,
        4405967, 2283296, 8406763, 3162406, 5476570, 9495040]
      ((monsterCo1GeometryVectorFiveOperator_matrix 4).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 4)))
      hm6 hm7 (by decide +kernel)
  have h0 := monsterCo1GeometryTransportWord_nil_binary
  have h1 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0]) v =
      monsterCo1GeometryVectorPoint22WordMatrix1 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [] 0
      (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) monsterCo1GeometryVectorPoint22WordMatrix1 h0 hc1
  have h2 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3]) v =
      monsterCo1GeometryVectorPoint22WordMatrix2 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0] 3
      monsterCo1GeometryVectorPoint22WordMatrix1 monsterCo1GeometryVectorPoint22WordMatrix2 h1 hc2
  have h3 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0]) v =
      monsterCo1GeometryVectorPoint22WordMatrix3 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0, 3] 0
      monsterCo1GeometryVectorPoint22WordMatrix2 monsterCo1GeometryVectorPoint22WordMatrix3 h2 hc3
  have h4 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0, 1]) v =
      monsterCo1GeometryVectorPoint22WordMatrix4 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0, 3, 0] 1
      monsterCo1GeometryVectorPoint22WordMatrix3 monsterCo1GeometryVectorPoint22WordMatrix4 h3 hc4
  have h5 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0, 1, 4]) v =
      monsterCo1GeometryVectorPoint22WordMatrix5 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0, 3, 0, 1] 4
      monsterCo1GeometryVectorPoint22WordMatrix4 monsterCo1GeometryVectorPoint22WordMatrix5 h4 hc5
  have h6 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0, 1, 4, 0]) v =
      monsterCo1GeometryVectorPoint22WordMatrix6 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0, 3, 0, 1, 4] 0
      monsterCo1GeometryVectorPoint22WordMatrix5 monsterCo1GeometryVectorPoint22WordMatrix6 h5 hc6
  have h7 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0, 1, 4, 0, 4]) v =
      monsterCo1GeometryVectorPoint22Matrix *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0, 3, 0, 1, 4, 0] 4
      monsterCo1GeometryVectorPoint22WordMatrix6 monsterCo1GeometryVectorPoint22Matrix h6 hc7
  change co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0, 1, 4, 0, 4]) v = _
  exact h7 v

/-- The displayed inverse matrix of actual source transport 22. -/
def monsterCo1GeometryVectorPoint22InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0],
    ![1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0],
    ![1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0],
    ![0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1],
    ![0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0],
    ![1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint22Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint22Transport⁻¹ v =
      monsterCo1GeometryVectorPoint22InverseMatrix *ᵥ v := by
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint22Transport _ _
    monsterCo1GeometryVectorPoint22Transport_binary (by decide +kernel) v

/-- Source point 22 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint22 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint22Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint22_binary :
    monsterCo1GeometryVectorPoint22.val =
      ![0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint22Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint22Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
