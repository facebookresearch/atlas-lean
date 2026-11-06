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

/-- The literal actual lattice word for source basis point 20. -/
def monsterCo1GeometryVectorPoint20Transport : Co1 :=
  QuotientGroup.mk (omegaOrbitWordIsometry (omegaOrbitWords 20))

/-- Complete displayed binary matrix of actual transport 20. -/
def monsterCo1GeometryVectorPoint20Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0],
    ![1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0],
    ![1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1],
    ![0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
    ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1],
    ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0],
    ![0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1],
    ![0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1],
    ![1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1],
    ![1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Complete prefix matrix 1 of original actual source word 20. -/
def monsterCo1GeometryVectorPoint20WordMatrix1 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
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

/-- Complete prefix matrix 2 of original actual source word 20. -/
def monsterCo1GeometryVectorPoint20WordMatrix2 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
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

/-- Complete prefix matrix 3 of original actual source word 20. -/
def monsterCo1GeometryVectorPoint20WordMatrix3 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
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

/-- Complete prefix matrix 4 of original actual source word 20. -/
def monsterCo1GeometryVectorPoint20WordMatrix4 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0],
    ![1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Complete prefix matrix 5 of original actual source word 20. -/
def monsterCo1GeometryVectorPoint20WordMatrix5 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0],
    ![1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0],
    ![0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1],
    ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1],
    ![1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1],
    ![1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 20 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint20Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint20Transport v =
      monsterCo1GeometryVectorPoint20Matrix *ᵥ v := by
  have hm0 : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hm1 : monsterCo1GeometryVectorPoint20WordMatrix1 = monsterCo1GeometryBinaryMaskMatrix
      ![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
        16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632] := by
        decide +kernel
  have hc1 : omegaOrbitBinaryMatrices 0 * (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
    monsterCo1GeometryVectorPoint20WordMatrix1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 0))
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608]
      ![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
        16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632]
      ((monsterCo1GeometryVectorFiveOperator_matrix 0).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 0)))
      hm0 hm1 (by decide +kernel)
  have hm2 : monsterCo1GeometryVectorPoint20WordMatrix2 = monsterCo1GeometryBinaryMaskMatrix
      ![57504, 8441984, 8450944, 8450432, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
        8445952, 4203168, 13684367, 1049249, 2106784, 3155872, 12811348, 12762360, 13147381,
        13392985, 9495771, 9495671, 4524557, 8389632] := by decide +kernel
  have hc2 : omegaOrbitBinaryMatrices 3 * monsterCo1GeometryVectorPoint20WordMatrix1 =
    monsterCo1GeometryVectorPoint20WordMatrix2 :=
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
  have hm3 : monsterCo1GeometryVectorPoint20WordMatrix3 = monsterCo1GeometryBinaryMaskMatrix
      ![161, 12635279, 15788942, 14739854, 8445968, 8446000, 8446144, 8446016, 8421584,
        8405104, 8389632, 4524557, 5250063, 1105921, 2155520, 3204096, 12811348, 12762360,
        13147381, 13392985, 9495771, 9495671, 338093, 58368] := by decide +kernel
  have hc3 : omegaOrbitBinaryMatrices 0 * monsterCo1GeometryVectorPoint20WordMatrix2 =
    monsterCo1GeometryVectorPoint20WordMatrix3 :=
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
  have hm4 : monsterCo1GeometryVectorPoint20WordMatrix4 = monsterCo1GeometryBinaryMaskMatrix
      ![49312, 8421584, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
        12635182, 9438720, 4524557, 10356230, 328204, 387341, 387853, 8646666, 8917002,
        8581126, 9179142, 4275234, 4512899, 338093, 58368] := by decide +kernel
  have hc4 : omegaOrbitBinaryMatrices 4 * monsterCo1GeometryVectorPoint20WordMatrix3 =
    monsterCo1GeometryVectorPoint20WordMatrix4 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 4))
      ![161, 12635279, 15788942, 14739854, 8445968, 8446000, 8446144, 8446016, 8421584,
        8405104, 8389632, 4524557, 5250063, 1105921, 2155520, 3204096, 12811348, 12762360,
        13147381, 13392985, 9495771, 9495671, 338093, 58368]
      ![49312, 8421584, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
        12635182, 9438720, 4524557, 10356230, 328204, 387341, 387853, 8646666, 8917002,
        8581126, 9179142, 4275234, 4512899, 338093, 58368]
      ((monsterCo1GeometryVectorFiveOperator_matrix 4).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 4)))
      hm3 hm4 (by decide +kernel)
  have hm5 : monsterCo1GeometryVectorPoint20WordMatrix5 = monsterCo1GeometryBinaryMaskMatrix
      ![128, 13691598, 12593359, 58593, 5270255, 9488081, 9487985, 5286511, 6327614, 7360286,
        9488032, 9815203, 6231749, 8712320, 323724, 8716416, 8388906, 209664, 143616, 8389414,
        10778801, 11843729, 13706275, 58368] := by decide +kernel
  have hc5 : omegaOrbitBinaryMatrices 3 * monsterCo1GeometryVectorPoint20WordMatrix4 =
    monsterCo1GeometryVectorPoint20WordMatrix5 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 3))
      ![49312, 8421584, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
        12635182, 9438720, 4524557, 10356230, 328204, 387341, 387853, 8646666, 8917002,
        8581126, 9179142, 4275234, 4512899, 338093, 58368]
      ![128, 13691598, 12593359, 58593, 5270255, 9488081, 9487985, 5286511, 6327614, 7360286,
        9488032, 9815203, 6231749, 8712320, 323724, 8716416, 8388906, 209664, 143616, 8389414,
        10778801, 11843729, 13706275, 58368]
      ((monsterCo1GeometryVectorFiveOperator_matrix 3).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 3)))
      hm4 hm5 (by decide +kernel)
  have hm6 : monsterCo1GeometryVectorPoint20Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![1098272, 6327614, 6327711, 10502577, 14683423, 2138369, 3171073, 15732543, 13691598,
        13691470, 5245582, 9815203, 11933707, 5258286, 383488, 4515362, 2139258, 10654928,
        11752560, 3171542, 10008689, 10254545, 13706275, 58368] := by decide +kernel
  have hc6 : omegaOrbitBinaryMatrices 4 * monsterCo1GeometryVectorPoint20WordMatrix5 =
    monsterCo1GeometryVectorPoint20Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      (monsterCo1GeometryBinaryOperatorMasks (monsterCo1GeometryVectorFiveOperator 4))
      ![128, 13691598, 12593359, 58593, 5270255, 9488081, 9487985, 5286511, 6327614, 7360286,
        9488032, 9815203, 6231749, 8712320, 323724, 8716416, 8388906, 209664, 143616, 8389414,
        10778801, 11843729, 13706275, 58368]
      ![1098272, 6327614, 6327711, 10502577, 14683423, 2138369, 3171073, 15732543, 13691598,
        13691470, 5245582, 9815203, 11933707, 5258286, 383488, 4515362, 2139258, 10654928,
        11752560, 3171542, 10008689, 10254545, 13706275, 58368]
      ((monsterCo1GeometryVectorFiveOperator_matrix 4).symm.trans
        (monsterCo1GeometryBinaryOperatorMasks_decode (monsterCo1GeometryVectorFiveOperator 4)))
      hm5 hm6 (by decide +kernel)
  have h0 := monsterCo1GeometryTransportWord_nil_binary
  have h1 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0]) v =
      monsterCo1GeometryVectorPoint20WordMatrix1 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [] 0
      (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) monsterCo1GeometryVectorPoint20WordMatrix1 h0 hc1
  have h2 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3]) v =
      monsterCo1GeometryVectorPoint20WordMatrix2 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0] 3
      monsterCo1GeometryVectorPoint20WordMatrix1 monsterCo1GeometryVectorPoint20WordMatrix2 h1 hc2
  have h3 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0]) v =
      monsterCo1GeometryVectorPoint20WordMatrix3 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0, 3] 0
      monsterCo1GeometryVectorPoint20WordMatrix2 monsterCo1GeometryVectorPoint20WordMatrix3 h2 hc3
  have h4 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0, 4]) v =
      monsterCo1GeometryVectorPoint20WordMatrix4 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0, 3, 0] 4
      monsterCo1GeometryVectorPoint20WordMatrix3 monsterCo1GeometryVectorPoint20WordMatrix4 h3 hc4
  have h5 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0, 4, 3]) v =
      monsterCo1GeometryVectorPoint20WordMatrix5 *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0, 3, 0, 4] 3
      monsterCo1GeometryVectorPoint20WordMatrix4 monsterCo1GeometryVectorPoint20WordMatrix5 h4 hc5
  have h6 : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0, 4, 3, 4]) v =
      monsterCo1GeometryVectorPoint20Matrix *ᵥ v :=
    monsterCo1GeometryTransportWord_append_binary [0, 3, 0, 4, 3] 4
      monsterCo1GeometryVectorPoint20WordMatrix5 monsterCo1GeometryVectorPoint20Matrix h5 hc6
  change co1BinaryAction (monsterCo1GeometryTransportWord [0, 3, 0, 4, 3, 4]) v = _
  exact h6 v

/-- Source point 20 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint20 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint20Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint20_binary :
    monsterCo1GeometryVectorPoint20.val =
      ![0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint20Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint20Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
