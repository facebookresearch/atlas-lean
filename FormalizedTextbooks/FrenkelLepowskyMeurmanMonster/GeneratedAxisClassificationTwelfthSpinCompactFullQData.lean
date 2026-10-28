/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactBinaryCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Complete extraspecial coordinate caches for all genuine compact axis fixer candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Every actual compact coordinate cache retains its full central phase. -/
def generatedTwelfthSpinCompactFullQPhase : Fin 12 → Fin 24 → ZMod 2 :=
  ![
    ![0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0,
      1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1],
    ![0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0,
      1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0],
    ![1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1,
      0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0,
      1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0,
      1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0,
      0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
      1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0,
      1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0,
      0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0]
  ]

/-- The complete preferred coordinate image, retaining its full original binary base and phase. -/
def generatedTwelfthSpinCompactFullQCache (g : Fin 12) (j : Fin 24) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSpinCompactBinaryColumns g j)),
    ofAdd (generatedTwelfthSpinCompactFullQPhase g j)⟩

/-- Fast complete original coordinate-normal-form evaluator for every actual candidate. -/
def generatedTwelfthSpinCompactFullQFast (g : Fin 12) (q : Q) : Q :=
  monsterNortonCoordinateEvaluation (generatedTwelfthSpinCompactFullQCache g) q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
