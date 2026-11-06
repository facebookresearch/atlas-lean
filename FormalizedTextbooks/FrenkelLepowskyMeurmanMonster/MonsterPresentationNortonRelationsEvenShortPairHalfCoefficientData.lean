/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact full sixth integer coefficients at twelve actual preferred basis entries. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Integer signs of the original V action at the twelve covered basis inputs. -/
def monsterNortonPairHalfInitialSign : Fin 12 → ℤ :=
  ![-1, -1, -1, 1, -1, -1, 1, -1, -1, -1, 1, -1]

/-- Integer numerators of all sixty-four true sixth-step short terms for each covered input. -/
def monsterNortonPairHalfSixthInteger : Fin 12 → Fin 64 → ℤ :=
  ![
    ![
      -1, -1, -1, -1, 1, 1, 1, 1,
      1, 1, 1, 1, -1, -1, -1, -1,
      1, 1, 1, 1, -1, -1, -1, -1,
      -1, -1, -1, -1, 1, 1, 1, 1,
      1, 1, 1, 1, -1, -1, -1, -1,
      -1, -1, -1, -1, 1, 1, 1, 1,
      -1, -1, -1, -1, 1, 1, 1, 1,
      1, 1, 1, 1, -1, -1, -1, -1
    ],
    ![
      -1, -1, 1, 1, -1, -1, 1, 1,
      1, 1, -1, -1, 1, 1, -1, -1,
      1, 1, -1, -1, 1, 1, -1, -1,
      -1, -1, 1, 1, -1, -1, 1, 1,
      1, 1, -1, -1, 1, 1, -1, -1,
      -1, -1, 1, 1, -1, -1, 1, 1,
      -1, -1, 1, 1, -1, -1, 1, 1,
      1, 1, -1, -1, 1, 1, -1, -1
    ],
    ![
      1, 1, -1, -1, -1, -1, 1, 1,
      1, 1, -1, -1, -1, -1, 1, 1,
      1, 1, -1, -1, -1, -1, 1, 1,
      1, 1, -1, -1, -1, -1, 1, 1,
      -1, -1, 1, 1, 1, 1, -1, -1,
      -1, -1, 1, 1, 1, 1, -1, -1,
      -1, -1, 1, 1, 1, 1, -1, -1,
      -1, -1, 1, 1, 1, 1, -1, -1
    ],
    ![
      -1, 1, -1, 1, 1, -1, 1, -1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      1, -1, 1, -1, -1, 1, -1, 1,
      1, -1, 1, -1, -1, 1, -1, 1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      1, -1, 1, -1, -1, 1, -1, 1,
      1, -1, 1, -1, -1, 1, -1, 1
    ],
    ![
      1, 1, -1, -1, -1, -1, 1, 1,
      1, 1, -1, -1, -1, -1, 1, 1,
      -1, -1, 1, 1, 1, 1, -1, -1,
      -1, -1, 1, 1, 1, 1, -1, -1,
      1, 1, -1, -1, -1, -1, 1, 1,
      1, 1, -1, -1, -1, -1, 1, 1,
      -1, -1, 1, 1, 1, 1, -1, -1,
      -1, -1, 1, 1, 1, 1, -1, -1
    ],
    ![
      1, 1, -1, -1, 1, 1, -1, -1,
      -1, -1, 1, 1, -1, -1, 1, 1,
      -1, -1, 1, 1, -1, -1, 1, 1,
      1, 1, -1, -1, 1, 1, -1, -1,
      1, 1, -1, -1, 1, 1, -1, -1,
      -1, -1, 1, 1, -1, -1, 1, 1,
      -1, -1, 1, 1, -1, -1, 1, 1,
      1, 1, -1, -1, 1, 1, -1, -1
    ],
    ![
      -1, 1, -1, 1, 1, -1, 1, -1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      1, -1, 1, -1, -1, 1, -1, 1,
      1, -1, 1, -1, -1, 1, -1, 1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      1, -1, 1, -1, -1, 1, -1, 1,
      1, -1, 1, -1, -1, 1, -1, 1
    ],
    ![
      1, -1, 1, -1, 1, -1, 1, -1,
      -1, 1, -1, 1, -1, 1, -1, 1,
      1, -1, 1, -1, 1, -1, 1, -1,
      -1, 1, -1, 1, -1, 1, -1, 1,
      -1, 1, -1, 1, -1, 1, -1, 1,
      1, -1, 1, -1, 1, -1, 1, -1,
      -1, 1, -1, 1, -1, 1, -1, 1,
      1, -1, 1, -1, 1, -1, 1, -1
    ],
    ![
      1, -1, 1, -1, -1, 1, -1, 1,
      1, -1, 1, -1, -1, 1, -1, 1,
      1, -1, 1, -1, -1, 1, -1, 1,
      1, -1, 1, -1, -1, 1, -1, 1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      -1, 1, -1, 1, 1, -1, 1, -1
    ],
    ![
      1, -1, 1, -1, -1, 1, -1, 1,
      1, -1, 1, -1, -1, 1, -1, 1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      1, -1, 1, -1, -1, 1, -1, 1,
      1, -1, 1, -1, -1, 1, -1, 1,
      -1, 1, -1, 1, 1, -1, 1, -1,
      -1, 1, -1, 1, 1, -1, 1, -1
    ],
    ![
      1, 1, 1, 1, -1, -1, -1, -1,
      1, 1, 1, 1, -1, -1, -1, -1,
      1, 1, 1, 1, -1, -1, -1, -1,
      1, 1, 1, 1, -1, -1, -1, -1,
      -1, -1, -1, -1, 1, 1, 1, 1,
      -1, -1, -1, -1, 1, 1, 1, 1,
      -1, -1, -1, -1, 1, 1, 1, 1,
      -1, -1, -1, -1, 1, 1, 1, 1
    ],
    ![
      1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1
    ]
  ]

/-- The finite original signs equal their actual real qSign values. -/
theorem monsterNortonPairHalfInitialSign_actual (k : Fin 12) :
    qSign (monsterNortonEvenShortInitialVPhase (monsterNortonPairHalfBasisIndex k)) =
      (monsterNortonPairHalfInitialSign k : ℝ) := by
  fin_cases k <;> norm_num [monsterNortonPairHalfBasisIndex,
    monsterNortonEvenShortInitialVPhase, monsterNortonPairHalfInitialSign, qSign]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 32000000 in
-- Check all 768 complete finite phase numerators through the frozen actual Q data.
/-- The coefficient cache equals the complete actual sixth-step integer expression. -/
theorem monsterNortonPairHalfSixthInteger_actual (k : Fin 12) (e : Fin 64) :
    monsterNortonEvenShortSixthInteger (monsterNortonPairHalfBasisIndex k) e =
      monsterNortonPairHalfSixthInteger k e := by
  revert k e
  decide +kernel

/-- Each cached numerator gives the full real coefficient in the literal seventh packet. -/
theorem monsterNortonPairHalfSixthCoefficient_integer (k : Fin 12) (e : Fin 64) :
    monsterNortonEvenShortSixthCoefficient (monsterNortonPairHalfBasisIndex k) e =
      (monsterNortonPairHalfSixthInteger k e : ℝ) / 8 := by
  rw [monsterNortonEvenShortSixthInteger_actual, monsterNortonPairHalfSixthInteger_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
