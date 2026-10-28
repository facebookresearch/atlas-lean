/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitData

/-! The first seventeen original genuine section generators are exact signed coordinate actions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- Exact physical source coordinate selected in each row by the original monomial generator. -/
def generatedTwelfthGoldenMonomialCoordinate : Fin 17 → Fin 8 → Fin 8 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![6, 1, 7, 3, 4, 5, 0, 2],
  ![0, 2, 1, 3, 5, 4, 6, 7],
  ![2, 3, 0, 1, 4, 5, 6, 7],
  ![0, 1, 2, 6, 5, 4, 3, 7],
  ![5, 0, 2, 6, 7, 3, 4, 1]
]

/-- Exact original sign in each physical source-generator row. -/
def generatedTwelfthGoldenMonomialSign : Fin 17 → Fin 8 → ℤ := ![
  ![1, 1, 1, 1, -1, -1, -1, -1],
  ![1, 1, 1, 1, -1, -1, -1, -1],
  ![1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, -1, -1, -1, -1],
  ![1, 1, 1, 1, 1, 1, -1, -1],
  ![1, 1, 1, 1, 1, -1, 1, -1],
  ![1, 1, 1, 1, 1, -1, 1, -1],
  ![1, 1, 1, 1, 1, -1, -1, 1],
  ![1, 1, -1, -1, 1, -1, -1, 1],
  ![1, -1, 1, -1, 1, 1, -1, -1],
  ![1, -1, -1, -1, -1, 1, 1, 1],
  ![-1, -1, -1, -1, -1, -1, -1, -1],
  ![1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1, 1, 1]
]

set_option maxRecDepth 10000 in
-- Check every original physical source-generator entry against its signed-coordinate action.
/-- All seventeen actual source matrices have these exact monomial rows. -/
theorem generatedTwelfthGoldenMonomial_source : ∀ (g : Fin 17) (i j : Fin 8),
    generatedTwelfthSectionGeneratorTwice (Fin.castLE (by decide : 17 ≤ 18) g) i j =
      2 * generatedTwelfthGoldenMonomialSign g i *
        (if generatedTwelfthGoldenMonomialCoordinate g i = j then (1 : ℤ) else 0) := by
  intro g i j
  fin_cases g <;> fin_cases i <;> fin_cases j <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
