/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitDataColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCorrectedGenerators

/-! Integer basis certificates for the actual original sixth spatial words. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Exact coordinate data for the original spatial word. -/
def sixthFrameOrbitBForward : Fin 24 → Fin 24 :=
  ![16, 17, 19, 20, 8, 14, 7, 1, 18, 21, 22, 23, 0, 6, 15, 9, 12, 5, 10, 3, 4, 11, 13, 2]

/-- Exact coordinate data for the original spatial word. -/
def sixthFrameOrbitBInverse : Fin 24 → Fin 24 :=
  ![12, 7, 23, 19, 20, 17, 13, 6, 4, 15, 18, 21, 16, 22, 5, 14, 0, 1, 8, 2, 3, 9, 10, 11]

/-- Exact coordinate data for the original spatial word. -/
def sixthFrameOrbitCForward : Fin 24 → Fin 24 :=
  ![18, 11, 7, 12, 23, 0, 22, 20, 17, 4, 13, 9, 15, 16, 5, 10, 1, 2, 21, 3, 14, 6, 8, 19]

/-- Exact coordinate data for the original spatial word. -/
def sixthFrameOrbitCInverse : Fin 24 → Fin 24 :=
  ![5, 16, 17, 19, 9, 14, 21, 2, 22, 11, 15, 1, 3, 10, 20, 12, 13, 8, 0, 23, 7, 18, 6, 4]

/-- Exact coordinate data for the original spatial word. -/
def sixthFrameOrbitSwapForward : Fin 24 → Fin 24 :=
  ![18, 5, 7, 4, 13, 21, 1, 10, 20, 0, 15, 9, 8, 22, 12, 2, 17, 16, 6, 19, 3, 11, 14, 23]

/-- Exact coordinate data for the original spatial word. -/
def sixthFrameOrbitSwapInverse : Fin 24 → Fin 24 :=
  ![9, 6, 15, 20, 3, 1, 18, 2, 12, 11, 7, 21, 14, 4, 22, 10, 17, 16, 0, 19, 8, 5, 13, 23]

/-- Original sign labels for the ten equal-sign generators. -/
def sixthFrameOrbitSignLabels : Fin 10 → Fin 4096 :=
  ![1, 2, 4, 8, 96, 176, 304, 528, 1056, 2048]

/-- Physical input-coordinate indices of fourteen generators and the two Xi transporters. -/
def sixthFrameOrbitSpatialInput : Fin 16 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![4, 7, 5, 6, 0, 2, 3, 1, 20, 21, 22, 23, 12, 13, 14, 15, 16, 17, 18, 19, 8, 9, 10, 11],
    ![11, 4, 13, 2, 5, 12, 10, 3, 21, 18, 22, 23, 6, 0, 15, 9, 16, 17, 20, 19, 8, 14, 1, 7],
    ![1, 21, 6, 13, 11, 8, 9, 18, 20, 12, 5, 3, 0, 14, 22, 4, 16, 17, 10, 19, 23, 2, 15, 7],
    ![9, 6, 15, 20, 3, 1, 18, 2, 12, 11, 7, 21, 14, 4, 22, 10, 17, 16, 0, 19, 8, 5, 13, 23],
    ![5, 16, 17, 19, 9, 14, 21, 2, 22, 11, 15, 1, 3, 10, 20, 12, 13, 8, 0, 23, 7, 18, 6, 4],
    ![18, 11, 7, 12, 23, 0, 22, 20, 17, 4, 13, 9, 15, 16, 5, 10, 1, 2, 21, 3, 14, 6, 8, 19]]

/-- Physical integer signs, with identity signs on the six actual permutation words. -/
def sixthFrameOrbitSpatialSign : Fin 16 → Fin 24 → ℤ :=
  ![![1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    ![1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1],
    ![1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1],
    ![1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, -1, -1],
    ![1, 1, 1, 1, 1, -1, 1, -1, 1, -1, -1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, -1, 1, -1],
    ![1, 1, -1, -1, 1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1, 1, 1, 1, 1, 1, -1, -1],
    ![1, -1, 1, -1, 1, 1, 1, 1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1, 1, 1, 1, -1, 1, -1],
    ![1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1],
    ![-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
      -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
