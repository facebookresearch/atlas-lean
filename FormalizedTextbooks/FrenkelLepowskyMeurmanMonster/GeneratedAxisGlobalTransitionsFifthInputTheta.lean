/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthInputMaskData

/-! Original Parker-theta values for the fifty-six actual input octad codes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Candidate theta masks in the exact original input octad order. -/
def generatedAxisGlobalFifthInputThetaData : Fin 56 → ℕ :=
  ![1029, 1028, 624, 1537, 63, 78, 1077, 1092,
    1658, 523, 15, 14, 1030, 7, 123, 1146,
    215, 1238, 173, 1196, 1025, 0, 1036, 13,
    192, 1301, 651, 351, 1988, 16, 1022, 555,
    128, 1829, 715, 879, 1412, 32, 446, 539,
    1462, 1555, 397, 1065, 1730, 1894, 1160, 813,
    279, 1218, 1372, 1672, 1043, 967, 1577, 2044]

/-- Every cached theta mask is its complete actual original Parker-theta value. -/
theorem generatedAxisGlobalFifthInputThetaData_actual (j : Fin 56) :
    parkerThetaMask (generatedFifthEvenRootCode j).val =
      generatedAxisGlobalFifthInputThetaData j := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
