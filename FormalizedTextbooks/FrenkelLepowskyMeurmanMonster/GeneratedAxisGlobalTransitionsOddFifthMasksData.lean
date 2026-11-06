/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStageData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Original full forward binary cocycle rows and central coefficients for both Fifth frames. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every triangular row retains the entire original normalized cocycle difference. -/
def generatedAxisGlobalOddFifthMaskRows : Fin 2 → Fin 24 → ℕ :=
![![14030006, 14471172, 11687560, 14123280, 8943264, 648320, 103168, 3708416, 6112256, 13935616, 8593408, 8388608, 14573568, 14024704, 14024704, 8388608, 0, 8912896, 8912896, 5242880, 0, 8388608, 8388608, 0], ![14028934, 177184, 12198072, 5640800, 3737024, 648832, 14030208, 5735168, 12301312, 5582848, 8564736, 8388608, 647168, 12091392, 3702784, 8912896, 14024704, 3670016, 12058624, 14680064, 6291456, 12582912, 8388608, 0]]

/-- The complete original central linear coefficients. -/
def generatedAxisGlobalOddFifthMaskCoefficients : Fin 2 → ℕ :=
![8917144, 12491833]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
