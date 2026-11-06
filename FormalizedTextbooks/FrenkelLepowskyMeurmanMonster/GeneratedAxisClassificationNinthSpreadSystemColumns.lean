/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemData

/-! The displayed compact columns bind to the eighteen original integral section isometries. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every compact intrinsic column is the reduction of the corresponding actual root action. -/
theorem generatedNinth_spread_columns_eq : ∀ g : Fin 18,
    sixthFrameOrbitColumnMatrix (generatedNinthSpreadColumns g) =
      generatedFifthSectionGeneratorBinary g := by
  decide +kernel

/-- The four-bit coefficient of a source basis image in its stated target system. -/
def generatedNinthSpreadSystemCoefficient (g : Fin 18) (k : Fin 270) (j : Fin 4) :
    Fin 4 → ZMod 2 := monsterCo1GeometryBinaryMaskDecode
      (generatedNinthSpreadSystemCoefficientLabels g k j).val

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
