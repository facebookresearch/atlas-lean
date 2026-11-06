/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Two exact finite bit identities certify a complete original extraspecial image. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- A complete output binary word and its original central bit determine the entire Q image. -/
theorem generatedAxisGlobalQMaskImage_certificate (cols rows : Fin 24 → ℕ)
    (coeff input output : ℕ) (phase : ZMod 2)
    (hb : generatedAxisGlobalQMaskVector cols input = output)
    (hc : (if (generatedAxisGlobalQMaskCentral rows coeff input).testBit 0 then
      (1 : ZMod 2) else 0) = phase) :
    generatedAxisGlobalQMaskImage cols rows coeff input =
      qCentral phase * generatedAxisGlobalQMask output := by
  apply NormalizedCocycleExtension.Extension.ext
  · change ofAdd (monsterCo1GeometryBinaryMaskDecode
      (generatedAxisGlobalQMaskVector cols input)) =
        1 * ofAdd (monsterCo1GeometryBinaryMaskDecode output)
    rw [hb, one_mul]
  · apply toAdd.injective
    change (if (generatedAxisGlobalQMaskCentral rows coeff input).testBit 0 then
      (1 : ZMod 2) else 0) = phase + 0 +
        qBeta 0 (monsterCo1GeometryBinaryMaskDecode output)
    rw [add_zero, qBeta_zero_left, add_zero]
    exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
