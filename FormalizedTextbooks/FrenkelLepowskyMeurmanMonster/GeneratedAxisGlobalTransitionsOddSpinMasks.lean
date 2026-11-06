/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorSignFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorFactorPackets

/-! Complete integer spin packets stored in sixteen bounded physical bit masks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The physical spin coordinate's block in a complete sixteen-block packet. -/
def generatedAxisGlobalOddSpinMaskBlock (k : Fin 4096) : Fin 16 :=
  ⟨k.val / 256, by have hk := k.isLt; omega⟩

/-- A complete integer spin vector, retaining all positive, negative, and zero coordinates. -/
def generatedAxisGlobalOddMaskedSpin (positive negative : Fin 16 → ℕ)
    (amplitude : ℤ) (k : Fin 4096) : ℤ :=
  amplitude *
    (if Nat.testBit (positive (generatedAxisGlobalOddSpinMaskBlock k)) (k.val % 256)
      then 1 else if Nat.testBit (negative (generatedAxisGlobalOddSpinMaskBlock k))
        (k.val % 256) then -1 else 0)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
