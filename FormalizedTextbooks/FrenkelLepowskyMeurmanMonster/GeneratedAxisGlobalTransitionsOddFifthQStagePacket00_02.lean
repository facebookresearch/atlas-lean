/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStageData

/-! A bounded packet checks the entire original primitive binary and central images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
-- Normalize only six original source stages, retaining every full preferred-Q coordinate.
set_option maxHeartbeats 200000000

/-- Every original primitive returns its whole next image, with the genuine central coefficient. -/
theorem generatedAxisGlobalOddFifthQStagePacket00_02 (n : Fin 6) (i : Fin 24) :
    generatedAxisGlobalOddFifthQStageCoordinate 0 ⟨12+n.val, by omega⟩ i =
      generatedAxisGlobalOddFifthQStageCache 0 ⟨12+n.val+1, by omega⟩ i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ (n : Fin 6) (i j : Fin 24),
        toAdd (generatedAxisGlobalOddFifthQStageCoordinate 0 ⟨12+n.val, by omega⟩ i).base j =
          toAdd (generatedAxisGlobalOddFifthQStageCache 0 ⟨12+n.val+1, by omega⟩ i).base j := by
      decide +kernel
    exact h n i j
  · apply toAdd.injective
    have h : ∀ (n : Fin 6) (i : Fin 24),
        toAdd (generatedAxisGlobalOddFifthQStageCoordinate 0 ⟨12+n.val, by omega⟩ i).coeff =
          toAdd (generatedAxisGlobalOddFifthQStageCache 0 ⟨12+n.val+1, by omega⟩ i).coeff := by
      decide +kernel
    exact h n i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
