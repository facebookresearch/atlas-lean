/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQStageData

/-! Complete original one-step coordinate checks for one genuine comparison word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 10000

/-- All original primitive images and their complete central phases at every stage. -/
theorem generatedAxisGlobalOddFourthQStageCheck03 (n : Fin 20) (i : Fin 24) :
    generatedAxisGlobalOddFourthQStageCoordinate 3 n i =
      generatedAxisGlobalOddFourthQStageCache 3 ⟨n.val + 1, by omega⟩ i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ n : Fin 20, ∀ i j : Fin 24,
        toAdd (generatedAxisGlobalOddFourthQStageCoordinate 3 n i).base j =
          toAdd (generatedAxisGlobalOddFourthQStageCache 3 ⟨n.val + 1, by omega⟩ i).base j := by decide +kernel
    exact h n i j
  · apply toAdd.injective
    have h : ∀ n : Fin 20, ∀ i : Fin 24,
        toAdd (generatedAxisGlobalOddFourthQStageCoordinate 3 n i).coeff =
          toAdd (generatedAxisGlobalOddFourthQStageCache 3 ⟨n.val + 1, by omega⟩ i).coeff := by decide +kernel
    exact h n i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
