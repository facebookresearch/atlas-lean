/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCacheData

/-! Check all twenty-four full coordinate images of original signed odd source letter 3. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 80000000 in
-- The kernel checks 24 original finite source formulas, retaining all central phases.
/-- Every cached coordinate image agrees with the complete actual signed source formula. -/
theorem generatedAxisGlobalOddLetterQCache03_certificate (i : Fin 24) :
    generatedAxisGlobalOddSourceLetterQImage 3 (qCoordinateGenerator i) =
      generatedAxisGlobalOddLetterQCache 3 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24,
        toAdd (generatedAxisGlobalOddSourceLetterQImage 3 (qCoordinateGenerator i)).base j =
          toAdd (generatedAxisGlobalOddLetterQCache 3 i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24,
        toAdd (generatedAxisGlobalOddSourceLetterQImage 3 (qCoordinateGenerator i)).coeff =
          toAdd (generatedAxisGlobalOddLetterQCache 3 i).coeff := by decide +kernel
    exact h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
