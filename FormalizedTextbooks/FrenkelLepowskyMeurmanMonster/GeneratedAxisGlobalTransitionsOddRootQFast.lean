/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCacheData

/-! A complete actual root product is determined by 24 phase-correct coordinate images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Compact full-phase evaluation from one root product's complete coordinate-image table. -/
def generatedAxisGlobalOddRootQFast (k : Fin 9) (q : Q) : Q :=
  monsterNortonCoordinateEvaluation (generatedAxisGlobalOddRootQCache k) q

/-- The exact 24 finite source image checks determine the complete genuine root Q action. -/
theorem generatedAxisGlobalOddRootQFast_actual (k : Fin 9)
    (hk : ∀ i, generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords k)
      (qCoordinateGenerator i) = generatedAxisGlobalOddRootQCache k i) (q : Q) :
    generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords k) q =
      generatedAxisGlobalOddRootQFast k q := by
  rw [← generatedAxisGlobalOddSourceFastRoot_actual]
  apply monsterNortonCoordinateEvaluation_eq
  intro i
  rw [generatedAxisGlobalOddSourceFastRoot_actual]
  exact hk i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
