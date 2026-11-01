/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonQCacheData

/-! Check every full original coordinate image before using the three comparison caches. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem comparisonRoot_generator (k : Fin 9) (i : Fin 24) :
    generatedAxisGlobalOddRootQFast k (qCoordinateGenerator i) =
      generatedAxisGlobalOddRootQCache k i :=
  (generatedAxisGlobalOddRootQFast_actual k
    (generatedAxisGlobalOddRootQCache_certificate k) _).symm.trans
      (generatedAxisGlobalOddRootQCache_certificate k i)

/-- The executable coordinate formula uses the already proved full original root image. -/
def generatedAxisGlobalOddComparisonCoordinateSource (k : Fin 3) (i : Fin 24) : Q :=
  let r := generatedAxisGlobalSignFullImage (generatedAxisGlobalOddComparisonSign k)
    (generatedAxisGlobalOddRootQCache (generatedAxisGlobalOddComparisonRoot k) i)
  generatedAxisGlobalOddComparisonQ k * r * (generatedAxisGlobalOddComparisonQ k)⁻¹

/-- Replacing a root generator evaluation uses its proved phase-correct source certificate. -/
theorem generatedAxisGlobalOddComparisonCoordinateSource_actual (k : Fin 3) (i : Fin 24) :
    generatedAxisGlobalOddComparisonQImage k (qCoordinateGenerator i) =
      generatedAxisGlobalOddComparisonCoordinateSource k i := by
  unfold generatedAxisGlobalOddComparisonQImage generatedAxisGlobalOddComparisonCoordinateSource
  rw [comparisonRoot_generator]

set_option maxHeartbeats 80000000 in
-- Check all 72 complete original coordinate images and all their central signs.
/-- Every cached coordinate image is the complete genuine local source image. -/
theorem generatedAxisGlobalOddComparisonQCache_certificate (k : Fin 3) (i : Fin 24) :
    generatedAxisGlobalOddComparisonQImage k (qCoordinateGenerator i) =
      generatedAxisGlobalOddComparisonQCache k i := by
  rw [generatedAxisGlobalOddComparisonCoordinateSource_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ k : Fin 3, ∀ i j : Fin 24,
        toAdd (generatedAxisGlobalOddComparisonCoordinateSource k i).base j =
          toAdd (generatedAxisGlobalOddComparisonQCache k i).base j := by decide +kernel
    exact h k i j
  · apply toAdd.injective
    have h : ∀ k : Fin 3, ∀ i : Fin 24,
        toAdd (generatedAxisGlobalOddComparisonCoordinateSource k i).coeff =
          toAdd (generatedAxisGlobalOddComparisonQCache k i).coeff := by decide +kernel
    exact h k i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
