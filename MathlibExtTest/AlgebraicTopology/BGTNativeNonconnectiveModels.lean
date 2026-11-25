/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicTopology.BGTNativeNonconnectiveModels

/-!
# Tests for the nonconnective K tower

The `n`-th term of the nonconnective tower is `Ωⁿ QK(Σⁿ C)`, and its map from term `n` to term
`n + 1` is the loop image of the boundary of the `n`-th stage.
-/

noncomputable section

open CategoryTheory
open MathlibExt.AlgebraicTopology.BGTNativeNonconnectiveModels
open MathlibExt.AlgebraicTopology.NativeKParametrizedSource
open MathlibExt.AlgebraicTopology.NativeSpectraSimplicialSource
open MathlibExt.AlgebraicTopology.NativeEnrichedSpectrumReplacements
open MathlibExt.AlgebraicTopology.NativeSpectrumConeSources
open MathlibExt.AlgebraicTopology.StableSpectraInfinitySource
open MathlibExt.AlgebraicTopology.StableInfinityCategoryModels
open MathlibExt.AlgebraicTopology.BGTIndKappaModels
open MathlibExt.AlgebraicTopology.StableInfinityFilteredColimits

variable {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
  {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
  (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
  (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal}
  (P : SigmaKappaSystem k) (B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C)
  (C : StableInfinityCategory.{0})

/-- The terms of the tower are its native terms `Ωⁿ QK(Σⁿ C)`. -/
example (n : ℕ) : (nonconnectiveTower K R L P B C).obj n = towerTerm K R P C n :=
  rfl

/-- The map from term `n` to term `n + 1` is the transition built from the `n`-th boundary. -/
example (n : ℕ) :
    (nonconnectiveTower K R L P B C).map (homOfLE (Nat.le_succ n)) =
      towerTransition K R L P B C n :=
  Functor.ofSequence_map_homOfLE_succ _ n
