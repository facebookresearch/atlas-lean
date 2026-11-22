/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalStableModelConstruction
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.NativeStableIndexComparisons

/-!
# Stable weak reflection for the original spectrum restrictions

The original orthogonal K replacement followed by either the sequential or
symmetric restriction preserves and reflects the stable weak class on every
arrow. The same restrictions preserve and reflect actual stable fibrancy and
the stable weak class between fibrant objects.

These results use the existing complete restriction functors and original K
unit comparison. The native Omega tests are identified with the weak classes
of the three constructed stable models at the caller's generator-cardinal
bottom. No unit or Quillen-equivalence criterion is an additional premise.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.Spectra.NativeIndexKanComposition
open scoped CGWH.modelCategory MonoidalClosed

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

namespace PointedCGWH.Spectra.Orthogonal.IndexKan.NativeStableIndexComparisons

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] StableModelConstruction.sequentialModelCategory
  StableModelConstruction.symmetricModelCategory StableModelConstruction.orthogonalModelCategory

/-- The actual orthogonal K replacement followed by N restriction detects
the whole stable weak class, with arbitrary original endpoints. -/
theorem sequentialRightDerivedRestriction_stableWeak_iff
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Actual.OrthogonalCarrier.{u, v} f ↔
      weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
        (sequentialRightDerivedRestriction.map f) := by
  rw [StableModelConstruction.orthogonal_five_classes.1,
    StableModelConstruction.sequential_five_classes.1]
  exact (sequentialRightDerivedRestriction_omegaTests_iff f).symm

/-- The actual orthogonal K replacement followed by symmetric restriction
detects the whole stable weak class, with arbitrary original endpoints. -/
theorem symmetricRightDerivedRestriction_stableWeak_iff
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Actual.OrthogonalCarrier.{u, v} f ↔
      weakEquivalences Actual.SymmetricCarrier.{u, v}
        (symmetricRightDerivedRestriction.map f) := by
  rw [StableModelConstruction.orthogonal_five_classes.1,
    StableModelConstruction.symmetric_five_classes.1]
  exact (symmetricRightDerivedRestriction_omegaTests_iff f).symm

/-- N restriction preserves and reflects fibrancy in the actual native stable models. -/
theorem sequentialRestriction_isFibrant_iff (X : Actual.OrthogonalCarrier.{u, v}) :
    IsFibrant (sequentialOrthogonalRestriction.obj X) ↔ IsFibrant X := by
  exact (StableModelConstruction.sequential_isFibrant_iff_isOmega _).trans
    ((sequentialRestriction_isOmega_iff X).trans
      (StableModelConstruction.orthogonal_isFibrant_iff_isOmega X).symm)

/-- Symmetric restriction preserves and reflects fibrancy in the actual native stable models. -/
theorem symmetricRestriction_isFibrant_iff (X : Actual.OrthogonalCarrier.{u, v}) :
    IsFibrant (symmetricOrthogonalRestriction.obj X) ↔ IsFibrant X := by
  exact (StableModelConstruction.symmetric_isFibrant_iff_isOmega _).trans
    ((symmetricRestriction_isOmega_iff X).trans
      (StableModelConstruction.orthogonal_isFibrant_iff_isOmega X).symm)

/-- On actual fibrant orthogonal endpoints, the complete N restriction
preserves and reflects stable weak equivalences. -/
theorem sequentialRestriction_stableWeak_iff_of_isFibrant
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) [IsFibrant X] [IsFibrant Y] :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
        (sequentialOrthogonalRestriction.map f) ↔
      weakEquivalences Actual.OrthogonalCarrier.{u, v} f := by
  rw [StableModelConstruction.sequential_five_classes.1,
    StableModelConstruction.orthogonal_five_classes.1]
  exact sequentialRestriction_omegaTests_iff_of_isOmega f
    ((StableModelConstruction.orthogonal_isFibrant_iff_isOmega X).mp inferInstance)
    ((StableModelConstruction.orthogonal_isFibrant_iff_isOmega Y).mp inferInstance)

/-- On actual fibrant orthogonal endpoints, the complete symmetric restriction
preserves and reflects stable weak equivalences. -/
theorem symmetricRestriction_stableWeak_iff_of_isFibrant
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) [IsFibrant X] [IsFibrant Y] :
    weakEquivalences Actual.SymmetricCarrier.{u, v}
        (symmetricOrthogonalRestriction.map f) ↔
      weakEquivalences Actual.OrthogonalCarrier.{u, v} f := by
  rw [StableModelConstruction.symmetric_five_classes.1,
    StableModelConstruction.orthogonal_five_classes.1]
  exact symmetricRestriction_omegaTests_iff_of_isOmega f
    ((StableModelConstruction.orthogonal_isFibrant_iff_isOmega X).mp inferInstance)
    ((StableModelConstruction.orthogonal_isFibrant_iff_isOmega Y).mp inferInstance)

end PointedCGWH.Spectra.Orthogonal.IndexKan.NativeStableIndexComparisons
