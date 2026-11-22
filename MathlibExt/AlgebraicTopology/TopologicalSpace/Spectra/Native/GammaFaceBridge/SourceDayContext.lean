/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaSmashFaces

/-!
# Source Day Context

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
noncomputable section
universe uV vV
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open scoped MonoidalClosed
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ]
  [HasColimitsOfSize.{0, 0} V] [HasProducts.{0} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V ℕ)

/-- Families of tensor comparisons between two free source diagrams and the free diagram at `t n
r`. -/
def SourceDiagramFamilyType (t : ℕ → ℕ → ℕ) : Type _ :=
  letI := q.dayMonoidal
  ∀ (n r : ℕ) (K L : V), Free.object n K ⊗ Free.object r L ≅ Free.object (t n r) (K ⊗ L)

/-- Natural isomorphisms from the selected source tensor to the Day bifunctor determined by `T`. -/
def SourceDayComparisonType (T : EnrichedFunctor V (ℕ × ℕ) ℕ) : Type _ :=
  letI := q.dayMonoidal
  tensor (EnrichedFunctorCat V ℕ) ≅ EnrichedDayKernel.Input.bifunctor T

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
