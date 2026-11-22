/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ContinuousDay
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingMonoidal

/-!
# Genuine symmetric continuous Day convolution on orthogonal I-spaces

The original continuous index block braid and pointed-CGWH smash braid
descend through the entire original enriched coend. Both Day hexagons and
symmetry use the original Day tensor, represented unit and associator.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.OrthogonalDay

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory Enriched.prodCategory

/-- The original continuous Day tensor is symmetric by the full coend braid and both hexagons. -/
@[instance_reducible]
def symmetricCategory :
    letI := monoidalCategory.{u, v}
    SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  EnrichedDayKernel.BraidingMonoidal.symmetricCategory
    OrthogonalIndex.enrichedMonoidalData.{u, v} OrthogonalIndex.enrichedSymmetricData.{u, v}

/-- The entire native braid is the actual original index/coefficient coend descent. -/
theorem braiding_eq_coend
    (F G : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :
    letI := monoidalCategory.{u, v}
    letI := symmetricCategory.{u, v}
    (β_ F G) = EnrichedDayKernel.BraidingFunctor.functorIso
      OrthogonalIndex.enrichedMonoidalData.{u, v} OrthogonalIndex.enrichedSymmetricData.{u, v}
      F.toEnrichedFunctor G.toEnrichedFunctor := rfl

end CategoryTheory.Spectra.OrthogonalDay
