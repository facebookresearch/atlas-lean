/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ColimitMonoidal
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.Index
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.CGWH.Colimits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Genuine continuous Day convolution on native orthogonal index spaces

The category on the original enriched functors is supplied by the actual
PointedCGWH colimits and the original orthogonal enriched tensor data.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Spectra
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.OrthogonalDay
attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory Enriched.prodCategory

/-- Ordinary native colimits supply the original continuous Day category on all orthogonal index
      spaces. -/
@[instance_reducible]
def monoidalCategory :
    MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  EnrichedDayKernel.ColimitMonoidal.monoidalCategory
    OrthogonalIndex.enrichedMonoidalData.{u, v}

end CategoryTheory.Spectra.OrthogonalDay
