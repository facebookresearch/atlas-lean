/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ContinuousDaySymmetry
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereDayMonoid
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoidCommutativity

/-!
# The original native orthogonal sphere Day monoid is commutative

The original ordered sphere tensorator intertwines the entire continuous
index block braid and smash symmetry. Its full coend descent therefore
makes the previously constructed original sphere monoid commutative.
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
attribute [local instance] OrthogonalIndex.symmetricCategory
attribute [local instance] Enriched.prodCategory

open OrthogonalSourceRightModule

/-- Commutativity on the exact constructed original sphere monoid under the actual native braid. -/
theorem sphereIsCommMonObj :
    letI := monoidalCategory.{u, v}
    letI := symmetricCategory.{u, v}
    letI := sphereMonObj.{u, v}
    IsCommMonObj sphereISpace.{u, v} :=
  EnrichedDayKernel.LaxMonoid.isCommMonObj
    OrthogonalIndex.enrichedMonoidalData.{u, v} OrthogonalIndex.enrichedSymmetricData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    orthogonalSphereBraidedData.{u, v}

/-- The constructed stock multiplication of the original native sphere is commutative. -/
theorem sphereMonoid_mul_comm :
    letI := monoidalCategory.{u, v}
    letI := symmetricCategory.{u, v}
    letI := sphereMonObj.{u, v}
    (β_ sphereISpace.{u, v} sphereISpace.{u, v}).hom ≫
      MonObj.mul (X := sphereISpace.{u, v}) = MonObj.mul := by
  let := monoidalCategory.{u, v}
  let := symmetricCategory.{u, v}
  let := sphereMonObj.{u, v}
  let := sphereIsCommMonObj.{u, v}
  exact IsCommMonObj.mul_comm sphereISpace.{u, v}

/-- The entire original sphere multiplication is invariant under the actual full coend braid. -/
theorem sphereDayMultiply_braid :
    (EnrichedDayKernel.BraidingFunctor.functorIso OrthogonalIndex.enrichedMonoidalData.{u, v}
      OrthogonalIndex.enrichedSymmetricData.{u, v} orthogonalSphereFunctor.{u, v}
      orthogonalSphereFunctor.{u, v}).hom ≫ sphereDayMultiply.{u, v} =
        sphereDayMultiply.{u, v} :=
  EnrichedDayKernel.LaxMonoid.multiply_braid
    OrthogonalIndex.enrichedMonoidalData.{u, v} OrthogonalIndex.enrichedSymmetricData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    orthogonalSphereBraidedData.{u, v}

end CategoryTheory.Spectra.OrthogonalDay
