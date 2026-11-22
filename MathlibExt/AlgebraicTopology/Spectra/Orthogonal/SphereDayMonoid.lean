/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ContinuousDay
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceSphereDayArrows
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoidAssembly

/-!
# The original orthogonal sphere monoid in genuine continuous Day convolution

The original one-point representation spheres, enriched isometry actions,
unit and ordered sphere tensorators define a monoid on the actual orthogonal
I-space category. The unit and multiplication remain the existing complete
Yoneda-extension and continuous-coend arrows.
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

/-- The exact original sphere is a monoid under the constructed continuous Day category. -/
@[instance_reducible]
def sphereMonObj :
    letI := monoidalCategory.{u, v}
    MonObj sphereISpace.{u, v} :=
  EnrichedDayKernel.LaxMonoid.monObj OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}

/-- The original sphere, bundled in the stock category of monoids. -/
def sphereMonoid :
    letI := monoidalCategory.{u, v}
    Mon (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) := by
  letI := monoidalCategory.{u, v}
  letI := sphereMonObj.{u, v}
  exact Mon.mk sphereISpace.{u, v}

/-- The bundled monoid retains the original complete enriched sphere object. -/
theorem sphereMonoid_X_eq_original :
    letI := monoidalCategory.{u, v}
    sphereMonoid.{u, v}.X = sphereISpace.{u, v} := rfl

/-- The monoid unit is the exact original enriched Yoneda extension of the sphere epsilon. -/
theorem sphereMonoid_one_eq_original :
    letI := monoidalCategory.{u, v}
    letI := sphereMonObj.{u, v}
    MonObj.one (X := sphereISpace.{u, v}) = sphereDayUnit.{u, v} := rfl

/-- The monoid multiplication is the exact original full continuous coend descent. -/
theorem sphereMonoid_mul_eq_original :
    letI := monoidalCategory.{u, v}
    letI := sphereMonObj.{u, v}
    MonObj.mul (X := sphereISpace.{u, v}) = sphereDayMultiply.{u, v} := rfl

/-- Every full native generator uses the original ordered tensorator and entire isometry action. -/
theorem sphereMonoid_gen_multiply (k : OrthogonalIndex) (a : OrthogonalIndex × OrthogonalIndex) :
    letI := monoidalCategory.{u, v}
    letI := sphereMonObj.{u, v}
    EnrichedDayKernel.gen OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v} k a ≫
        EnrichedFunctorCat.component (MonObj.mul (X := sphereISpace.{u, v})) k =
      (𝟙 (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k) ⊗ₘ
        orthogonalSphereMonoidalData.{u, v}.mu a.1 a.2) ≫
        (β_ (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k)
          (orthogonalSphereFunctor.{u, v}.obj (a.1 + a.2))).hom ≫
        MonoidalClosed.uncurry (orthogonalSphereFunctor.{u, v}.map (a.1 + a.2) k) :=
  gen_sphereDayMultiply k a

/-- Every entire unit component is the original epsilon acting on the full native Hom object. -/
theorem sphereMonoid_unit_component (k : OrthogonalIndex) :
    letI : Category OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI := monoidalCategory.{u, v}
    letI := sphereMonObj.{u, v}
    EnrichedFunctorCat.component (MonObj.one (X := sphereISpace.{u, v})) k =
      GradedYoneda.component (𝟙_ OrthogonalIndex) orthogonalSphereFunctor.{u, v}
        orthogonalSphereMonoidalData.{u, v}.epsilon k := by
  let : Category OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  exact GradedYoneda.extend_component (𝟙_ OrthogonalIndex) orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v}.epsilon k

/-- The constructed native sphere monoid satisfies the whole left unit law. -/
theorem sphereMonoid_one_mul :
    letI := monoidalCategory.{u, v}
    letI := sphereMonObj.{u, v}
    (MonObj.one (X := sphereISpace.{u, v}) ▷ sphereISpace.{u, v}) ≫
      MonObj.mul (X := sphereISpace.{u, v}) = (λ_ sphereISpace.{u, v}).hom := by
  let := monoidalCategory.{u, v}
  let := sphereMonObj.{u, v}
  exact MonObj.one_mul sphereISpace.{u, v}

/-- The constructed native sphere monoid satisfies the whole right unit law. -/
theorem sphereMonoid_mul_one :
    letI := monoidalCategory.{u, v}
    letI := sphereMonObj.{u, v}
    (sphereISpace.{u, v} ◁ MonObj.one (X := sphereISpace.{u, v})) ≫
      MonObj.mul (X := sphereISpace.{u, v}) = (ρ_ sphereISpace.{u, v}).hom := by
  let := monoidalCategory.{u, v}
  let := sphereMonObj.{u, v}
  exact MonObj.mul_one sphereISpace.{u, v}

/-- The constructed native sphere monoid satisfies the original full Day associator equation. -/
theorem sphereMonoid_mul_assoc :
    letI := monoidalCategory.{u, v}
    letI := sphereMonObj.{u, v}
    (MonObj.mul (X := sphereISpace.{u, v}) ▷ sphereISpace.{u, v}) ≫
      MonObj.mul (X := sphereISpace.{u, v}) =
      (α_ sphereISpace.{u, v} sphereISpace.{u, v} sphereISpace.{u, v}).hom ≫
        (sphereISpace.{u, v} ◁ MonObj.mul (X := sphereISpace.{u, v})) ≫
        MonObj.mul (X := sphereISpace.{u, v}) := by
  let := monoidalCategory.{u, v}
  let := sphereMonObj.{u, v}
  exact MonObj.mul_assoc sphereISpace.{u, v}

end CategoryTheory.Spectra.OrthogonalDay
