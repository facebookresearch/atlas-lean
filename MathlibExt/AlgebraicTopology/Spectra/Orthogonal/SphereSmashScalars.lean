/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereModuleStructure
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereDayCommutativity
public import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances
public import MathlibExt.CategoryTheory.Monoidal.RightModuleRelativeTensor

/-!
# Native orthogonal sphere scalar specialization

The scalar, module conversion and map conversion are direct abbreviations of
the shared right-module API at the original continuous sphere Day monoid.
The native facts identify that scalar's complete carrier, unit and multiplication.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.Orthogonal.SphereSmashScalars

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
attribute [local instance] Enriched.prodCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

/-- The genuine continuous orthogonal space category carrying the source Day tensor. -/
abbrev ISpace := EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex

attribute [local instance]
  NativeSphereModule.instMonoidalCategoryEnrichedFunctorCatOrthogonalIndex
  NativeSphereModule.instMonObjEnrichedFunctorCatOrthogonalIndexSphereISpace
  OrthogonalDay.symmetricCategory OrthogonalDay.sphereIsCommMonObj

/-- The complete original continuous sphere, bundled with its actual monoid and commutativity. -/
abbrev scalar : CommMon ISpace.{u, v} := RightModuleFree.scalarCommMon sphereISpace.{u, v}

/-- The named scalar retains the full original representation-sphere enriched functor. -/
@[simp]
theorem scalar_obj : scalar.{u, v}.X = sphereISpace.{u, v} := rfl

/-- The named scalar unit is the original entire sphere Day unit transformation. -/
theorem scalar_one :
    MonObj.one (X := scalar.{u, v}.X) = sphereDayUnit.{u, v} := rfl

/-- The named scalar multiplication is the original entire continuous sphere coend descent. -/
theorem scalar_mul :
    MonObj.mul (X := scalar.{u, v}.X) = sphereDayMultiply.{u, v} := rfl

/-- Convert the entire stock right sphere action through the original positive Day braid. -/
abbrev leftObject (X : NativeSphereModule.Carrier.{u, v}) : Mod ISpace.{u, v} scalar.{u, v}.X :=
  RightModuleFree.leftModule sphereISpace.{u, v} X

/-- Every whole source module map is converted by the original left-map function. -/
abbrev leftMap {X Y : NativeSphereModule.Carrier.{u, v}} (f : X ⟶ Y) :
    leftObject X ⟶ leftObject Y :=
  CommutativeModuleConversion.toLeftMap sphereISpace.{u, v} f

end PointedCGWH.Spectra.Orthogonal.SphereSmashScalars
