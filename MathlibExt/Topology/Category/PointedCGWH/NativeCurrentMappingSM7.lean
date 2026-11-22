/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingCorner
public import MathlibExt.CategoryTheory.Functor.PushoutObjObj.Transport
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarCompatibility
public import MathlibExt.CategoryTheory.Enriched.ScalarCorners

/-!
# Mapping-corner lifting for pointed enriched diagrams

The mapping corner of a cofibration and a fibration is a fibration in pointed spaces. It is a trivial fibration when either input is trivial. Each statement retains the specified pullback corner in the native level model.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.CurrentMappingSM7

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf Native.modelCategory
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The whole original mapping corner of a projective cofibration and fibration is fibrant. -/
theorem fibration
    {F G X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (j : F ⟶ G) (p : X ⟶ Y)
    (hj : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) j)
    (hp : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) p)
    (pb : WeightedEndVariance.bifunctor.PullbackObjObj j p) :
    fibrations PointedCGWH.{u, v} pb.π := by
  rw [← trivialCofibrations_rlp]
  rw [← trivialCofibrations_rlp] at hp
  intro M N i hi
  let po := Functor.PushoutObjObj.ofHasPushout
    (WeightedEndVariance.tensorBifunctor (V := PointedCGWH.{u, v}) (I := A)) i j
  let oldPo := Functor.PushoutObjObj.transport
    (by rfl) po
  have hpo := ScalarCompatibility.scalarPushoutProduct_trivial_left i j hi hj oldPo
  have hArrow := Functor.PushoutObjObj.transport_arrow_heq
    (by rfl) po
  have hSame : oldPo.ι = po.ι := eq_of_heq hArrow
  rw [hSame] at hpo
  exact (PointedCGWH.NativeMappingCorner.lifting_iff po pb).mp (hp _ hpo)

/-- Original projective trivial source cofibrations give whole mapping trivial fibrations. -/
theorem trivial_left
    {F G X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (j : F ⟶ G) (p : X ⟶ Y)
    (hj : trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) j)
    (hp : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) p)
    (pb : WeightedEndVariance.bifunctor.PullbackObjObj j p) :
    trivialFibrations PointedCGWH.{u, v} pb.π := by
  rw [← cofibrations_rlp]
  rw [← trivialCofibrations_rlp] at hp
  intro M N i hi
  let po := Functor.PushoutObjObj.ofHasPushout
    (WeightedEndVariance.tensorBifunctor (V := PointedCGWH.{u, v}) (I := A)) i j
  let oldPo := Functor.PushoutObjObj.transport
    (by rfl) po
  have hpo := ScalarCompatibility.scalarPushoutProduct_trivial_right i j hi hj oldPo
  have hArrow := Functor.PushoutObjObj.transport_arrow_heq
    (by rfl) po
  have hSame : oldPo.ι = po.ι := eq_of_heq hArrow
  rw [hSame] at hpo
  exact (PointedCGWH.NativeMappingCorner.lifting_iff po pb).mp (hp _ hpo)

/-- Original projective trivial target fibrations give whole mapping trivial fibrations. -/
theorem trivial_right
    {F G X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (j : F ⟶ G) (p : X ⟶ Y)
    (hj : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) j)
    (hp : trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) p)
    (pb : WeightedEndVariance.bifunctor.PullbackObjObj j p) :
    trivialFibrations PointedCGWH.{u, v} pb.π := by
  rw [← cofibrations_rlp]
  rw [← cofibrations_rlp] at hp
  intro M N i hi
  let po := Functor.PushoutObjObj.ofHasPushout
    (WeightedEndVariance.tensorBifunctor (V := PointedCGWH.{u, v}) (I := A)) i j
  let oldPo := Functor.PushoutObjObj.transport
    (by rfl) po
  have hpo := ScalarCompatibility.scalarPushoutProduct_cofibration i j hi hj oldPo
  have hArrow := Functor.PushoutObjObj.transport_arrow_heq
    (by rfl) po
  have hSame : oldPo.ι = po.ι := eq_of_heq hArrow
  rw [hSame] at hpo
  exact (PointedCGWH.NativeMappingCorner.lifting_iff po pb).mp (hp _ hpo)

end HomotopicalAlgebra.EnrichedProjective.Native.CurrentMappingSM7
