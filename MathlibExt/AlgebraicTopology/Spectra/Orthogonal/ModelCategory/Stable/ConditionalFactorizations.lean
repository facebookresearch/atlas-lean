/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalModel

/-!
# Original full orthogonal factors in the conditional model

The conditional model uses the two entire original functorial records.
Only their membership is interpreted in the constructed model classes.
Every native Arrow, middle object, full Arrow action, injection,
projection and original realized cardinal retains its original value.

The existing six source algorithms and original Thom acyclicity are
preserved. Every conditional model view has the exact original comparison
premise as an explicit argument; no algorithm is rerun or supplied as
an assumed model outcome.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalFactorizations

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
  NativeK.generators_isCardinalForSmallObjectArgument

/-- The whole classified original I record is interpreted in the
single conditional actual model, retaining its entire original fields. -/
def IFactorizationData (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    FunctorialFactorizationData (cofibrations C.{u, v}) (trivialFibrations C.{u, v}) := by
  let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
  change FunctorialFactorizationData stableCofibrations stableTrivialFibrations
  exact classifiedIFactorizationData

/-- The whole classified original paired K record is interpreted in
those same conditional model classes with the unchanged Thom classification. -/
def KFactorizationData (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    FunctorialFactorizationData (trivialCofibrations C.{u, v}) (fibrations C.{u, v}) := by
  let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
  change FunctorialFactorizationData stableTrivialCofibrations stableFibrations
  exact classifiedKFactorizationData

/-- Both conditional records retain every complete field of the
corresponding original I/K algorithms. -/
theorem original_fields (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    (IFactorizationData hComparison).Z = originalIFactorizationData.Z ∧
      (IFactorizationData hComparison).i = originalIFactorizationData.i ∧
      (IFactorizationData hComparison).p = originalIFactorizationData.p ∧
      (KFactorizationData hComparison).Z = originalKFactorizationData.Z ∧
      (KFactorizationData hComparison).i = originalKFactorizationData.i ∧
      (KFactorizationData hComparison).p = originalKFactorizationData.p :=
  classifiedFactorization_original_fields

/-- Both full original middle objects use the caller's unchanged arrow
and precisely the original realized-generator cardinal. -/
theorem original_objects (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (F : Arrow C.{u, v}) :
    (IFactorizationData hComparison).Z.obj F =
        SmallObject.obj originalI realizedGeneratorCardinal.{v} F.hom ∧
      (KFactorizationData hComparison).Z.obj F =
        SmallObject.obj originalK realizedGeneratorCardinal.{v} F.hom :=
  factorization_objects F

/-- Every full native Arrow square retains both original same-cardinal middle maps. -/
theorem original_maps (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {F G : Arrow C.{u, v}} (f : F ⟶ G) :
    (IFactorizationData hComparison).Z.map f =
        SmallObject.objMap originalI realizedGeneratorCardinal.{v} f ∧
      (KFactorizationData hComparison).Z.map f =
        SmallObject.objMap originalK realizedGeneratorCardinal.{v} f :=
  factorization_maps f

/-- All four entire original factor legs are the same actual
same-cardinal small-object injections and projections. -/
theorem original_legs (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (F : Arrow C.{u, v}) :
    (IFactorizationData hComparison).i.app F =
        SmallObject.ιObj originalI realizedGeneratorCardinal.{v} F.hom ∧
      (IFactorizationData hComparison).p.app F =
        SmallObject.πObj originalI realizedGeneratorCardinal.{v} F.hom ∧
      (KFactorizationData hComparison).i.app F =
        SmallObject.ιObj originalK realizedGeneratorCardinal.{v} F.hom ∧
      (KFactorizationData hComparison).p.app F =
        SmallObject.πObj originalK realizedGeneratorCardinal.{v} F.hom :=
  factorization_legs F

/-- Both actual entire records factor the unchanged original input arrow. -/
theorem factorization_fac (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (F : Arrow C.{u, v}) :
    (IFactorizationData hComparison).i.app F ≫ (IFactorizationData hComparison).p.app F = F.hom ∧
      (KFactorizationData hComparison).i.app F ≫ (KFactorizationData hComparison).p.app F = F.hom :=
  NativeStableModels.factorization_fac F

/-- Every original Arrow square retains all four complete naturality
equations for the unchanged I/K factor records. -/
theorem factorization_naturality (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {F G : Arrow C.{u, v}} (f : F ⟶ G) :
    (IFactorizationData hComparison).i.app F ≫ (IFactorizationData hComparison).Z.map f =
        f.left ≫ (IFactorizationData hComparison).i.app G ∧
      (IFactorizationData hComparison).Z.map f ≫ (IFactorizationData hComparison).p.app G =
        (IFactorizationData hComparison).p.app F ≫ f.right ∧
      (KFactorizationData hComparison).i.app F ≫ (KFactorizationData hComparison).Z.map f =
        f.left ≫ (KFactorizationData hComparison).i.app G ∧
      (KFactorizationData hComparison).Z.map f ≫ (KFactorizationData hComparison).p.app G =
        (KFactorizationData hComparison).p.app F ≫ f.right :=
  NativeStableModels.factorization_naturality f

/-- The four original legs have their full memberships in the same
single conditional actual model, at every native Arrow input. -/
theorem factorization_membership (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (F : Arrow C.{u, v}) :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    cofibrations C.{u, v} ((IFactorizationData hComparison).i.app F) ∧
      trivialFibrations C.{u, v} ((IFactorizationData hComparison).p.app F) ∧
      trivialCofibrations C.{u, v} ((KFactorizationData hComparison).i.app F) ∧
      fibrations C.{u, v} ((KFactorizationData hComparison).p.app F) :=
  ⟨(IFactorizationData hComparison).hi F, (IFactorizationData hComparison).hp F,
    (KFactorizationData hComparison).hi F, (KFactorizationData hComparison).hp F⟩

/-- The two actual model WFS have precisely these full original
functorial factorization witnesses, without choosing new records. -/
theorem functorialFactorizations (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    HasFunctorialFactorization (cofibrations C.{u, v}) (trivialFibrations C.{u, v}) ∧
      HasFunctorialFactorization (trivialCofibrations C.{u, v}) (fibrations C.{u, v}) :=
  ⟨⟨⟨IFactorizationData hComparison⟩⟩, ⟨⟨KFactorizationData hComparison⟩⟩⟩

/-- Both whole original middle functors preserve every identity Arrow input. -/
theorem factorization_map_id (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (F : Arrow C.{u, v}) :
    (IFactorizationData hComparison).Z.map (𝟙 F) = 𝟙 ((IFactorizationData hComparison).Z.obj F) ∧
      (KFactorizationData hComparison).Z.map (𝟙 F) = 𝟙 ((KFactorizationData hComparison).Z.obj F) :=
  ⟨(IFactorizationData hComparison).Z.map_id F, (KFactorizationData hComparison).Z.map_id F⟩

/-- Both whole original middle functions preserve every pair of full native Arrow squares. -/
theorem factorization_map_comp (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {F G T : Arrow C.{u, v}} (f : F ⟶ G) (g : G ⟶ T) :
    (IFactorizationData hComparison).Z.map (f ≫ g) =
        (IFactorizationData hComparison).Z.map f ≫ (IFactorizationData hComparison).Z.map g ∧
      (KFactorizationData hComparison).Z.map (f ≫ g) =
        (KFactorizationData hComparison).Z.map f ≫ (KFactorizationData hComparison).Z.map g :=
  ⟨(IFactorizationData hComparison).Z.map_comp f g, (KFactorizationData hComparison).Z.map_comp f g⟩

end PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalFactorizations
