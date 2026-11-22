/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Lambda
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableMonoidalAssembly
import MathlibExt.CategoryTheory.Monoidal.Mod.TransportedFunctionUnit

/-!
# The original native lambda and its selected source adjunction

The function unit determines its left unit by the original adjoint-uniqueness
construction. The native source map, that same selected unit, and both directions
of the actual balanced-smash adjunction give the characteristic equations for
lambda. Every source index, input map, and coefficient parameter is retained.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory CategoryTheory.Limits
open scoped MonoidalClosed

namespace NativeOmegaRecovery.NativeSymmetricLambdaAdjunction

universe u v
open CategoryTheory.EnrichedFunctorCat

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev E := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
private abbrev FreeZero :=
  Free.object (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I)) (𝟙_ V.{u, v})
private abbrev FreeOne :=
  Free.object (PointedCGWH.symmetricOperatorObj.{u, v} NativeSymmetricDelooping.firstIndex)
    PointedCGWH.sphereOne.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.originalSymmetricSequenceMonoidal PointedCGWH.originalSymmetricSequenceBraided
  PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers

open PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

attribute [local irreducible] CategoryTheory.Mod.internalHom
  CategoryTheory.MonoidalCategory.DayFunctor.inst
  CategoryTheory.MonoidalCategory.DayFunctor.instBraidedCategory

/-- The original entire balanced source bifunctor on the native carrier. -/
def sourceSmashBifunctor : Carrier.{u, v} ⥤ (Carrier.{u, v} ⥤ Carrier.{u, v}) :=
  CategoryTheory.Mod.EquivalenceFunctionTransport.smashBifunctor.{v + 1, v, v + 1, v} A.{u, v}
    E.{u, v}

/-- Each source value is exactly the existing native balanced-smash functor. -/
theorem sourceSmashBifunctor_obj (S : Carrier.{u, v}) :
    sourceSmashBifunctor.{u, v}.obj S =
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} S := rfl

/-- Every complete native source arrow is its original transported module tensor map. -/
def sourceSmashMap {S T : Carrier.{u, v}} (f : S ⟶ T) :
    NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} S ⟶
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} T :=
  CategoryTheory.Mod.EquivalenceFunctionTransport.sourceSmashMap.{v + 1, v, v + 1, v} A.{u, v}
    E.{u, v} f

/-- The native source map retains the whole original module-transport initializer. -/
theorem sourceSmashMap_original {S T : Carrier.{u, v}} (f : S ⟶ T) :
    sourceSmashMap.{u, v} f =
      CategoryTheory.Mod.EquivalenceFunctionTransport.sourceSmashMap.{v + 1, v, v + 1, v} A.{u, v}
        E.{u, v} f := rfl

/-- The covariant source bifunctor uses that same entire native source arrow. -/
theorem sourceSmashBifunctor_map_heq {S T : Carrier.{u, v}} (f : S ⟶ T) :
    HEq (sourceSmashBifunctor.{u, v}.map f) (sourceSmashMap.{u, v} f) := by
  unfold sourceSmashBifunctor sourceSmashMap
    CategoryTheory.Mod.EquivalenceFunctionTransport.sourceSmashMap
  exact HEq.refl _

/-- The contravariant source bifunctor uses the original native precomposition. -/
theorem bifunctor_map {S T : Carrier.{u, v}} (f : S ⟶ T) :
    NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v}.map f.op =
      NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f := rfl

/-- The original balanced module and carrier adjunctions retain source naturality. -/
def sourceParametrizedAdjunction :
    sourceSmashBifunctor.{u, v} ⊣₂ NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v}
      :=
  CategoryTheory.Mod.EquivalenceFunctionTransport.parametrizedAdjunction.{v + 1, v, v + 1, v}
    A.{u, v} E.{u, v}

/-- Its selected component is exactly the existing actual native adjunction. -/
theorem sourceParametrizedAdjunction_adj (S : Carrier.{u, v}) :
    sourceParametrizedAdjunction.{u, v}.adj S =
      NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} S := by
  unfold sourceParametrizedAdjunction NativeOmegaPreparation.NativeSymmetricFunction.adjunction
  rfl

/-- The free-zero unit uses the same original function-unit adjoint uniqueness. -/
theorem freeZeroSmashUnitIso_hom_original :
    freeZeroSmashUnitIso.{u, v}.hom =
      (FunctionUnitAdjunction.leftUnitIso
        (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeZero.{u, v})
        NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}).hom := by
  unfold FunctionUnitAdjunction.leftUnitIso
    freeZeroSmashUnitIso
  rfl

/-- The original free-zero selected left unit has exactly the given inverse adjunct. -/
theorem freeZeroUnit_adjoint (X : Carrier.{u, v}) :
    let F : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeZero.{u, v}
    let G : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} FreeZero.{u, v}
    let adj : F ⊣ G :=
      NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeZero.{u, v}
    let left : F ≅ 𝟭 Carrier.{u, v} := freeZeroSmashUnitIso.{u, v}
    let unit : G ≅ 𝟭 Carrier.{u, v} :=
      NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}
    (adj.homEquiv X X) (left.hom.app X) = unit.inv.app X := by
  dsimp only
  exact @FunctionUnitAdjunction.unitIso_adjoint_of_hom_eq.{v + 1, v}
    Carrier.{u, v} inferInstance
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeZero.{u, v})
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} FreeZero.{u, v})
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeZero.{u, v})
    NativeSymmetricFreeFunction.nativeUnitComparison.{u, v} freeZeroSmashUnitIso.{u, v}
    freeZeroSmashUnitIso_hom_original.{u, v} X

/-- The whole contravariant source value is exactly the existing native function functor. -/
theorem bifunctor_obj (S : Carrier.{u, v}) :
    NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v}.obj (.op S) =
      NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} S := rfl

/-- The full actual native component is compared before any original Hom projection. -/
theorem sourceParametrizedAdjunction_adj_heq (S : Carrier.{u, v}) :
    HEq (sourceParametrizedAdjunction.{u, v}.adj S)
      (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} S) := by
  exact heq_of_eq (sourceParametrizedAdjunction_adj S)

/-- The actual source pre-map is compared before its target component is projected. -/
theorem bifunctor_map_heq {S T : Carrier.{u, v}} (f : S ⟶ T) :
    HEq (NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v}.map f.op)
      (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f) := by
  unfold NativeOmegaPreparation.NativeSymmetricFunction.precompose
  exact HEq.refl _

/-- The exact original whole-functor component recipe supplies native source naturality. -/
theorem sourceAdjunctionEquation {S T : Carrier.{u, v}} (f : S ⟶ T)
    {X Y : Carrier.{u, v}}
    (g : (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} T).obj X ⟶ Y) :
    type_of% (FunctionUnitAdjunction.sourcePre_adjoint_of_whole_eq
    (P := Carrier.{u, v}) (C := Carrier.{u, v}) (D := Carrier.{u, v})
    (L := sourceSmashBifunctor.{u, v})
    (R := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v})
    sourceParametrizedAdjunction.{u, v} f
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} T)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} T)
    (sourceSmashBifunctor_obj S) (sourceSmashBifunctor_obj T)
    (bifunctor_obj S) (bifunctor_obj T)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} T)
    (sourceParametrizedAdjunction_adj_heq S)
    (sourceParametrizedAdjunction_adj_heq T)
    (sourceSmashMap.{u, v} f) (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
    (sourceSmashBifunctor_map_heq f) (bifunctor_map_heq f) (X := X) (Y := Y) g) :=
  FunctionUnitAdjunction.sourcePre_adjoint_of_whole_eq
    (P := Carrier.{u, v}) (C := Carrier.{u, v}) (D := Carrier.{u, v})
    (L := sourceSmashBifunctor.{u, v})
    (R := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v})
    sourceParametrizedAdjunction.{u, v} f
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} T)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} T)
    (sourceSmashBifunctor_obj S) (sourceSmashBifunctor_obj T)
    (bifunctor_obj S) (bifunctor_obj T)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} T)
    (sourceParametrizedAdjunction_adj_heq S)
    (sourceParametrizedAdjunction_adj_heq T)
    (sourceSmashMap.{u, v} f) (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
    (sourceSmashBifunctor_map_heq f) (bifunctor_map_heq f) (X := X) (Y := Y) g

/-- The chosen native free-zero unit is the same entire original left-unit constructor. -/
theorem freeZeroSmashUnitIso_original :
    freeZeroSmashUnitIso.{u, v} =
      FunctionUnitAdjunction.leftUnitIso
        (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeZero.{u, v})
        NativeSymmetricFreeFunction.nativeUnitComparison.{u, v} := by
  apply Iso.ext
  exact freeZeroSmashUnitIso_hom_original

/-- Every original unit-index coaugmentation uses the entire given unit and source pre-map. -/
theorem sourceCoaugmentation_original (r : I) :
    NativeSymmetricLambda.sourceCoaugmentation.{u, v} r =
      NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}.inv ≫
        NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v}
          (NativeSymmetricLambda.unitStabilization r) := rfl

/-- The original complete native source/unit formula is folded before source coefficients are
  specialized. -/
theorem sourceUnit_adjoint {S T : Carrier.{u, v}} (f : S ⟶ T)
    (leftIso : NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} T ≅ 𝟭
      Carrier.{u, v})
    (unitIso : NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} T ≅ 𝟭 Carrier.{u, v})
    (hLeft : leftIso = FunctionUnitAdjunction.leftUnitIso
      (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} T) unitIso)
    (η : 𝟭 Carrier.{u, v} ⟶ NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} S)
    (hη : η = unitIso.inv ≫ NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
    (X : Carrier.{u, v}) :
    type_of% (FunctionUnitAdjunction.sourcePre_unit_adjoint_of_whole_eq
    (P := Carrier.{u, v}) (C := Carrier.{u, v})
    (L := sourceSmashBifunctor.{u, v})
    (R := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v})
    sourceParametrizedAdjunction.{u, v} f
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} T)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} T)
    (sourceSmashBifunctor_obj S) (sourceSmashBifunctor_obj T)
    (bifunctor_obj S) (bifunctor_obj T)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} T)
    (sourceParametrizedAdjunction_adj_heq S) (sourceParametrizedAdjunction_adj_heq T)
    leftIso unitIso hLeft
    (sourceSmashMap.{u, v} f) (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
    (@sourceSmashBifunctor_map_heq.{u, v} S T f) (@bifunctor_map_heq.{u, v} S T f)
    η hη X) :=
  FunctionUnitAdjunction.sourcePre_unit_adjoint_of_whole_eq
    (P := Carrier.{u, v}) (C := Carrier.{u, v})
    (L := sourceSmashBifunctor.{u, v})
    (R := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v})
    sourceParametrizedAdjunction.{u, v} f
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} T)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} T)
    (sourceSmashBifunctor_obj S) (sourceSmashBifunctor_obj T)
    (bifunctor_obj S) (bifunctor_obj T)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} T)
    (sourceParametrizedAdjunction_adj_heq S) (sourceParametrizedAdjunction_adj_heq T)
    leftIso unitIso hLeft
    (sourceSmashMap.{u, v} f) (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
    (@sourceSmashBifunctor_map_heq.{u, v} S T f) (@bifunctor_map_heq.{u, v} S T f)
    η hη X

/-- The original complete native source/unit formula is folded before source coefficients are
  specialized. -/
theorem sourceUnit_uncurried {S T : Carrier.{u, v}} (f : S ⟶ T)
    (leftIso : NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} T ≅ 𝟭
      Carrier.{u, v})
    (unitIso : NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} T ≅ 𝟭 Carrier.{u, v})
    (hLeft : leftIso = FunctionUnitAdjunction.leftUnitIso
      (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} T) unitIso)
    (η : 𝟭 Carrier.{u, v} ⟶ NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} S)
    (hη : η = unitIso.inv ≫ NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
    (X : Carrier.{u, v}) :
    type_of% (FunctionUnitAdjunction.sourcePre_unit_uncurried_of_whole_eq
    (P := Carrier.{u, v}) (C := Carrier.{u, v})
    (L := sourceSmashBifunctor.{u, v})
    (R := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v})
    sourceParametrizedAdjunction.{u, v} f
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} T)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} T)
    (sourceSmashBifunctor_obj S) (sourceSmashBifunctor_obj T)
    (bifunctor_obj S) (bifunctor_obj T)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} T)
    (sourceParametrizedAdjunction_adj_heq S) (sourceParametrizedAdjunction_adj_heq T)
    leftIso unitIso hLeft
    (sourceSmashMap.{u, v} f) (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
    (@sourceSmashBifunctor_map_heq.{u, v} S T f) (@bifunctor_map_heq.{u, v} S T f)
    η hη X) :=
  FunctionUnitAdjunction.sourcePre_unit_uncurried_of_whole_eq
    (P := Carrier.{u, v}) (C := Carrier.{u, v})
    (L := sourceSmashBifunctor.{u, v})
    (R := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v})
    sourceParametrizedAdjunction.{u, v} f
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} T)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} T)
    (sourceSmashBifunctor_obj S) (sourceSmashBifunctor_obj T)
    (bifunctor_obj S) (bifunctor_obj T)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} S)
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} T)
    (sourceParametrizedAdjunction_adj_heq S) (sourceParametrizedAdjunction_adj_heq T)
    leftIso unitIso hLeft
    (sourceSmashMap.{u, v} f) (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
    (@sourceSmashBifunctor_map_heq.{u, v} S T f) (@bifunctor_map_heq.{u, v} S T f)
    η hη X

/-- Every original unit-index source retains the same entire original unit/source mate. -/
theorem sourceCoaugmentation_adjoint (r : I) (X : Carrier.{u, v}) :
    type_of% (@sourceUnit_adjoint.{u, v} (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
      ((𝟙_ I) ⊗ r))
      (PointedCGWH.sphereSequence.{u, v}.functor.obj r)) FreeZero.{u, v}
    (NativeSymmetricLambda.unitStabilization.{u, v} r)
    freeZeroSmashUnitIso.{u, v} NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}
    freeZeroSmashUnitIso_original.{u, v}
    (NativeSymmetricLambda.sourceCoaugmentation.{u, v} r) (sourceCoaugmentation_original r) X) :=
  @sourceUnit_adjoint.{u, v} (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r))
      (PointedCGWH.sphereSequence.{u, v}.functor.obj r)) FreeZero.{u, v}
    (NativeSymmetricLambda.unitStabilization.{u, v} r)
    freeZeroSmashUnitIso.{u, v} NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}
    freeZeroSmashUnitIso_original.{u, v}
    (NativeSymmetricLambda.sourceCoaugmentation.{u, v} r) (sourceCoaugmentation_original r) X

/-- Every original unit-index source retains the same entire original unit/source mate. -/
theorem sourceCoaugmentation_uncurried (r : I) (X : Carrier.{u, v}) :
    type_of% (@sourceUnit_uncurried.{u, v} (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
      ((𝟙_ I) ⊗ r))
      (PointedCGWH.sphereSequence.{u, v}.functor.obj r)) FreeZero.{u, v}
    (NativeSymmetricLambda.unitStabilization.{u, v} r)
    freeZeroSmashUnitIso.{u, v} NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}
    freeZeroSmashUnitIso_original.{u, v}
    (NativeSymmetricLambda.sourceCoaugmentation.{u, v} r) (sourceCoaugmentation_original r) X) :=
  @sourceUnit_uncurried.{u, v} (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r))
      (PointedCGWH.sphereSequence.{u, v}.functor.obj r)) FreeZero.{u, v}
    (NativeSymmetricLambda.unitStabilization.{u, v} r)
    freeZeroSmashUnitIso.{u, v} NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}
    freeZeroSmashUnitIso_original.{u, v}
    (NativeSymmetricLambda.sourceCoaugmentation.{u, v} r) (sourceCoaugmentation_original r) X

/-- The literal firstSource retains the original native lambda adjunct. -/
theorem firstSource_lambda_adjoint (X : Carrier.{u, v}) :
    let F : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeOne.{u, v}
    let G : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} FreeOne.{u, v}
    let adj : F ⊣ G :=
      NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeOne.{u, v}
    let F₀ : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeZero.{u, v}
    let zeroUnit : F₀ ≅ 𝟭 Carrier.{u, v} := freeZeroSmashUnitIso.{u, v}
    let source : F ⟶ F₀ :=
      sourceSmashMap.{u, v} (S := FreeOne.{u, v}) (T := FreeZero.{u, v})
        NativeSymmetricLambda.firstSource.{u, v}
    let η : 𝟭 Carrier.{u, v} ⟶ G := NativeSymmetricLambda.coaugmentation.{u, v}
    (adj.homEquiv X X) (source.app X ≫ zeroUnit.hom.app X) = η.app X := by
  dsimp only
  exact @sourceUnit_adjoint.{u, v} FreeOne.{u, v} FreeZero.{u, v}
    NativeSymmetricLambda.firstSource.{u, v} freeZeroSmashUnitIso.{u, v}
    NativeSymmetricFreeFunction.nativeUnitComparison.{u, v} freeZeroSmashUnitIso_original.{u, v}
    NativeSymmetricLambda.coaugmentation.{u, v}
    NativeSymmetricLambda.coaugmentation_original.{u, v} X

/-- The inverse uses that same literal lambda and original free-zero unit. -/
theorem firstSource_lambda_uncurried (X : Carrier.{u, v}) :
    let F : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeOne.{u, v}
    let G : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} FreeOne.{u, v}
    let adj : F ⊣ G :=
      NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeOne.{u, v}
    let F₀ : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeZero.{u, v}
    let zeroUnit : F₀ ≅ 𝟭 Carrier.{u, v} := freeZeroSmashUnitIso.{u, v}
    let source : F ⟶ F₀ :=
      sourceSmashMap.{u, v} (S := FreeOne.{u, v}) (T := FreeZero.{u, v})
        NativeSymmetricLambda.firstSource.{u, v}
    let η : 𝟭 Carrier.{u, v} ⟶ G := NativeSymmetricLambda.coaugmentation.{u, v}
    (adj.homEquiv X X).symm (η.app X) = source.app X ≫ zeroUnit.hom.app X := by
  dsimp only
  exact @sourceUnit_uncurried.{u, v} FreeOne.{u, v} FreeZero.{u, v}
    NativeSymmetricLambda.firstSource.{u, v} freeZeroSmashUnitIso.{u, v}
    NativeSymmetricFreeFunction.nativeUnitComparison.{u, v} freeZeroSmashUnitIso_original.{u, v}
    NativeSymmetricLambda.coaugmentation.{u, v}
    NativeSymmetricLambda.coaugmentation_original.{u, v} X

/-- The complete original source adjunct is a natural transformation of the actual functors. -/
def sourceAdjunct : NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v}
    FreeOne.{u, v} ⟶ 𝟭 Carrier.{u, v} :=
  { sourceSmashMap.{u, v} (S := FreeOne.{u, v}) (T := FreeZero.{u, v})
      NativeSymmetricLambda.firstSource ≫ freeZeroSmashUnitIso.{u, v}.hom with
    app := fun X =>
      (sourceSmashMap.{u, v} (S := FreeOne.{u, v}) (T := FreeZero.{u, v})
        NativeSymmetricLambda.firstSource).app X ≫ freeZeroSmashUnitIso.{u, v}.hom.app X }

/-- The whole adjunct retains the given module source map and the original chosen free-zero unit.
-/
theorem sourceAdjunct_original :
    sourceAdjunct.{u, v} =
      sourceSmashMap.{u, v} (S := FreeOne.{u, v}) (T := FreeZero.{u, v})
        NativeSymmetricLambda.firstSource ≫ freeZeroSmashUnitIso.{u, v}.hom := by
  rfl

/-- Every original native target arrow commutes with the whole source adjunct. -/
theorem sourceAdjunct_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeOne.{u, v}).map f ≫
      sourceAdjunct.{u, v}.app Y = sourceAdjunct.{u, v}.app X ≫ f :=
  sourceAdjunct.{u, v}.naturality f

/-- The selected natural transformation has exactly the literal native lambda adjunct. -/
theorem sourceAdjunct_adjoint (X : Carrier.{u, v}) :
    let F : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeOne.{u, v}
    let G : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} FreeOne.{u, v}
    let adj : F ⊣ G :=
      NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeOne.{u, v}
    let source : F ⟶ 𝟭 Carrier.{u, v} := sourceAdjunct.{u, v}
    let η : 𝟭 Carrier.{u, v} ⟶ G := NativeSymmetricLambda.coaugmentation.{u, v}
    (adj.homEquiv X X) (source.app X) = η.app X := by
  dsimp only
  unfold sourceAdjunct
  exact firstSource_lambda_adjoint X

/-- Every original target parameter retains the same complete native lambda source. -/
theorem sourceAdjunct_target_parameter {P X : Carrier.{u, v}} (a : P ⟶ X) :
    type_of% (@FunctionUnitAdjunction.sourceAdjunct_target_of_mate.{v + 1, v}
    Carrier.{u, v} inferInstance
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeOne.{u, v})
    NativeSymmetricR.functor.{u, v}
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeOne.{u, v})
    sourceAdjunct.{u, v} NativeSymmetricLambda.coaugmentation.{u, v}
    (fun Y => sourceAdjunct_adjoint Y) P X a) :=
  @FunctionUnitAdjunction.sourceAdjunct_target_of_mate.{v + 1, v}
    Carrier.{u, v} inferInstance
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeOne.{u, v})
    NativeSymmetricR.functor.{u, v}
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeOne.{u, v})
    sourceAdjunct.{u, v} NativeSymmetricLambda.coaugmentation.{u, v}
    (fun Y => sourceAdjunct_adjoint Y) P X a

/-- Every source parameter retains the original left input of the actual lambda adjunction. -/
theorem sourceAdjunct_input_parameter {P X : Carrier.{u, v}} (a : P ⟶ X) :
    type_of% (@FunctionUnitAdjunction.sourceAdjunct_input_of_mate.{v + 1, v}
    Carrier.{u, v} inferInstance
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeOne.{u, v})
    NativeSymmetricR.functor.{u, v}
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeOne.{u, v})
    sourceAdjunct.{u, v} NativeSymmetricLambda.coaugmentation.{u, v}
    (fun Y => sourceAdjunct_adjoint Y) P X a) :=
  @FunctionUnitAdjunction.sourceAdjunct_input_of_mate.{v + 1, v}
    Carrier.{u, v} inferInstance
    (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeOne.{u, v})
    NativeSymmetricR.functor.{u, v}
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeOne.{u, v})
    sourceAdjunct.{u, v} NativeSymmetricLambda.coaugmentation.{u, v}
    (fun Y => sourceAdjunct_adjoint Y) P X a

/-- Every genuine native free coefficient parameter uses that same entire source formula. -/
theorem sourceAdjunct_free_parameter (X : Carrier.{u, v}) (m : I) (W : V.{u, v})
    (a : Free.object (PointedCGWH.symmetricOperatorObj.{u, v} m) W ⟶ X) :
    let P : Carrier.{u, v} := Free.object (PointedCGWH.symmetricOperatorObj.{u, v} m) W
    let b : P ⟶ X := a
    let F : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeOne.{u, v}
    let G : Carrier.{u, v} ⥤ Carrier.{u, v} :=
      NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} FreeOne.{u, v}
    let adj : F ⊣ G :=
      NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} FreeOne.{u, v}
    let source : F ⟶ 𝟭 Carrier.{u, v} := sourceAdjunct.{u, v}
    let η : 𝟭 Carrier.{u, v} ⟶ G := NativeSymmetricLambda.coaugmentation.{u, v}
    (adj.homEquiv P X) (F.map b ≫ source.app X) = b ≫ η.app X := by
  exact sourceAdjunct_input_parameter a

/-- The complete original operator Hom remains natural under the actual source adjunct. -/
theorem sourceAdjunct_fullHom (X : Carrier.{u, v})
    (j k : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    let SX := (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} FreeOne.{u,
      v}).obj X
    MonoidalClosed.uncurry (SX.toEnrichedFunctor.map j k) ≫ component (sourceAdjunct.{u, v}.app X)
      k =
      (component (sourceAdjunct.{u, v}.app X) j ⊗ₘ 𝟙 (j ⟶[V.{u, v}] k)) ≫
        MonoidalClosed.uncurry (X.toEnrichedFunctor.map j k) :=
  (sourceAdjunct.{u, v}.app X).uncurriedNaturality j k

end NativeOmegaRecovery.NativeSymmetricLambdaAdjunction
