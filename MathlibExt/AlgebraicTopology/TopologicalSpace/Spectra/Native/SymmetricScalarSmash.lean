/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableMonoidalAssembly
public import Mathlib.CategoryTheory.Adjunction.Unique
public import MathlibExt.CategoryTheory.Monoidal.TensorRepresentedInterchange

/-!
# Scalar tensor and the original symmetric sphere smash

The original free-function comparison in degree zero and the actual index
unit shift identify smash with the original zero-free coefficient spectrum
with the actual scalar tensor. The original monoidal associator then
compares scalar tensor of a smash with smash of the scalar tensor.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed


namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash

/-- The category of pointed symmetric spectra presented as enriched functors on the symmetric
operator index. -/
abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

/-- The original native free spectrum in degree zero at an arbitrary pointed coefficient. -/
def zeroFree (T : PointedCGWH.{u, v}) : Carrier.{u, v} :=
  Free.object (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ Operad.SmallFinBijGroupoid)) T

/-- The original function spectrum from zero-free T is the actual pointwise scalar cotensor by T. -/
def functionScalarIso (T : PointedCGWH.{u, v}) :
    NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v} (zeroFree T) ≅ cotensor T :=
  NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeFreeComparison
      (𝟙_ Operad.SmallFinBijGroupoid) T ≪≫
    Functor.isoWhiskerRight NativeOmegaRecovery.NativeSymmetricShiftUnit.comparison (cotensor T) ≪≫
      Functor.leftUnitor (cotensor T)

/-- The two original adjunctions construct the complete zero-free smash/scalar comparison. -/
def originalSmashScalarIso (T : PointedCGWH.{u, v}) :
    NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} (zeroFree T) ≅
      EnrichedFunctorCat.tensorLeft T :=
  ((NativeOmegaPreparation.NativeSymmetricFunction.adjunction (zeroFree T)).ofNatIsoRight
    (functionScalarIso T)).leftAdjointUniq (ScalarLeibniz.adjunction T)

/-- The actual transported sphere tensor with zero-free T is the actual native scalar tensor by T. -/
def tensorScalarIso (T : PointedCGWH.{u, v}) :
    MonoidalCategory.tensorLeft (zeroFree T) ≅ EnrichedFunctorCat.tensorLeft T :=
  eqToIso (PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.tensorLeft_eq_originalSmash
    (zeroFree T)) ≪≫ originalSmashScalarIso T

/-- Scalar tensor of the original arbitrary two-spectrum smash uses the original associator. -/
def scalarSmashIso (T : PointedCGWH.{u, v}) (X Y : Carrier.{u, v}) :
    tensorLeftObject T (X ⊗ Y) ≅ tensorLeftObject T X ⊗ Y :=
  CategoryTheory.TensorRepresentedInterchange.interchange
    (zeroFree T) (EnrichedFunctorCat.tensorLeft T) (tensorScalarIso T) X Y

/-- The whole actual scalar-smash comparison is natural in both arbitrary original spectrum maps. -/
@[reassoc]
theorem scalarSmashIso_naturality (T : PointedCGWH.{u, v})
    {X X' Y Y' : Carrier.{u, v}} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorLeftMap T (f ⊗ₘ g) ≫ (scalarSmashIso T X' Y').hom =
      (scalarSmashIso T X Y).hom ≫ (tensorLeftMap T f ⊗ₘ g) :=
  CategoryTheory.TensorRepresentedInterchange.interchange_naturality
    (zeroFree T) (EnrichedFunctorCat.tensorLeft T)
    (tensorScalarIso T) f g

/-- The same original scalar-smash components form the complete comparison on all first-spectrum inputs. -/
def scalarSmashFunctorIso (T : PointedCGWH.{u, v}) (Y : Carrier.{u, v}) :
    MonoidalCategory.tensorRight Y ⋙ EnrichedFunctorCat.tensorLeft T ≅
      EnrichedFunctorCat.tensorLeft T ⋙ MonoidalCategory.tensorRight Y :=
  CategoryTheory.TensorRepresentedInterchange.interchangeFunctorIso
    (zeroFree T) (EnrichedFunctorCat.tensorLeft T) (tensorScalarIso T) Y

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash
