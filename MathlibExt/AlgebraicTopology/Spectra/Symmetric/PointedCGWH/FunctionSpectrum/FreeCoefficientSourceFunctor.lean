/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSourceCoefficientBase
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeComparison

/-!
# Actual original coefficient source functor data

The entire coefficient free functor is the original sphere free functor.
The actual source of the full original module comparison equals the full
original internal-Hom functor used by the coefficient pre-map. This equality
retains every module object and target-module map and supplies both genuine
source isomorphisms. All sphere data and original closed choices remain fixed.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeScalarCoefficient

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev Sequence := PointedCGWH.SymmetricSequence.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided
  PointedCGWH.originalSymmetricSequenceSymmetric

open PointedCGWH.SymmetricModulePresentation
open NativeOmegaRecovery.NativeSymmetricFreeFunction

attribute [local instance] PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

open PointedCGWH.Spectra.NativeStableMonoidal

/-- The entire free coefficient functor retains the actual original sphere object and monoid. -/
theorem coefficientFreeFunctor_eq_original :
    Mod.free A.{u, v}.X = Mod.free S.{u, v} := rfl

/-- The actual source functor computes the original full module internal Hom. -/
def originalComparisonSourceFunctor (r : I) (M : V.{u, v}) :=
  letI : ∀ (F G : I ⥤ V.{u, v}) (c : I),
      CategoryTheory.Limits.HasEnd
        (((dayConvolutionInternalHomDiagramFunctor F).obj G).obj c) := by
    intro F G c
    infer_instance
  letI : MonoidalClosed Sequence.{u, v} :=
    CategoryTheory.MonoidalCategory.DayFunctor.instMonoidalClosed
  Mod.internalHom A.{u, v}
    ((Mod.free A.{u, v}.X).obj (DayFreeCoefficient.freeSequence r M))

/-- The original coefficient pre-map has this complete actual internal-Hom source functor. -/
def coefficientComparisonSourceFunctor (r : I) (M : V.{u, v}) :
    OriginalModule.{u, v} ⥤ OriginalModule.{u, v} :=
  Mod.internalHom A.{u, v} ((Mod.free A.{u, v}.X).obj (DayFreeCoefficient.freeSequence r M))

/-- The whole original source equality retains every module object and every target-module map. -/
theorem originalComparisonSourceFunctor_eq_coefficient (r : I) (M : V.{u, v}) :
    originalComparisonSourceFunctor r M = coefficientComparisonSourceFunctor r M := rfl

/-- Both complete original functor values are identified by the same proved actual
source equality. -/
def originalComparisonSourceIso (r : I) (M : V.{u, v}) :
    originalComparisonSourceFunctor r M ≅ coefficientComparisonSourceFunctor r M :=
  eqToIso (originalComparisonSourceFunctor_eq_coefficient r M)

end NativeOmegaRecovery.NativeScalarCoefficient
