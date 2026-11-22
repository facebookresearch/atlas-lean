/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Original
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Factories
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.NativeFreeSourceComparison

/-!
# Function spectra on symmetric operator diagrams

Module internal Hom and balanced smash are transported through the equivalence between
sphere modules and symmetric operator diagrams. The function-spectrum bifunctor is
contravariant in its source and right adjoint to balanced smash; free/evaluation
comparisons identify its free-source specialization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaPreparation.NativeSymmetricFunction
attribute [local instance] PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  SymmetricFunction.sequenceClosed SymmetricFunction.sequenceCoequalizers
  SymmetricFunction.sequenceEqualizers

/-- The complete existing native carrier equivalence retains its actual module source. -/
abbrev carrierEquivalence :=
  PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

/-- The original actual module internal Hom has both lawful native source and native target
variance. -/
def bifunctor :
    (EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})ᵒᵖ ⥤
    (EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  ModuleFunctionTransport.bifunctor PointedCGWH.sphereSequenceCommMon.{u, v}
    carrierEquivalence.{u, v}

/-- The actual function-spectrum functor retains the given entire native source object. -/
def functor (A : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} :=
  bifunctor.{u, v}.obj (.op A)

/-- Balanced smash retains that same actual native source through its original module image. -/
def smashFunctor
    (A : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} :=
  CategoryTheory.Mod.EquivalenceFunctionTransport.smashFunctor
    PointedCGWH.sphereSequenceCommMon.{u, v} carrierEquivalence.{u, v} A

/-- The original balanced module adjunction and original carrier adjunctions provide the actual
native function-spectrum adjunction. -/
def adjunction
    (A : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    smashFunctor A ⊣ functor A :=
  (CategoryTheory.Mod.EquivalenceFunctionTransport.parametrizedAdjunction
    PointedCGWH.sphereSequenceCommMon.{u, v} carrierEquivalence.{u, v}).adj A

/-- Every whole original native source arrow acts contravariantly through its unchanged full module
image. -/
def precompose
    {A B : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}}
    (f : A ⟶ B) : functor B ⟶ functor A :=
  ModuleFunctionTransport.precompose PointedCGWH.sphereSequenceCommMon.{u, v}
    carrierEquivalence.{u, v} f

/-- The actual original left-free and native enriched free comparisons identify both entire
function-spectrum functors. -/
def originalFreeComparison (n : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    SymmetricFunction.functor n M ≅
      functor (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} n) M) :=
  ModuleFunctionTransport.sourceComparison PointedCGWH.sphereSequenceCommMon.{u, v}
    carrierEquivalence.{u, v} ((Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n).obj M)
    (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} n) M)
    ((SymmetricNativeFree.comparison.{u, v} n).app M)

end NativeOmegaPreparation.NativeSymmetricFunction
