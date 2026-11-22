/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Native
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Factories
public import MathlibExt.CategoryTheory.Monoidal.Mod.FreeSourceTransport
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OperatorStabilizationK

/-!
# Free module and operator sources for symmetric spectra

The module/operator carrier equivalence identifies free sphere modules with the
corresponding free enriched objects. Transported source maps commute with the
function-spectrum comparison for all indices and coefficients, including the symmetric
stabilization map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeSymmetricFreeSource
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev NativeCarrier :=
  EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

open PointedCGWH.SymmetricModulePresentation

/-- Bind the existing full Hom-indexed native coproduct family before the
original free-module object, comparison and source arrow are constructed. -/
local instance originalFreeIndexedCoproducts :
    ∀ (a b : Operad.SmallFinBijGroupoid),
      HasCoproductsOfShape (a ⟶ b) PointedCGWH.{u, v} :=
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts.{u, v}

/-- The unchanged original sphere Day free module. -/
abbrev freeModule (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :=
  (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} r).obj M

/-- The unchanged native free object on the same entire original operator index. -/
abbrev nativeFree (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :=
  Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) M

/-- The complete existing free/evaluation adjunctions supply the actual original source iso. -/
def freeIso (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    freeModule r M ≅ reconstructedModule (nativeFree r M) :=
  (NativeOmegaPreparation.SymmetricNativeFree.comparison.{u, v} r).app M

/-- Every complete native free source arrow is transported by both actual original
free isomorphisms and the original inverse carrier functor. -/
def sourceArrow {r s : Operad.SmallFinBijGroupoid} {M M' : PointedCGWH.{u, v}}
    (f : nativeFree s M' ⟶ nativeFree r M) : freeModule s M' ⟶ freeModule r M :=
  ModuleFreeSourceTransport.sourceArrow PointedCGWH.sphereSequenceCommMon.{u, v}
    moduleOperatorEquivalence.{u, v}
    (freeIso r M) (freeIso s M') f

/-- The original entire module source arrow retains both actual free maps and
its original whole inverse-carrier image. -/
theorem sourceArrow_eq {r s : Operad.SmallFinBijGroupoid} {M M' : PointedCGWH.{u, v}}
    (f : nativeFree s M' ⟶ nativeFree r M) :
    sourceArrow f = (freeIso s M').hom ≫ operatorToModule.{u, v}.map f ≫ (freeIso r M).inv := rfl

set_option maxHeartbeats 500000 in
-- The complete native source comparison unfolds both original free-module isomorphisms.
/-- Every entire native free source arrow commutes with the actual original
function-functor source comparison, before any coefficient or sphere specialization. -/
theorem originalFreeComparison_precompose {r s : Operad.SmallFinBijGroupoid} {M M' : PointedCGWH.{u, v}}
    (f : nativeFree s M' ⟶ nativeFree r M) :
    (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison r M).hom ≫
        NativeOmegaPreparation.NativeSymmetricFunction.precompose f =
      NativeOmegaPreparation.SymmetricFunction.precompose (sourceArrow f) ≫
        (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison s M').hom := by
  exact ModuleFreeSourceTransport.sourceComparison_precompose A.{u, v}
    moduleOperatorEquivalence.{u, v} (freeIso r M) (freeIso s M') f

/-- The actual full original all-pair symmetric stabilization source is retained
through those same two complete free isomorphisms. -/
def moduleStabilization (r a : Operad.SmallFinBijGroupoid) :
    freeModule (r ⊗ a) (PointedCGWH.sphereSequence.{u, v}.functor.obj a) ⟶
      freeModule r (𝟙_ PointedCGWH.{u, v}) :=
  sourceArrow
    (HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.symmetricStabilization.{u, v}
      r a)

end NativeOmegaRecovery.NativeSymmetricFreeSource
