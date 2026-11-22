/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKMonoidal
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeKan
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Omega
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Unit
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import MathlibExt.CategoryTheory.Monoidal.Transport

/-!
# Native free-spectrum inputs to stable monoidality

The actual symmetric function spectrum from every free cofibrant pointed
coefficient preserves all original Ω labels. The full original free-function
comparison identifies it with the genuine enriched shift followed by scalar
cotensor; the shift retains its block permutation and the scalar result uses
the whole original K family.

These are ingredients for the ordinary stable smash pushout-product theorem.
No stable model or completed native monoidal-model theorem is asserted here.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CGWH.modelCategory CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Operator := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} Operator.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Every actual free cofibrant coefficient, in every degree and both
universe levels, preserves the complete original symmetric Ω family. -/
theorem symmetricFreeFunction_isOmega (r : Operad.SmallFinBijGroupoid)
    (M : PointedCGWH.{u, v}) [IsCofibrant M]
    (E : Actual.SymmetricCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    Actual.SymmetricIsOmega
      ((NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) M)).obj E) := by
  apply NativeOmegaRecovery.NativeOmegaIsoTransport.isOmega_obj_of_natIso Actual.symmetricFamily
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeFreeComparison r M) E
  exact NativeK.cotensor_isOmega Actual.symmetricFamily M
    ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj E)
    (NativeOmegaRecovery.NativeSymmetricShiftOmega.shift_isOmega E hE r)

/-- The actual balanced smash with every free cofibrant coefficient is
left Quillen for the original native level model. The proof uses its given
adjunction, the whole free-function comparison, and original right classes. -/
theorem symmetricFreeSmash_isQuillen (r : Operad.SmallFinBijGroupoid)
    (M : PointedCGWH.{u, v}) [IsCofibrant M] :
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v}
      (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) M)).IsQuillenAdjunction := by
  let _ : (ScalarLeibniz.adjunction
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) M).IsQuillenAdjunction :=
    ScalarCompatibility.scalar_isQuillen M
  refine Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations ?_ ?_
  · change (fibrations Actual.SymmetricCarrier.{u, v}) ≤
      (fibrations Actual.SymmetricCarrier.{u, v}).inverseImage
        (NativeOmegaPreparation.NativeSymmetricFunction.functor
          (Free.object (PointedCGWH.symmetricOperatorObj r) M))
    rw [← CategoryTheory.MorphismProperty.map_le_iff]
    rw [CategoryTheory.MorphismProperty.map_eq_of_iso _
      (NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeFreeComparison r M)]
    rw [CategoryTheory.MorphismProperty.map_le_iff]
    intro X Y p hp
    have hShift : PreservesFibrations (PointedCGWH.SymmetricShift.functor.{u, v} r) := by
      have hB : B = Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
      cases hB
      exact HomotopicalAlgebra.EnrichedProjective.Native.Kan.restriction_preservesFibrations
        (PointedCGWH.SymmetricShift.indexShift.{u, v} r)
    exact Adjunction.IsQuillenAdjunction.preservesFibrations
      (adj := ScalarLeibniz.adjunction M) _ (hShift p hp)
  · change (trivialFibrations Actual.SymmetricCarrier.{u, v}) ≤
      (trivialFibrations Actual.SymmetricCarrier.{u, v}).inverseImage
        (NativeOmegaPreparation.NativeSymmetricFunction.functor
          (Free.object (PointedCGWH.symmetricOperatorObj r) M))
    rw [← CategoryTheory.MorphismProperty.map_le_iff]
    rw [CategoryTheory.MorphismProperty.map_eq_of_iso _
      (NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeFreeComparison r M)]
    rw [CategoryTheory.MorphismProperty.map_le_iff]
    intro X Y p hp
    have hShift : PreservesTrivialFibrations (PointedCGWH.SymmetricShift.functor.{u, v} r) := by
      have hB : B = Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
      cases hB
      exact HomotopicalAlgebra.EnrichedProjective.Native.Kan.restriction_preservesTrivialFibrations
        (PointedCGWH.SymmetricShift.indexShift.{u, v} r)
    exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
      (adj := ScalarLeibniz.adjunction M) _ (hShift p hp)

/-- The actual free-spectrum smash preserves the original all-label Ω
tests for arbitrary cofibrant original endpoints. -/
theorem symmetricFreeSmashMap_omegaTests (r : Operad.SmallFinBijGroupoid)
    (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : Actual.SymmetricCarrier.{u, v}} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : NativeK.omegaTests Actual.symmetricFamily f) :
    NativeK.omegaTests Actual.symmetricFamily
      ((NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) M)).map f) := by
  let _ := symmetricFreeSmash_isQuillen r M
  exact NativeK.adjointMap_omegaTests_of_cofibrant Actual.symmetricFamily
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction
      (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) M))
    (symmetricFreeFunction_isOmega r M) f hf

/-- For an arbitrary original arrow, the same smash acts on its entire
original I replacement, retaining the original cardinal and caller bottom. -/
theorem symmetricFreeSmashQMap_omegaTests (r : Operad.SmallFinBijGroupoid)
    (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests Actual.symmetricFamily f) :
    NativeK.omegaTests Actual.symmetricFamily
      ((NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) M)).map
          ((Replacement.cofibrantReplacement (B := B)).map f)) := by
  let _ := symmetricFreeSmash_isQuillen r M
  exact NativeK.adjointQMap_omegaTests Actual.symmetricFamily
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction
      (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) M))
    (symmetricFreeFunction_isOmega r M) f hf

end PointedCGWH.Spectra.NativeStableMonoidal


/-!
## The actual native symmetric sphere smash

The complete original left sphere-module equivalence transports its actual
relative tensor, sphere unit, symmetry and coherence maps. The closed structure
uses the same original native balanced-smash/function adjunction; the displayed
whole functor equalities and comparison formulas preserve those constructions.
No monoidal model axiom or native stable model is used in this assembly.
-/

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

open PointedCGWH.SymmetricModulePresentation


private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Sequence := PointedCGWH.SymmetricSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed

private abbrev Modules := Mod Sequence.{u, v} S.{u, v}

private abbrev E := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

private instance moduleMonoidal : MonoidalCategory Modules.{u, v} :=
  Mod.instMonoidalCategory (C := Sequence.{u, v}) A.{u, v}
private instance moduleSymmetric : SymmetricCategory Modules.{u, v} :=
  Mod.instSymmetricCategory (C := Sequence.{u, v}) A.{u, v}
private instance moduleClosed : MonoidalClosed Modules.{u, v} :=
  Mod.instMonoidalClosed (C := Sequence.{u, v}) A.{u, v}

/-- The complete original sphere-module tensor provider for the native transport. -/
public local instance originalModuleMonoidal : MonoidalCategory
    (Mod PointedCGWH.SymmetricSequence.{u, v} PointedCGWH.sphereSequence.{u, v}) :=
  Mod.instMonoidalCategory (C := PointedCGWH.SymmetricSequence.{u, v})
    PointedCGWH.sphereSequenceCommMon.{u, v}

/-- The complete original sphere-module symmetry on that same original tensor. -/
public local instance originalModuleSymmetric : SymmetricCategory
    (Mod PointedCGWH.SymmetricSequence.{u, v} PointedCGWH.sphereSequence.{u, v}) :=
  Mod.instSymmetricCategory (C := PointedCGWH.SymmetricSequence.{u, v})
    PointedCGWH.sphereSequenceCommMon.{u, v}

/-- The complete original sphere-module closed provider on that same tensor. -/
public local instance originalModuleClosed : MonoidalClosed
    (Mod PointedCGWH.SymmetricSequence.{u, v} PointedCGWH.sphereSequence.{u, v}) :=
  Mod.instMonoidalClosed (C := PointedCGWH.SymmetricSequence.{u, v})
    PointedCGWH.sphereSequenceCommMon.{u, v}

/-- The monoidal structure on native symmetric spectra transported from sphere modules
along `moduleOperatorEquivalence`, with their original relative tensor and sphere unit. -/
@[instance_reducible]
def monoidalCategory : MonoidalCategory Actual.SymmetricCarrier.{u, v} :=
  letI : MonoidalCategory
      (Mod PointedCGWH.SymmetricSequence.{u, v} PointedCGWH.sphereSequence.{u, v}) :=
    Mod.instMonoidalCategory (C := PointedCGWH.SymmetricSequence.{u, v})
      PointedCGWH.sphereSequenceCommMon.{u, v}
  Monoidal.transport moduleOperatorEquivalence.{u, v}

attribute [local instance] monoidalCategory

/-- The symmetry on native symmetric spectra transported from modules over the
commutative sphere sequence along `moduleOperatorEquivalence`. -/
@[instance_reducible]
def symmetricCategory : SymmetricCategory Actual.SymmetricCarrier.{u, v} :=
  inferInstanceAs (SymmetricCategory (Monoidal.Transported moduleOperatorEquivalence.{u, v}))

attribute [local instance] symmetricCategory

theorem tensorObj_eq_originalSmash (X Y : Actual.SymmetricCarrier.{u, v}) :
    X ⊗ Y = (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor X).obj Y := rfl

theorem tensorLeft_eq_originalSmash (X : Actual.SymmetricCarrier.{u, v}) :
    tensorLeft X = NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor X := rfl

theorem tensorUnit_eq_originalSphereModule :
    (𝟙_ Actual.SymmetricCarrier.{u, v}) = moduleOperatorEquivalence.{u, v}.functor.obj
      (Mod.relativeTensorUnit PointedCGWH.sphereSequenceCommMon.{u, v}) := rfl

/-- The original native balanced-smash/function-spectrum adjunction, identifying
its left functor with the transported `tensorLeft X` by `tensorLeft_eq_originalSmash`. -/
def actualClosedAdjunction (X : Actual.SymmetricCarrier.{u, v}) :
    tensorLeft X ⊣ NativeOmegaPreparation.NativeSymmetricFunction.functor X :=
  (NativeOmegaPreparation.NativeSymmetricFunction.adjunction X).ofNatIsoLeft
    (eqToIso (tensorLeft_eq_originalSmash X)).symm

/-- The closed structure on the transported native sphere smash, using the original
native symmetric function spectrum and `actualClosedAdjunction` as its right adjoint data. -/
@[instance_reducible]
def monoidalClosed : MonoidalClosed Actual.SymmetricCarrier.{u, v} where
  closed X :=
    { rightAdj := NativeOmegaPreparation.NativeSymmetricFunction.functor X
      adj := actualClosedAdjunction X }

attribute [local instance] monoidalClosed

theorem internalHom_eq_originalFunction (X : Actual.SymmetricCarrier.{u, v}) :
    ihom X = NativeOmegaPreparation.NativeSymmetricFunction.functor X := rfl


theorem whiskerLeft_eq_original (X : Actual.SymmetricCarrier.{u, v})
    {Y Z : Actual.SymmetricCarrier.{u, v}} (f : Y ⟶ Z) :
    X ◁ f = moduleOperatorEquivalence.{u, v}.functor.map
      (moduleOperatorEquivalence.inverse.obj X ◁ moduleOperatorEquivalence.inverse.map f) := rfl

theorem whiskerRight_eq_original {X Y : Actual.SymmetricCarrier.{u, v}}
    (f : X ⟶ Y) (Z : Actual.SymmetricCarrier.{u, v}) :
    f ▷ Z = moduleOperatorEquivalence.{u, v}.functor.map
      (moduleOperatorEquivalence.inverse.map f ▷ moduleOperatorEquivalence.inverse.obj Z) := rfl

theorem tensorHom_eq_original {X Y Z W : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y) (g : Z ⟶ W) :
    f ⊗ₘ g = moduleOperatorEquivalence.{u, v}.functor.map
      (moduleOperatorEquivalence.inverse.map f ⊗ₘ moduleOperatorEquivalence.inverse.map g) := rfl

theorem braiding_eq_original (X Y : Actual.SymmetricCarrier.{u, v}) :
    (β_ X Y) = moduleOperatorEquivalence.{u, v}.functor.mapIso
      (β_ (moduleOperatorEquivalence.inverse.obj X)
        (moduleOperatorEquivalence.inverse.obj Y)) := rfl

theorem associator_eq_original (X Y Z : Actual.SymmetricCarrier.{u, v}) :
    CategoryTheory.Monoidal.Transport.SourceCoherence.AssociatorFormula
      moduleOperatorEquivalence.{u, v} X Y Z := rfl

theorem leftUnitor_eq_original (X : Actual.SymmetricCarrier.{u, v}) :
    (λ_ X) = moduleOperatorEquivalence.{u, v}.functor.mapIso
      (whiskerRightIso (moduleOperatorEquivalence.unitIso.app _).symm _ ≪≫
        (λ_ (moduleOperatorEquivalence.inverse.obj X))) ≪≫
        moduleOperatorEquivalence.counitIso.app _ := rfl

theorem rightUnitor_eq_original (X : Actual.SymmetricCarrier.{u, v}) :
    (ρ_ X) = moduleOperatorEquivalence.{u, v}.functor.mapIso
      (whiskerLeftIso _ (moduleOperatorEquivalence.unitIso.app _).symm ≪≫
        (ρ_ (moduleOperatorEquivalence.inverse.obj X))) ≪≫
        moduleOperatorEquivalence.counitIso.app _ := rfl

theorem closed_actualAdjunction (X : Actual.SymmetricCarrier.{u, v}) :
    (ihom.adjunction X) = actualClosedAdjunction X := rfl

theorem closed_unit_compared (X : Actual.SymmetricCarrier.{u, v}) :
    (ihom.adjunction X).unit = (actualClosedAdjunction X).unit := rfl

theorem closed_counit_compared (X : Actual.SymmetricCarrier.{u, v}) :
    (ihom.adjunction X).counit = (actualClosedAdjunction X).counit := rfl

private abbrev FreeZero :=
  Free.object (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I)) (𝟙_ V.{u, v})

/-- Smashing with the native free spectrum on the pointed tensor unit in degree zero
is naturally isomorphic to the identity, by left-adjoint uniqueness applied to the
original free-function unit comparison. -/
def freeZeroSmashUnitIso :
    NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor
      (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v})) ≅
      𝟭 Actual.SymmetricCarrier.{u, v} :=
  Adjunction.leftAdjointUniq
    ((NativeOmegaPreparation.NativeSymmetricFunction.adjunction
      (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v}))).ofNatIsoRight
      NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeUnitComparison.{u, v})
    (Adjunction.id (C := Actual.SymmetricCarrier.{u, v}))

/-- The native free spectrum on the pointed tensor unit in degree zero is isomorphic
to the transported sphere-module tensor unit, using `freeZeroSmashUnitIso` at that unit. -/
def freeZeroIsoSphereUnit : (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v})) ≅
      (𝟙_ Actual.SymmetricCarrier.{u, v}) :=
  (ρ_ (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v}))).symm ≪≫
    eqToIso (tensorObj_eq_originalSmash (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v}))
      (𝟙_ Actual.SymmetricCarrier.{u, v})) ≪≫
    freeZeroSmashUnitIso.{u, v}.app (𝟙_ Actual.SymmetricCarrier.{u, v})

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

theorem tensorUnit_isCofibrant :
    HomotopicalAlgebra.IsCofibrant (𝟙_ Actual.SymmetricCarrier.{u, v}) := by
  let _ : HomotopicalAlgebra.IsCofibrant (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v})) :=
    HomotopicalAlgebra.EnrichedProjective.Native.freeAt_unit_isCofibrant
      (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I))
  exact HomotopicalAlgebra.isCofibrant_of_cofibration freeZeroIsoSphereUnit.{u, v}.hom


end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash
