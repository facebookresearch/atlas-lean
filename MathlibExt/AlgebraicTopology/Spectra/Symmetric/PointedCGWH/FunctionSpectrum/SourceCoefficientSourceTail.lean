/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceFactors
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSourceCoefficientData

/-!
# The complete original source tail of the native free-function comparison

The actual sphere coefficient data carry the original module comparison and
carrier counit as entire natural isomorphisms. The full source equality is
applied before any component is selected.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.SourceEquality

universe uC vC
variable {C : Type uC} [Category.{vC} C] {S G G' R : C}

/-- Heterogeneously equal tail isomorphisms transport the factorization of a
comparison across the two given source equalities. -/
theorem comparison_from_two_source_equalities (c : S ≅ R) (h : S = G) (k : G ≅ R)
    (hc : c = eqToIso h ≪≫ k) (k' : G' ≅ R) (h' : S = G') (hk : HEq k k') :
    c = eqToIso h' ≪≫ k' :=
  hc.trans (eqToIso_comp_eq_of_heq h h' k k' hk)

end NativeOmegaRecovery.SourceEquality


namespace NativeOmegaRecovery.SourceEquality

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Whisker the full comparison through the inverse carrier, then apply
the carrier counit and the target functor's left unitor. -/
def normalizedTail (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
    (k : F ⋙ E.functor ≅ E.functor ⋙ R) : E.inverse ⋙ F ⋙ E.functor ≅ R :=
  Functor.isoWhiskerLeft E.inverse k ≪≫ Functor.isoWhiskerRight E.counitIso R ≪≫
    Functor.leftUnitor R

/-- The normalized carrier tail equals its composite without the final
target-functor left unitor. -/
theorem normalizedTail_eq (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
    (k : F ⋙ E.functor ≅ E.functor ⋙ R) :
    normalizedTail E k =
      Functor.isoWhiskerLeft E.inverse k ≪≫ Functor.isoWhiskerRight E.counitIso R := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  dsimp only [normalizedTail, Iso.trans_hom, NatTrans.comp_app,
    Functor.leftUnitor_hom_app]
  change k.hom.app (E.inverse.obj X) ≫ R.map (E.counitIso.hom.app X) ≫
      𝟙 (R.obj X) = k.hom.app (E.inverse.obj X) ≫ R.map (E.counitIso.hom.app X)
  exact congrArg (fun z => k.hom.app (E.inverse.obj X) ≫ z)
    (Category.comp_id (R.map (E.counitIso.hom.app X)))

/-- The unitor-free carrier-tail composite is heterogeneously equal to the normalized tail. -/
theorem normalizedTail_heq (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
    (k : F ⋙ E.functor ≅ E.functor ⋙ R) :
    HEq (Functor.isoWhiskerLeft E.inverse k ≪≫ Functor.isoWhiskerRight E.counitIso R)
      (normalizedTail E k) :=
  heq_of_eq (normalizedTail_eq E k).symm

end NativeOmegaRecovery.SourceEquality

namespace NativeOmegaRecovery.SourceEquality
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The actual module Iso supplies the entire original normalized carrier tail. -/
def moduleTail (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) : E.inverse ⋙ F ⋙ E.functor ≅ R :=
  normalizedTail E (FreeFunctionCarrierComparison.collapse E e)

/-- A whole equality of the original module comparison is eliminated before
its full original carrier tail is read. -/
theorem moduleTail_heq_given_tail (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse)
    (k : F ⋙ E.functor ≅ E.functor ⋙ R)
    (hk : k = FreeFunctionCarrierComparison.collapse E e) :
    HEq (Functor.isoWhiskerLeft E.inverse k ≪≫ Functor.isoWhiskerRight E.counitIso R)
      (moduleTail E e) := by
  cases hk
  exact normalizedTail_heq E (FreeFunctionCarrierComparison.collapse E e)

end NativeOmegaRecovery.SourceEquality

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

universe u v
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Carrier :=
  EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric

open PointedCGWH.SymmetricModulePresentation
open OriginalCarrierZeroSourceUnit
open NativeSymmetricSourceMatch

attribute [local irreducible] Mod.internalHom moduleComparisonNat moduleOperatorComparison

/-- The complete original tail is the module comparison followed by
the carrier recovery comparison. -/
def originalComparisonTail (r : I) (M : V.{u, v}) :=
  comparisonModuleFactor r M ≪≫ comparisonRecoveryFactor r M

/-- The whole source equality is transported through the complete actual coefficient data. -/
theorem nativeSource_eq_actualCoefficientSource (r : I) (M : V.{u, v}) :
    NativeOmegaPreparation.SymmetricFunction.functor.{u, v} r M =
      NativeScalarCoefficient.coefficientOperatorEquivalence.{u, v}.inverse ⋙
        NativeScalarCoefficient.originalComparisonSourceFunctor r M ⋙
          NativeScalarCoefficient.coefficientOperatorEquivalence.{u, v}.functor := by
  rw [NativeScalarCoefficient.coefficientOperatorEquivalence_eq_original]
  exact nativeSource_eq_actualComparisonSource r M

/-- The actual whole equality isomorphism preserves both complete original carrier functors. -/
def actualCoefficientSourceTransport (r : I) (M : V.{u, v}) :=
  eqToIso (nativeSource_eq_actualCoefficientSource r M)

/-- Transport the complete module comparison through the actual sphere
coefficient equivalence to the native shift and cotensor functor. -/
def actualComparisonTail (r : I) (M : V.{u, v}) :=
  SourceEquality.moduleTail
    (C := OriginalModule.{u, v}) (D := NativeCarrier.{u, v})
    (R := PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M)
    NativeScalarCoefficient.coefficientOperatorEquivalence.{u, v} (moduleComparisonNat r M)

/-- The original carrier tail is heterogeneously equal to the tail from the
actual sphere-coefficient module equivalence. -/
theorem originalTail_heq_actual (r : I) (M : V.{u, v}) :
    HEq (originalComparisonTail r M) (actualComparisonTail r M) := by
  unfold originalComparisonTail actualComparisonTail
  unfold comparisonModuleFactor comparisonRecoveryFactor
  apply SourceEquality.moduleTail_heq_given_tail
    (C := OriginalModule.{u, v}) (D := NativeCarrier.{u, v})
    (R := PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M)
    NativeScalarCoefficient.coefficientOperatorEquivalence.{u, v} (moduleComparisonNat r M)
  exact NativeScalarCoefficient.moduleOperatorComparison_coefficient_collapse r M

/-- The complete native free-function comparison factors through its original
source equality and original carrier tail. -/
theorem comparison_eq_originalSourceTail (r : I) (M : V.{u, v}) :
    comparison r M = eqToIso (comparison_source r M) ≪≫ originalComparisonTail r M :=
  comparison_factorization r M

/-- The same comparison factors through the actual coefficient-source
transport and complete module-comparison tail. -/
theorem comparison_eq_actualSourceTail (r : I) (M : V.{u, v}) :
    comparison r M = actualCoefficientSourceTransport r M ≪≫ actualComparisonTail r M :=
  SourceEquality.comparison_from_two_source_equalities (comparison r M)
    (comparison_source r M) (originalComparisonTail r M) (comparison_eq_originalSourceTail r M)
    (actualComparisonTail r M) (nativeSource_eq_actualCoefficientSource r M)
    (originalTail_heq_actual r M)


end NativeOmegaRecovery.NativeSymmetricFreeFunction
