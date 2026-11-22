/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceTail
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Unit

/-!
# The original complete native zero source and chosen unit

The original module comparison, both carrier functors and actual source equality
supply the same chosen unit. Its full native comparison and inverse source prefix
are identified before any module image or output coordinate is selected.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- A comparison factored through the original carrier counit gives the chosen
source unit after composing with the supplied target unit. -/
theorem sourceUnitFromModule_of_comparison (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
    (k : F ⋙ E.functor ≅ E.functor ⋙ R)
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)
    (hk : k = FreeFunctionCarrierComparison.collapse E e)
    {S : D ⥤ D} (s : S ≅ E.inverse ⋙ F ⋙ E.functor) (w : S ≅ R)
    (hc : w = s ≪≫ Functor.isoWhiskerLeft E.inverse k ≪≫
      Functor.isoWhiskerRight E.counitIso R) :
    w ≪≫ u = sourceUnitFromModule E e u s := by
  unfold sourceUnitFromModule
  apply source_unit_of_factorization E s e u w
  simpa only [hk] using hc

/-- On each carrier image, the inverse of the chosen source unit is the full
module inverse word with both carrier units and the source transport inverse. -/
theorem sourceUnitFromModule_inv_on_image_of_value (E : C ≌ D)
    {F : C ⥤ C} {R : D ⥤ D} (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)
    {S : D ⥤ D} (s : S ≅ E.inverse ⋙ F ⋙ E.functor) (w : S ≅ 𝟭 D)
    (hw : w = sourceUnitFromModule E e u s) (N : C) :
    w.inv.app (E.functor.obj N) =
      E.functor.map
        (E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N)) ≫
          e.inv.app N ≫ F.map (E.unitIso.hom.app N)) ≫
        s.inv.app (E.functor.obj N) :=
  source_unit_inv_on_image_of_value E s e u w hw N

end NativeOmegaRecovery.OriginalCarrierZeroSourceUnit


namespace NativeOmegaRecovery.OriginalCarrierZeroSourceUnit
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The original complete module tail carries the same complete chosen unit. -/
theorem sourceUnitFromModule_of_module_tail (E : C ≌ D)
    {F : C ⥤ C} {R : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)
    {S : D ⥤ D} (s : S ≅ E.inverse ⋙ F ⋙ E.functor) (w : S ≅ R)
    (hc : w = s ≪≫ SourceEquality.moduleTail E e) :
    w ≪≫ u = sourceUnitFromModule E e u s := by
  apply sourceUnitFromModule_of_comparison E (FreeFunctionCarrierComparison.collapse E e)
    e u rfl s w
  exact hc.trans (congrArg (fun q => s ≪≫ q)
    (SourceEquality.normalizedTail_eq E (FreeFunctionCarrierComparison.collapse E e)))

end NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

namespace NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

private theorem fiveIso_unit_recipe {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₃ ≅ X₄) (e : X₄ ≅ X₅) (w : X₁ ≅ X₅)
    (h : b ≪≫ (c ≪≫ d ≪≫ e) = w) :
    ((a ≪≫ b) ≪≫ c ≪≫ d) ≪≫ e = a ≪≫ w := by
  rw [Iso.trans_assoc, Iso.trans_assoc, Iso.trans_assoc, h]

/-- The same whole chosen source unit cancels the original full source prefix. -/
theorem source_inv_prefix_cancel {C : Type*} [Category C] {S H R : C}
    (e : S ≅ H) (u : S ≅ R) (w : H ≅ R) (hw : w = e.symm ≪≫ u) :
    w.inv ≫ e.inv = u.inv := by
  rw [hw]
  change (u.inv ≫ e.hom) ≫ e.inv = u.inv
  rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Every genuine following source arrow retains this same whole prefix cancellation. -/
theorem source_inv_prefix_cancel_suffix {C : Type*} [Category C] {S H R T : C}
    (e : S ≅ H) (u : S ≅ R) (w : H ≅ R) (hw : w = e.symm ≪≫ u) (f : S ⟶ T) :
    w.inv ≫ e.inv ≫ f = u.inv ≫ f := by
  rw [← Category.assoc, source_inv_prefix_cancel e u w hw]

end NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

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

/-- Every full chosen source unit retains the actual entire module source and carrier tail. -/
theorem comparison_unit_from_source (r : I) (M : V.{u, v})
    (uR : PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M ≅ 𝟭 Carrier.{u, v}) :
    comparison r M ≪≫ uR = comparisonSourceUnit r M uR :=
by
  unfold comparisonSourceUnit
  apply sourceUnitFromModule_of_module_tail
  exact comparison_eq_actualSourceTail r M

/-- The zero scalar and index unit use both original complete chosen comparisons. -/
def zeroScalarIndexUnit :
    PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I) ⋙ cotensor (𝟙_ V.{u, v}) ≅
      𝟭 Carrier.{u, v} :=
  Functor.isoWhiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I))
      OriginalCotensorUnit.comparison ≪≫
    Functor.rightUnitor (PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I)) ≪≫
      NativeSymmetricShiftUnit.comparison

/-- The actual native zero source retains its original free comparison before
 the full source unit. -/
def nativeZeroSourceUnit :=
  (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v}
      (𝟙_ I) (𝟙_ V.{u, v})).symm ≪≫
    comparisonSourceUnit.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) zeroScalarIndexUnit.{u, v}

/-- The entire original native unit comparison is this same actual source-unit recipe. -/
theorem nativeUnitComparison_eq_wholeSourceUnit :
    nativeUnitComparison.{u, v} = nativeZeroSourceUnit.{u, v} := by
  exact fiveIso_unit_recipe
    (C := NativeCarrier.{u, v} ⥤ NativeCarrier.{u, v})
    (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v}
      (𝟙_ I) (𝟙_ V.{u, v})).symm
    (comparison.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
    (Functor.isoWhiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I))
      OriginalCotensorUnit.comparison)
    (Functor.rightUnitor (PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I)))
    NativeSymmetricShiftUnit.comparison
    (comparisonSourceUnit.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) zeroScalarIndexUnit.{u, v})
    (comparison_unit_from_source.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) zeroScalarIndexUnit.{u, v})

/-- The entire actual native zero inverse cancels its unchanged original free-source inverse
before any input or enriched output component is selected. -/
theorem nativeUnitComparison_inverse_source_prefix :
    nativeUnitComparison.{u, v}.inv ≫
        (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v}
          (𝟙_ I) (𝟙_ V.{u, v})).inv =
      (comparisonSourceUnit.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) zeroScalarIndexUnit.{u, v}).inv :=
  source_inv_prefix_cancel (C := NativeCarrier.{u, v} ⥤ NativeCarrier.{u, v})
    (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v}
      (𝟙_ I) (𝟙_ V.{u, v}))
    (comparisonSourceUnit.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) zeroScalarIndexUnit.{u, v})
    nativeUnitComparison.{u, v} nativeUnitComparison_eq_wholeSourceUnit.{u, v}

end NativeOmegaRecovery.NativeSymmetricFreeFunction

namespace NativeOmegaRecovery.OriginalCarrierZeroSourceUnit
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The same whole native chosen unit carries the complete original module image inverse word. -/
theorem source_unit_prefixed_inv_on_image (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)
    {S H : D ⥤ D} (s : S ≅ E.inverse ⋙ F ⋙ E.functor)
    (a : S ≅ H) (w : H ≅ 𝟭 D)
    (hw : w = a.symm ≪≫ sourceUnitFromModule E e u s) (N : C) :
    w.inv.app (E.functor.obj N) =
      E.functor.map
        (E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N)) ≫
          e.inv.app N ≫ F.map (E.unitIso.hom.app N)) ≫
        s.inv.app (E.functor.obj N) ≫ a.hom.app (E.functor.obj N) := by
  rw [hw]
  change (sourceUnitFromModule E e u s).inv.app (E.functor.obj N) ≫
    a.hom.app (E.functor.obj N) = _
  rw [sourceUnitFromModule_inv_on_image_of_value E e u s
    (sourceUnitFromModule E e u s) rfl N]
  exact Category.assoc _ _ _

end NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

universe u v

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

open PointedCGWH.SymmetricModulePresentation
open OriginalCarrierZeroSourceUnit
open NativeSymmetricSourceMatch


attribute [local irreducible] Mod.internalHom moduleComparisonNat moduleOperatorComparison

/-- On every original module image, the full inverse keeps both carrier units,
the original module-comparison inverse and the actual complete source inverse. -/
theorem comparisonSourceUnit_inv_on_image (r : I) (M : V.{u, v})
    (uR : PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M ≅ 𝟭 Carrier.{u, v})
    (N : OriginalModule.{u, v}) :
    type_of% (sourceUnitFromModule_inv_on_image_of_value
      (R := PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M)
      moduleOperatorEquivalence.{u, v} (moduleComparisonNat r M) uR (actualSourceTransport r M)
      (comparisonSourceUnit r M uR) rfl N) :=
  sourceUnitFromModule_inv_on_image_of_value
      (R := PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M)
      moduleOperatorEquivalence.{u, v} (moduleComparisonNat r M) uR (actualSourceTransport r M)
      (comparisonSourceUnit r M uR) rfl N

/-- Every actual original module image retains both carrier units, the original complete
module-comparison inverse, the actual source inverse and original native free map. -/
theorem nativeUnitComparison_inv_on_original_image (N : OriginalModule.{u, v}) :
    type_of% (source_unit_prefixed_inv_on_image
      (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I) ⋙ cotensor (𝟙_ V.{u, v}))
      moduleOperatorEquivalence.{u, v} (moduleComparisonNat (𝟙_ I) (𝟙_ V.{u, v}))
      zeroScalarIndexUnit.{u, v} (actualSourceTransport (𝟙_ I) (𝟙_ V.{u, v}))
      (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v}
        (𝟙_ I) (𝟙_ V.{u, v})) nativeUnitComparison.{u, v}
      nativeUnitComparison_eq_wholeSourceUnit.{u, v} N) :=
  source_unit_prefixed_inv_on_image
      (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I) ⋙ cotensor (𝟙_ V.{u, v}))
      moduleOperatorEquivalence.{u, v} (moduleComparisonNat (𝟙_ I) (𝟙_ V.{u, v}))
      zeroScalarIndexUnit.{u, v} (actualSourceTransport (𝟙_ I) (𝟙_ V.{u, v}))
      (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v}
        (𝟙_ I) (𝟙_ V.{u, v})) nativeUnitComparison.{u, v}
      nativeUnitComparison_eq_wholeSourceUnit.{u, v} N

end NativeOmegaRecovery.NativeSymmetricFreeFunction
