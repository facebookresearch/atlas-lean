/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalLocalizedFactors
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalDefaults

/-!
# Entire original Q/R maps on the computed orthogonal localization

The original native I cofibrant replacement and paired K Omega replacement
are moved through the actual identity equivalence. Both whole functors and
every source map retain the original algorithms. The initial leg, Q counit,
R unit and terminal leg retain their original entire native components.

All four model class memberships follow from the same original I/K factor
records. The actual tagged zero supplies initial and terminal objects, so
the replacements are cofibrant and fibrant in this computed localization.
The exact original comparison proposition remains an explicit argument.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalLocalizedReplacements

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

variable (hComparison : ComparisonHomBijections.{u, v} (B := B))

/-- The same original full native zero object acquires the proved localization tag. -/
def zero : ConditionalLocalization.Carrier hComparison :=
  (ConditionalLocalizedCarrier.ofNative hComparison).obj
    (Diagrams.zeroDiagram (A := O.{u, v}))

private instance ofNative_isEquivalence :
    (ConditionalLocalizedCarrier.ofNative hComparison).IsEquivalence := by
  change (ConditionalLocalizedCarrier.equivalence hComparison).functor.IsEquivalence
  infer_instance

/-- The actual original tagged zero remains initial through the complete equivalence. -/
def zeroIsInitial : IsInitial (zero hComparison) :=
  (Diagrams.zeroDiagramIsInitial (A := O.{u, v})).isInitialObj
    (ConditionalLocalizedCarrier.ofNative hComparison) _

/-- The same actual original tagged zero remains terminal through that equivalence. -/
def zeroIsTerminal : IsTerminal (zero hComparison) :=
  (Diagrams.zeroDiagramIsTerminal (A := O.{u, v})).isTerminalObj
    (ConditionalLocalizedCarrier.ofNative hComparison) _

/-- The whole original I replacement functor is retained between the two identity functions. -/
def QFunctor : ConditionalLocalization.Carrier hComparison ⥤
    ConditionalLocalization.Carrier hComparison :=
  (ConditionalLocalizedCarrier.toNative hComparison ⋙
    ConditionalDefaults.QOfComparison hComparison) ⋙
      ConditionalLocalizedCarrier.ofNative hComparison

/-- The whole original paired K replacement retains every native source arrow. -/
def RFunctor : ConditionalLocalization.Carrier hComparison ⥤
    ConditionalLocalization.Carrier hComparison :=
  (ConditionalLocalizedCarrier.toNative hComparison ⋙
    ConditionalDefaults.ROfComparison hComparison) ⋙
      ConditionalLocalizedCarrier.ofNative hComparison

/-- The original Q counit is followed by the actual identity comparison of its target. -/
def qCounit : QFunctor hComparison ⟶ 𝟭 (ConditionalLocalization.Carrier hComparison) :=
  Functor.whiskerRight
    (Functor.whiskerLeft (ConditionalLocalizedCarrier.toNative hComparison)
      (ConditionalDefaults.QCounitOfComparison hComparison))
    (ConditionalLocalizedCarrier.ofNative hComparison) ≫
      (ConditionalLocalizedCarrier.equivalence hComparison).counitIso.hom

/-- The entire original zero-source I injection is the initial replacement leg. -/
def initialToQ :
    (Functor.const (ConditionalLocalization.Carrier hComparison)).obj (zero hComparison) ⟶
      QFunctor hComparison :=
  Functor.whiskerRight
    (Functor.whiskerLeft (ConditionalLocalizedCarrier.toNative hComparison)
      (ConditionalDefaults.initialToQOfComparison hComparison))
    (ConditionalLocalizedCarrier.ofNative hComparison)

/-- The actual inverse identity comparison is followed by the original entire K unit. -/
def rUnit : 𝟭 (ConditionalLocalization.Carrier hComparison) ⟶ RFunctor hComparison :=
  (ConditionalLocalizedCarrier.equivalence hComparison).counitIso.inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (ConditionalLocalizedCarrier.toNative hComparison)
        (ConditionalDefaults.RUnitOfComparison hComparison))
      (ConditionalLocalizedCarrier.ofNative hComparison)

/-- The entire original K projection to the native zero is the terminal replacement leg. -/
def rToZero : RFunctor hComparison ⟶
    (Functor.const (ConditionalLocalization.Carrier hComparison)).obj (zero hComparison) :=
  Functor.whiskerRight
    (Functor.whiskerLeft (ConditionalLocalizedCarrier.toNative hComparison)
      (ConditionalDefaults.RToZeroOfComparison hComparison))
    (ConditionalLocalizedCarrier.ofNative hComparison)

/-- Every original zero-source Arrow is moved by the same full native identity functions. -/
def fromZeroArrow : ConditionalLocalization.Carrier hComparison ⥤
    CategoryTheory.Arrow (ConditionalLocalization.Carrier hComparison) :=
  (ConditionalLocalizedCarrier.toNative hComparison ⋙
    Diagrams.fromZeroArrow (A := O.{u, v})) ⋙
      (ConditionalLocalizedCarrier.ofNative hComparison).mapArrow

/-- Every original zero-target Arrow retains all its native object and source map data. -/
def toZeroArrow : ConditionalLocalization.Carrier hComparison ⥤
    CategoryTheory.Arrow (ConditionalLocalization.Carrier hComparison) :=
  (ConditionalLocalizedCarrier.toNative hComparison ⋙
    Diagrams.toZeroArrow (A := O.{u, v})) ⋙
      (ConditionalLocalizedCarrier.ofNative hComparison).mapArrow

/-- Both replacements and all four legs come from those same given original I/K records. -/
theorem replacement_original_factors (X : ConditionalLocalization.Carrier hComparison) :
    (QFunctor hComparison).obj X =
        (ConditionalLocalizedFactors.IFactorizationData hComparison).Z.obj
          ((fromZeroArrow hComparison).obj X) ∧
      (initialToQ hComparison).app X =
        (ConditionalLocalizedFactors.IFactorizationData hComparison).i.app
          ((fromZeroArrow hComparison).obj X) ∧
      (qCounit hComparison).app X =
        (ConditionalLocalizedFactors.IFactorizationData hComparison).p.app
          ((fromZeroArrow hComparison).obj X) ∧
      (RFunctor hComparison).obj X =
        (ConditionalLocalizedFactors.KFactorizationData hComparison).Z.obj
          ((toZeroArrow hComparison).obj X) ∧
      (rUnit hComparison).app X =
        (ConditionalLocalizedFactors.KFactorizationData hComparison).i.app
          ((toZeroArrow hComparison).obj X) ∧
      (rToZero hComparison).app X =
        (ConditionalLocalizedFactors.KFactorizationData hComparison).p.app
          ((toZeroArrow hComparison).obj X) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, ?_⟩
  · apply InducedCategory.hom_ext
    change _ = 𝟙 _ ≫ _
    exact (Category.id_comp _).symm
  · apply InducedCategory.hom_ext
    change _ = _ ≫ 𝟙 _
    exact (Category.comp_id _).symm

/-- Both full replacement functors are the actual original I/K functions on native diagrams. -/
theorem original_functors :
    QFunctor hComparison =
        (ConditionalLocalizedCarrier.toNative hComparison ⋙
          Replacement.cofibrantReplacement (B := B) (A := O.{u, v})) ⋙
            ConditionalLocalizedCarrier.ofNative hComparison ∧
      RFunctor hComparison =
        (ConditionalLocalizedCarrier.toNative hComparison ⋙
          NativeK.omegaReplacement orthogonalFamily) ⋙
            ConditionalLocalizedCarrier.ofNative hComparison := by
  constructor
  · exact congrArg (fun F : C.{u, v} ⥤ C.{u, v} =>
      (ConditionalLocalizedCarrier.toNative hComparison ⋙ F) ⋙
        ConditionalLocalizedCarrier.ofNative hComparison)
      (ConditionalDefaults.original_replacement_defaults hComparison).1
  · exact congrArg (fun F : C.{u, v} ⥤ C.{u, v} =>
      (ConditionalLocalizedCarrier.toNative hComparison ⋙ F) ⋙
        ConditionalLocalizedCarrier.ofNative hComparison)
      (ConditionalDefaults.original_replacement_defaults hComparison).2.2.2.1

/-- Every entire Q source map retains its original complete native replacement map. -/
theorem Q_map {X Y : ConditionalLocalization.Carrier hComparison} (f : X ⟶ Y) :
    (ConditionalLocalizedCarrier.toNative hComparison).map ((QFunctor hComparison).map f) =
      (ConditionalDefaults.QOfComparison hComparison).map
        ((ConditionalLocalizedCarrier.toNative hComparison).map f) := rfl

/-- Every entire R source map retains its original complete paired K replacement map. -/
theorem R_map {X Y : ConditionalLocalization.Carrier hComparison} (f : X ⟶ Y) :
    (ConditionalLocalizedCarrier.toNative hComparison).map ((RFunctor hComparison).map f) =
      (ConditionalDefaults.ROfComparison hComparison).map
        ((ConditionalLocalizedCarrier.toNative hComparison).map f) := rfl

/-- Every initial leg is the same entire original I injection on the native source. -/
theorem initialToQ_component (X : ConditionalLocalization.Carrier hComparison) :
    (ConditionalLocalizedCarrier.toNative hComparison).map ((initialToQ hComparison).app X) =
      (ConditionalDefaults.initialToQOfComparison hComparison).app
        ((ConditionalLocalizedCarrier.toNative hComparison).obj X) := rfl

/-- Every Q projection is the same complete original native counit. -/
theorem qCounit_component (X : ConditionalLocalization.Carrier hComparison) :
    (ConditionalLocalizedCarrier.toNative hComparison).map ((qCounit hComparison).app X) =
      (ConditionalDefaults.QCounitOfComparison hComparison).app
        ((ConditionalLocalizedCarrier.toNative hComparison).obj X) := by
  change (ConditionalDefaults.QCounitOfComparison hComparison).app _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Every R unit is the same entire original paired K injection. -/
theorem rUnit_component (X : ConditionalLocalization.Carrier hComparison) :
    (ConditionalLocalizedCarrier.toNative hComparison).map ((rUnit hComparison).app X) =
      (ConditionalDefaults.RUnitOfComparison hComparison).app
        ((ConditionalLocalizedCarrier.toNative hComparison).obj X) := by
  change 𝟙 _ ≫ (ConditionalDefaults.RUnitOfComparison hComparison).app _ = _
  exact Category.id_comp _

/-- Every terminal leg retains the complete original paired K zero-target projection. -/
theorem rToZero_component (X : ConditionalLocalization.Carrier hComparison) :
    (ConditionalLocalizedCarrier.toNative hComparison).map ((rToZero hComparison).app X) =
      (ConditionalDefaults.RToZeroOfComparison hComparison).app
        ((ConditionalLocalizedCarrier.toNative hComparison).obj X) := rfl

/-- The original I injection is a cofibration on the computed localization. -/
theorem initialToQ_cofibration (X : ConditionalLocalization.Carrier hComparison) :
    cofibrations (ConditionalLocalization.Carrier hComparison)
      ((initialToQ hComparison).app X) := by
  apply (ConditionalLocalizedCarrier.cofibration_iff hComparison _).mpr
  have h := originalIFactorizationData.hi
    (Diagrams.fromZeroArrow.obj ((ConditionalLocalizedCarrier.toNative hComparison).obj X))
  change stableCofibrations ((ConditionalDefaults.initialToQOfComparison hComparison).app _) at h
  exact (initialToQ_component hComparison X).symm ▸ h

/-- The original I projection has the complete original trivial-right property. -/
theorem qCounit_trivialFibration (X : ConditionalLocalization.Carrier hComparison) :
    trivialFibrations (ConditionalLocalization.Carrier hComparison)
      ((qCounit hComparison).app X) := by
  apply (ConditionalLocalizedCarrier.trivialFibration_iff hComparison _).mpr
  have h := originalIFactorizationData.hp
    (Diagrams.fromZeroArrow.obj ((ConditionalLocalizedCarrier.toNative hComparison).obj X))
  change originalI.rlp ((ConditionalDefaults.QCounitOfComparison hComparison).app _) at h
  exact (qCounit_component hComparison X).symm ▸ h

/-- The original paired K injection has the actual localized trivial-left property. -/
theorem rUnit_trivialCofibration (X : ConditionalLocalization.Carrier hComparison) :
    trivialCofibrations (ConditionalLocalization.Carrier hComparison)
      ((rUnit hComparison).app X) := by
  apply (ConditionalLocalizedCarrier.trivialCofibration_iff hComparison _).mpr
  have h := originalKFactorizationData.hi
    (Diagrams.toZeroArrow.obj ((ConditionalLocalizedCarrier.toNative hComparison).obj X))
  change originalK.rlp.llp ((ConditionalDefaults.RUnitOfComparison hComparison).app _) at h
  exact (rUnit_component hComparison X).symm ▸ h

/-- The original K projection is the full localized paired right map. -/
theorem rToZero_fibration (X : ConditionalLocalization.Carrier hComparison) :
    fibrations (ConditionalLocalization.Carrier hComparison)
      ((rToZero hComparison).app X) := by
  apply (ConditionalLocalizedCarrier.fibration_iff hComparison _).mpr
  have h := originalKFactorizationData.hp
    (Diagrams.toZeroArrow.obj ((ConditionalLocalizedCarrier.toNative hComparison).obj X))
  change stableFibrations ((ConditionalDefaults.RToZeroOfComparison hComparison).app _) at h
  exact (rToZero_component hComparison X).symm ▸ h

/-- The actual original zero-source I record makes every Q object cofibrant. -/
theorem Q_isCofibrant (X : ConditionalLocalization.Carrier hComparison) :
    IsCofibrant ((QFunctor hComparison).obj X) := by
  rw [isCofibrant_iff_of_isInitial ((initialToQ hComparison).app X)
    (zeroIsInitial hComparison), HomotopicalAlgebra.cofibration_iff]
  exact initialToQ_cofibration hComparison X

/-- The actual original zero-target K record makes every R object fibrant. -/
theorem R_isFibrant (X : ConditionalLocalization.Carrier hComparison) :
    IsFibrant ((RFunctor hComparison).obj X) := by
  rw [isFibrant_iff_of_isTerminal ((rToZero hComparison).app X)
    (zeroIsTerminal hComparison), HomotopicalAlgebra.fibration_iff]
  exact rToZero_fibration hComparison X

/-- Every original R object has all native Omega structure maps at every actual pair. -/
theorem R_isOmega (X : ConditionalLocalization.Carrier hComparison) :
    NativeK.IsOmega orthogonalFamily
      ((ConditionalLocalizedCarrier.toNative hComparison).obj ((RFunctor hComparison).obj X)) :=
  (ConditionalLocalizedCarrier.isFibrant_iff_isOmega hComparison _).mp
    (R_isFibrant hComparison X)

/-- Both original comparison maps are weak in the same computed localization class. -/
theorem replacement_weak (X : ConditionalLocalization.Carrier hComparison) :
    weakEquivalences (ConditionalLocalization.Carrier hComparison)
        ((qCounit hComparison).app X) ∧
      weakEquivalences (ConditionalLocalization.Carrier hComparison)
        ((rUnit hComparison).app X) :=
  ⟨(qCounit_trivialFibration hComparison X).2, (rUnit_trivialCofibration hComparison X).2⟩

/-- Every source arrow retains all four complete original replacement naturality squares. -/
theorem replacement_naturality
    {X Y : ConditionalLocalization.Carrier hComparison} (f : X ⟶ Y) :
    (initialToQ hComparison).app X ≫ (QFunctor hComparison).map f =
        (initialToQ hComparison).app Y ∧
      (QFunctor hComparison).map f ≫ (qCounit hComparison).app Y =
        (qCounit hComparison).app X ≫ f ∧
      f ≫ (rUnit hComparison).app Y =
        (rUnit hComparison).app X ≫ (RFunctor hComparison).map f ∧
      (RFunctor hComparison).map f ≫ (rToZero hComparison).app Y =
        (rToZero hComparison).app X := by
  refine ⟨?_, (qCounit hComparison).naturality f, (rUnit hComparison).naturality f, ?_⟩
  · have h := (initialToQ hComparison).naturality f
    change 𝟙 _ ≫ (initialToQ hComparison).app Y =
      (initialToQ hComparison).app X ≫ (QFunctor hComparison).map f at h
    exact h.symm.trans (Category.id_comp _)
  · have h := (rToZero hComparison).naturality f
    change (RFunctor hComparison).map f ≫ (rToZero hComparison).app Y =
      (rToZero hComparison).app X ≫ 𝟙 _ at h
    exact h.trans (Category.comp_id _)

end PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalLocalizedReplacements
