/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalTransfiniteSliceFiltration

set_option autoImplicit false
noncomputable section

universe w t uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.SmallObject.DiagramActionCapture
open CategoryTheory.SmallObject.DiagramSliceExhaustion
open CategoryTheory.SmallObject.OriginalTransfiniteSliceFiltration
open CategoryTheory.SmallObject.CompactRootBaseChange
open HomotopicalAlgebra HomotopicalAlgebra.FunctorInjective

attribute [local instance] constructionIndexWellFounded constructionIndexSuccOrder

section OriginalLowerChoices

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (hUncountable : Cardinal.aleph0 < chi) (hArrow : HasCardinalLT (Arrow D) chi)
  (good : ∀ d, (theta.component d).tree.IsGood chi)

-- The actual original lower choices supply every BEFORE and the whole original endpoint UP.
example (p : HistoryIndex (P := P)) :
    IsColimit (beforeCocone theta L chi hUncountable hArrow good p) :=
  beforeIsColimit theta L chi hUncountable hArrow good p

example : IsColimit (endpointCocone theta L chi hUncountable hArrow good) :=
  endpointIsColimit theta L chi hUncountable hArrow good

example (p : HistoryIndex (P := P)) :
    IsPushout (birth theta L chi hUncountable hArrow good p).intoBefore.toNatTrans
      (birth theta L chi hUncountable hArrow good p).intoPatch.toNatTrans
      (beforeToAfter theta L chi hUncountable hArrow good p).toNatTrans
      (birth theta L chi hUncountable hArrow good p).patchInclusion.toNatTrans :=
  (birth theta L chi hUncountable hArrow good p).isPushout

example : TransfiniteCompositionOfShape (ConstructionIndex (HistoryIndex (P := P))) f :=
  continuousPresentation theta L chi hUncountable hArrow good

-- The original full-label bijection remains valid when all original label carriers are empty.
example (hEmpty : ∀ d, IsEmpty (P d)) : IsEmpty (HistoryIndex (P := P)) :=
  ⟨fun p => (hEmpty p.1).false p.2⟩

example (hEmpty : ∀ d, IsEmpty (P d)) (a : D) :
    (whole theta L chi hUncountable hArrow good).supports a = ⊥ := by
  let : IsEmpty (P a) := hEmpty a
  ext p
  exact isEmptyElim p

end OriginalLowerChoices

section OriginalCoefficientModel

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)
  (b : BoundedConstruction d kappaLP s.equivalence) {F G : D ⥤ C}
  (f : F ⟶ G) (hf : ∀ a : D, cofibrations C (f.app a))

-- The model constructs the whole native presentation using the exact selected s.index bound.
example : TransfiniteCompositionOfShape
    (ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf)) f :=
  originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf

example :
    (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).isoBot.inv ≫
      (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).incl.app ⊥ = f :=
  originalTransfiniteFiltration_fac d kappaLP s b f hf

example : IsColimit (originalSliceEndpointCocone d kappaLP s b f hf) :=
  originalSliceEndpointIsColimit d kappaLP s b f hf

example (p : originalSliceHistoryIndex d kappaLP s b f hf) :
    IsColimit (originalSliceBeforeCocone d kappaLP s b f hf p) :=
  originalSliceBeforeIsColimit d kappaLP s b f hf p

example :
    originalTransfiniteFiltrationUnder d kappaLP s b f hf ⋙ Under.forget F =
      (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F :=
  originalTransfiniteFiltration_under_forget d kappaLP s b f hf

example (p : originalSliceHistoryIndex d kappaLP s b f hf) :
    letI := originalSliceComponentOrders d kappaLP s b f hf
    HasCardinalLT (originalSliceBirth d kappaLP s b f hf p).NewLabels b.cardinal :=
  originalSliceBirthLabelsBound d kappaLP s b f hf p

-- Both actual native successor comparison maps and all original birth maps are consumed.
example (p : originalSliceHistoryIndex d kappaLP s b f hf) :
    letI := originalSliceComponentOrders d kappaLP s b f hf
    Nonempty (Arrow.mk ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.map
      (homOfLE (Order.le_succ (constructionLabel p)))) ≅
        Arrow.mk ((originalFiltrationEquivalence s).inverse.map
          (originalSliceBirth d kappaLP s b f hf p).beforeInclusion.toNatTrans)) := by
  let := originalSliceComponentOrders d kappaLP s b f hf
  exact ⟨originalTransfiniteFiltrationBirthIso d kappaLP s b f hf p⟩

example : IsIso ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.map
    (homOfLE (Order.le_succ
      (⊥ : ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf))))) :=
  originalTransfiniteFiltrationBotMapIsIso d kappaLP s b f hf

example (gamma : ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf))
    {a c : D} (g : a ⟶ c) :
    ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj gamma).map g =
      (((boundedCofibrationTransfiniteSliceFiltration d kappaLP
        (originalFiltrationSelectedIndex s) (originalFiltrationSelectedSource d kappaLP s b)
        (originalFiltrationSelectedArrow s f) (originalFiltrationSelectedCofibration s f hf)
        b.profile.arrows).F.obj gamma).map (s.equivalence.functor.map g)) :=
  originalTransfiniteFiltration_action d kappaLP s b f hf gamma g

end OriginalCoefficientModel
