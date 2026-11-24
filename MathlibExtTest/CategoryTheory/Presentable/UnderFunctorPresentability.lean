/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.UnderFunctorPresentability
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeDiagramActionCapture

/-!
# Relative whole under-functor compactness at the original noncompact coefficient

The actual original source functor and all original index arrows remain.
Its identity under-object has relatively compact components, even though
its actual source-seven coefficient has cardinal chi and is not absolutely
chi-presentable. Native relative equation labels keep both original parallel
arrows through coincident target actions.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  CategoryTheory.Presentable.UnderFunctorPresentability

namespace RelativeUnderFunctorPresentabilityExamples

open OriginalDiagramActionCaptureExamples DiagramActionConstraintBoundExamples

/-- The original whole under-object is the identity of the same actual source functor. -/
abbrev originalIdentityUnder : Under originalSource := Under.mk (𝟙 originalSource)

/-- Its every component is compact under its own original coefficient root. -/
theorem originalIdentityComponents (d : OriginalIndex) :
    IsCardinalPresentable ((relativeEvaluation originalSource d).obj originalIdentityUnder) chi :=
      by
  have hB : HasCardinalLT ((⊥ : LowerSet (originalLabels d)) : Set (originalLabels d)) chi := by
    change HasCardinalLT (∅ : Set (originalLabels d)) chi
    exact hasCardinalLT_of_finite _ chi chi_regular.aleph0_le
  let : IsCardinalPresentable ((originalLower.{0} d).obj ⊥) chi :=
    RelativeCellPresentability.selectedLower chi (originalTrees.{0}.component d).tree
      (originalTrees_good.{0} d) (originalLower.{0} d) ⊥ hB
  have h := isCardinalPresentable_of_iso
    ((originalTrees.{0}.component d).tree.emptyLowerIso (originalLower.{0} d)) chi
  change IsCardinalPresentable (Under.mk (𝟙 (originalSource.obj d))) chi
  exact h

/-- The real relative whole-functor criterion applies without any compact original root premise. -/
theorem originalIdentityWholeRelative : IsCardinalPresentable originalIdentityUnder chi :=
  relative_diagram_presentable originalSource chi originalArrowBound
    originalIdentityUnder originalIdentityComponents

/-- The same actual original source coefficient remains noncompact at the SAME chi. -/
theorem originalIdentitySourceNotAbsolute :
    ¬ IsCardinalPresentable (originalIdentityUnder.right.obj sourceSeven) chi := by
  change ¬ IsCardinalPresentable LargeRoot chi
  exact largeRoot_not_presentable

/-- Native under evaluation retains every original component root as the whole object function. -/
theorem actualRelativeComponentFunction (d : OriginalIndex) :
    (fun V : Under originalSource => ((relativeEvaluation originalSource d).obj V).hom) =
      (fun V : Under originalSource => V.hom.app d) := rfl

/-- Its complete original morphism component function is the actual right natural transformation. -/
theorem actualRelativeMapFunction (d : OriginalIndex) :
    (fun (V W : Under originalSource) (a : V ⟶ W) =>
      ((relativeEvaluation originalSource d).map a).right) =
    (fun (V W : Under originalSource) (a : V ⟶ W) => a.right.app d) := rfl

/-- The whole original target under-object contains the same original F→G transformation. -/
abbrev originalTargetUnder : Under originalSource := Under.mk originalMap

/-- Both original parallel inputs are still different right labels in the native end shape. -/
theorem originalEquationRightLabelsDifferent :
    (WalkingMulticospan.right (Arrow.mk firstArrow) :
      WalkingMulticospan (multicospanShapeEnd OriginalIndex)) ≠
      WalkingMulticospan.right (Arrow.mk secondArrow) := by
  intro h
  have ha : Arrow.mk firstArrow = Arrow.mk secondArrow := by cases h
  exact originalArrowValuesDifferent ha

/-- Both original target coefficient actions coincide in the actual original target under-object. -/
theorem originalTargetStructureRightActionsEqual :
    ((structureAction originalSource firstArrow).app originalTargetUnder).right =
      ((structureAction originalSource secondArrow).app originalTargetUnder).right := rfl

/-- Every original actual g is retained in the whole native structure-action function. -/
theorem actualStructureActionFunction {d e : OriginalIndex} (g : d ⟶ e) :
    (fun V : Under originalSource => ((structureAction originalSource g).app V).right) =
      (fun V : Under originalSource => V.right.map g) := rfl

/-- The complete native equation cone projects the same original under-component functions. -/
theorem actualWholeHomComponent (V : Under originalSource)
    (a : originalIdentityUnder ⟶ V) (d : OriginalIndex) :
    (((componentCone originalSource originalIdentityUnder).ι d).app V) (ULift.up a) =
      ULift.up ((relativeEvaluation originalSource d).map a) := rfl

/-- Its actual inverse universal lift retains each original component function and root. -/
theorem actualWholeLiftComponent
    (T : Multifork (equationIndex originalSource originalIdentityUnder))
    (V : Under originalSource) (x : T.pt.obj V) (d : OriginalIndex) :
    (componentLiftMorphism originalSource originalIdentityUnder T V x).right.app d =
      (((T.ι d).app V) x).down.right := rfl

section IndependentUniverses

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [HasColimitsOfSize.{w, w} C] (F : D ⥤ C)
  (k : Cardinal.{w}) [Fact k.IsRegular] (hArrow : HasCardinalLT (Arrow D) k)
  (U : Under F) (hU : ∀ d, IsCardinalPresentable (Under.mk (U.hom.app d)) k)

include hArrow hU in
/-- The expected whole relative TYPE keeps all original object, Hom and working universes
independent. -/
theorem independentOriginalRelativeCompactness : IsCardinalPresentable U k :=
  relative_diagram_presentable F k hArrow U hU

end IndependentUniverses

end RelativeUnderFunctorPresentabilityExamples
