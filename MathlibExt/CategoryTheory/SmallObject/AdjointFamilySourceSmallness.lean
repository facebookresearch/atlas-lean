/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily
public import MathlibExt.CategoryTheory.Adjunction.SourceHomColimit
public import MathlibExt.CategoryTheory.SmallObject.Closure
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Actual source smallness for indexed adjoint generator families

The same caller diagram, source member and mapped canonical cocone are kept.
Cardinal eligibility supplies all six actual fields at the chosen cardinal.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w t s vC vD uC uD

open CategoryTheory Limits Opposite

namespace HomotopicalAlgebra

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D] {S : Type s}
  (L : S → C ⥤ D) (R : S → D ⥤ C) (adj : ∀ a, L a ⊣ R a)
  (P Q : MorphismProperty C)

section ActualSourceColimit

variable {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  [∀ a, PreservesColimitsOfSize.{w, w} (R a)]
  [∀ a, PreservesColimitsOfShape T (R a)]
  [∀ a, PreservesWellOrderContinuousOfShape T (R a)]
  [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
  [Q.IsStableUnderTransfiniteComposition.{t}]
  (hEval : ∀ a, MorphismProperty.adjointFamilyGenerators L P ≤ Q.inverseImage (R a))
  (hSource : ∀ {A B : C} (g : A ⟶ B), P g →
    ∀ (F : T ⥤ C) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), Q (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op A)))

include R adj Q hEval hSource

/-- Source Hom for the caller's actual family member preserves the given cell colimit. -/
theorem adjointFamilySource_preservesColimit
    {A B X Y : D} (i : A ⟶ B)
    (hi : MorphismProperty.adjointFamilyGenerators L P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w}
      (fun (_ : T) => (MorphismProperty.adjointFamilyGenerators L P).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (op A)) := by
  obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff L P i).mp hi
  let ev := R q.1
  let _ : c.F.IsWellOrderContinuous :=
    c.toTransfiniteCompositionOfShape.isWellOrderContinuous
  let _ : (c.F ⋙ ev).IsWellOrderContinuous := inferInstance
  have hTransitions : ∀ ⦃a b⦄ (φ : a ⟶ b), Q ((c.F ⋙ ev).map φ) := by
    intro a b φ
    exact c.map_map_mem_of_le ev (MorphismProperty.adjointFamilyGenerators L P)
      Q (hEval q.1) φ
  let _ : PreservesColimit (c.F ⋙ ev) (coyoneda.obj (op q.2.1.left)) :=
    hSource q.2.1.hom q.2.2 (c.F ⋙ ev) hTransitions
  let _ : PreservesColimit c.F (coyoneda.obj (op ((L q.1).obj q.2.1.left))) :=
    (adj q.1).preservesColimit_leftAdjointSource q.2.1.left c.F
  let e : A ≅ (L q.1).obj q.2.1.left := Arrow.leftFunc.mapIso (eqToIso hq)
  exact preservesColimit_of_natIso c.F (coyoneda.mapIso e.op)

/-- The literal canonical cocone of the given cell diagram survives source Hom. -/
def adjointFamilySourceMappedCanonicalCocone
    {A B X Y : D} (i : A ⟶ B)
    (hi : MorphismProperty.adjointFamilyGenerators L P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w}
      (fun (_ : T) => (MorphismProperty.adjointFamilyGenerators L P).homFamily) f)
    [HasColimit c.F] :
    IsColimit ((coyoneda.obj (op A)).mapCocone (colimit.cocone c.F)) := by
  let _ : PreservesColimit c.F (coyoneda.obj (op A)) :=
    adjointFamilySource_preservesColimit L R adj P Q hEval hSource i hi f c
  exact isColimitOfPreserves (coyoneda.obj (op A)) (colimit.isColimit c.F)


/-- Deprecated alias retaining the original public colimit map. -/
@[deprecated adjointFamilySourceMappedCanonicalCocone (since := "2026-11-06"),
  nolint defsWithUnderscore]
alias adjointFamilySource_mappedCanonicalCocone := adjointFamilySourceMappedCanonicalCocone

end ActualSourceColimit

section ChosenCardinal

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} S] [P.IsSmall.{w}] [LocallySmall.{w} D]
  [HasPushouts D] [HasCoproducts.{w} D] [HasIterationOfShape κ.ord.ToType D]
  [∀ a, PreservesColimitsOfSize.{w, w} (R a)]
  [∀ a, PreservesColimitsOfShape κ.ord.ToType (R a)]
  [∀ a, PreservesWellOrderContinuousOfShape κ.ord.ToType (R a)]
  [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
  [Q.IsStableUnderTransfiniteComposition.{w}]
  (hEval : ∀ a, MorphismProperty.adjointFamilyGenerators L P ≤ Q.inverseImage (R a))
  (hSource : ∀ {A B : C} (g : A ⟶ B), P g →
    ∀ (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), Q (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op A)))

include R adj Q hEval hSource

/-- All six actual eligibility fields at the given cardinal and caller bottom. -/
theorem adjointFamily_isCardinalForSmallObjectArgument :
    (MorphismProperty.adjointFamilyGenerators L P).IsCardinalForSmallObjectArgument κ :=
  { isSmall := MorphismProperty.adjointFamilyGenerators_isSmall L P
    locallySmall := inferInstance
    hasPushouts := inferInstance
    hasCoproducts := inferInstance
    hasIterationOfShape := inferInstance
    preservesColimit := fun i hi f c =>
      adjointFamilySource_preservesColimit L R adj P Q hEval hSource i hi f c }

/-- Package the same actual cardinal eligibility as a small-object argument. -/
theorem adjointFamily_hasSmallObjectArgument :
    (MorphismProperty.adjointFamilyGenerators L P).HasSmallObjectArgument.{w} :=
  ⟨κ, inferInstance, inferInstance,
    adjointFamily_isCardinalForSmallObjectArgument L R adj P Q κ hEval hSource⟩

end ChosenCardinal

end HomotopicalAlgebra
