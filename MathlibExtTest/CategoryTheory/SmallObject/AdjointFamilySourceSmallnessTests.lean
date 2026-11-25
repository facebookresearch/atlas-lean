/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.AdjointFamilySourceSmallness

set_option autoImplicit false
noncomputable section
universe w t s vC vD uC uD

open CategoryTheory Limits Opposite HomotopicalAlgebra

namespace MathlibExtTest.AdjointFamilySourceSmallness

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {S : Type s} (L : S → C ⥤ D) (R : S → D ⥤ C) (adj : ∀ a, L a ⊣ R a)
  (P Q : MorphismProperty C)

section ActualCallerDiagram

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
  {A B X Y : D} (i : A ⟶ B)
  (hi : MorphismProperty.adjointFamilyGenerators L P i) (f : X ⟶ Y)
  (c : RelativeCellComplex.{w}
    (fun (_ : T) => (MorphismProperty.adjointFamilyGenerators L P).homFamily) f)

-- The exact original diagram and source object occur in the returned preservation.
example : PreservesColimit c.F (coyoneda.obj (op A)) :=
  adjointFamilySource_preservesColimit L R adj P Q hEval hSource i hi f c

-- The caller's literal canonical colimit cocone is retained as actual IsColimit data.
example [HasColimit c.F] :
    IsColimit ((coyoneda.obj (op A)).mapCocone (colimit.cocone c.F)) :=
  adjointFamilySourceMappedCanonicalCocone L R adj P Q hEval hSource i hi f c

-- Actual supplied source-Hom preservation applies to the same diagram cocone.
example (d : Cocone c.F) (hd : IsColimit d) :
    IsColimit ((coyoneda.obj (op A)).mapCocone d) := by
  let _ : PreservesColimit c.F (coyoneda.obj (op A)) :=
    adjointFamilySource_preservesColimit L R adj P Q hEval hSource i hi f c
  exact isColimitOfPreserves (coyoneda.obj (op A)) hd

end ActualCallerDiagram

section ExactCardinal

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

example : (MorphismProperty.adjointFamilyGenerators L P).IsCardinalForSmallObjectArgument κ :=
  adjointFamily_isCardinalForSmallObjectArgument L R adj P Q κ hEval hSource

-- All six real eligibility fields are exposed at this same original κ/bottom.
example : (MorphismProperty.adjointFamilyGenerators L P).IsSmall.{w} :=
  (adjointFamily_isCardinalForSmallObjectArgument L R adj P Q κ hEval hSource).isSmall

example : LocallySmall.{w} D :=
  (adjointFamily_isCardinalForSmallObjectArgument L R adj P Q κ hEval hSource).locallySmall

example : HasPushouts D :=
  (adjointFamily_isCardinalForSmallObjectArgument L R adj P Q κ hEval hSource).hasPushouts

example : HasCoproducts.{w} D :=
  (adjointFamily_isCardinalForSmallObjectArgument L R adj P Q κ hEval hSource).hasCoproducts

example : HasIterationOfShape κ.ord.ToType D :=
  (adjointFamily_isCardinalForSmallObjectArgument L R adj P Q κ hEval hSource).hasIterationOfShape

example {A B X Y : D} (i : A ⟶ B)
    (hi : MorphismProperty.adjointFamilyGenerators L P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) => (MorphismProperty.adjointFamilyGenerators L P).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (op A)) :=
  (adjointFamily_isCardinalForSmallObjectArgument L R adj P Q κ hEval hSource).preservesColimit
    i hi f c

example : (MorphismProperty.adjointFamilyGenerators L P).HasSmallObjectArgument.{w} :=
  adjointFamily_hasSmallObjectArgument L R adj P Q κ hEval hSource

end ExactCardinal

#check @adjointFamilySource_preservesColimit
#check @adjointFamilySourceMappedCanonicalCocone
#check @adjointFamily_isCardinalForSmallObjectArgument
#check @adjointFamily_hasSmallObjectArgument
#print axioms adjointFamilySource_preservesColimit
#print axioms adjointFamilySourceMappedCanonicalCocone
#print axioms adjointFamily_isCardinalForSmallObjectArgument
#print axioms adjointFamily_hasSmallObjectArgument

end MathlibExtTest.AdjointFamilySourceSmallness
