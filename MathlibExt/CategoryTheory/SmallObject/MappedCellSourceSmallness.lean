/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.SmallObject.AdjointFamilySourceSmallness

/-!
# Source smallness on the original evaluated free-cell diagrams

The premise concerns the original base source Hom functor on each actual
evaluated cell diagram. The adjunction transfers that same colimit, retaining
the source label, caller cardinal, ordinal bottom and all six eligibility fields.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uS uC vC uD vD

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.MappedCellSourceSmallness

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] {S : Type uS}
  (L : S → C ⥤ D) (R : S → D ⥤ C) (P : MorphismProperty C)
  (κ : Cardinal.{w}) [OrderBot κ.ord.ToType]

/-- The original source-Hom premise is restricted to the actual evaluated free-cell diagrams. -/
def Condition : Prop :=
  ∀ (s : S) {A B : C} (i : A ⟶ B), P i →
    ∀ {X Y : D} (f : X ⟶ Y)
      (c : RelativeCellComplex.{w}
        (fun _ : κ.ord.ToType => (adjointFamilyGenerators L P).homFamily) f),
      PreservesColimit (c.F ⋙ R s) (coyoneda.obj (op A))

variable (adj : ∀ s, L s ⊣ R s)
  [∀ s, PreservesColimitsOfShape κ.ord.ToType (R s)]

include adj

/-- The same actual source member and cell diagram retain their source-Hom colimit. -/
theorem preservesColimit (hSource : Condition L R P κ)
    {A B X Y : D} (i : A ⟶ B) (hi : adjointFamilyGenerators L P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => (adjointFamilyGenerators L P).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (op A)) := by
  obtain ⟨q, hq⟩ := (adjointFamilyGenerators_iff L P i).mp hi
  let _ : PreservesColimit (c.F ⋙ R q.1) (coyoneda.obj (op q.2.1.left)) :=
    hSource q.1 q.2.1.hom q.2.2 f c
  let _ : PreservesColimit c.F (coyoneda.obj (op ((L q.1).obj q.2.1.left))) :=
    (adj q.1).preservesColimit_leftAdjointSource q.2.1.left c.F
  let e : A ≅ (L q.1).obj q.2.1.left := Arrow.leftFunc.mapIso (eqToIso hq)
  exact preservesColimit_of_natIso c.F (coyoneda.mapIso e.op)

/-- The original canonical cell cocone remains a colimit under the original source Hom functor. -/
def mappedCanonicalCocone (hSource : Condition L R P κ)
    {A B X Y : D} (i : A ⟶ B) (hi : adjointFamilyGenerators L P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => (adjointFamilyGenerators L P).homFamily) f)
    [HasColimit c.F] :
    IsColimit ((coyoneda.obj (op A)).mapCocone (colimit.cocone c.F)) := by
  let _ : PreservesColimit c.F (coyoneda.obj (op A)) :=
    preservesColimit L R P κ adj hSource i hi f c
  exact isColimitOfPreserves (coyoneda.obj (op A)) (colimit.isColimit c.F)

variable [Fact κ.IsRegular] [Small.{w} S] [P.IsSmall.{w}] [LocallySmall.{w} D]
  [HasPushouts D] [HasCoproducts.{w} D] [HasIterationOfShape κ.ord.ToType D]

/-- Every actual target eligibility field is derived at the same caller cardinal and ordinal
bottom. -/
theorem isCardinalForSmallObjectArgument (hSource : Condition L R P κ) :
    (adjointFamilyGenerators L P).IsCardinalForSmallObjectArgument κ where
  isSmall := adjointFamilyGenerators_isSmall L P
  locallySmall := inferInstance
  hasPushouts := inferInstance
  hasCoproducts := inferInstance
  hasIterationOfShape := inferInstance
  preservesColimit i hi f c := preservesColimit L R P κ adj hSource i hi f c

/-- The same actual cardinal and bottom package the original free-family small-object argument. -/
theorem hasSmallObjectArgument (hSource : Condition L R P κ) :
    (adjointFamilyGenerators L P).HasSmallObjectArgument.{w} :=
  ⟨κ, inferInstance, inferInstance, isCardinalForSmallObjectArgument L R P κ adj hSource⟩

end HomotopicalAlgebra.MappedCellSourceSmallness
