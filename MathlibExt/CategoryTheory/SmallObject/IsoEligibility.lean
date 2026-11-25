/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# The same small-object cardinal for an isomorphic small family

Each original P-arrow is identified with an actual Q-arrow by a whole
Arrow isomorphism. Reindex only the actual attachment labels. The complete
original chain, endpoint and inclusion stay unchanged.

The P family is genuinely small. Neither its eligibility nor smallness of
the possibly large isomorphism closure of Q is assumed. All six fields
use the same caller cardinal and ordinal bottom.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w t u v
open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.RelativeCellComplex

variable {C : Type u} [Category.{v} C] (P Q : MorphismProperty C)
  (q : P.toSet → Q.toSet)
  (e : ∀ p : P.toSet, Arrow.mk p.1.hom ≅ Arrow.mk (q p).1.hom)
  {J : Type t} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : J => P.homFamily) f)

/-- Reindex every actual cell by its chosen whole Arrow isomorphism to the Q-family. -/
def reindexByArrowIso :
    RelativeCellComplex.{w} (fun _ : J => Q.homFamily) f where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
  attachCells j hj := (c.attachCells j hj).reindexCellTypes Q.homFamily q e

/-- Reindexing keeps the whole original chain functor, including all of its maps. -/
theorem reindexByArrowIso_F : (reindexByArrowIso P Q q e c).F = c.F := rfl

/-- Reindexing keeps the actual original endpoint inclusion at every stage. -/
theorem reindexByArrowIso_incl : (reindexByArrowIso P Q q e c).incl = c.incl := rfl

/-- The full original structural transfinite-composition record is retained. -/
theorem reindexByArrowIso_transfinite :
    (reindexByArrowIso P Q q e c).toTransfiniteCompositionOfShape =
      c.toTransfiniteCompositionOfShape := rfl

end HomotopicalAlgebra.RelativeCellComplex

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (P Q : MorphismProperty C)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- All six original P-fields follow from actual Q eligibility and chosen Arrow isomorphisms. -/
theorem isCardinalForSmallObjectArgument_of_arrowIso
    [P.IsSmall.{w}] [LocallySmall.{w} C] [HasPushouts C] [HasCoproducts.{w} C]
    [HasIterationOfShape κ.ord.ToType C] [Q.IsCardinalForSmallObjectArgument κ]
    (q : P.toSet → Q.toSet)
    (e : ∀ p : P.toSet, Arrow.mk p.1.hom ≅ Arrow.mk (q p).1.hom) :
    P.IsCardinalForSmallObjectArgument κ where
  isSmall := inferInstance
  locallySmall := inferInstance
  hasPushouts := inferInstance
  hasCoproducts := inferInstance
  hasIterationOfShape := inferInstance
  preservesColimit {A B X Y} i hi f c := by
    let d := c.reindexByArrowIso P Q q e
    let p : P.toSet := ⟨Arrow.mk i, hi⟩
    let _ : PreservesColimit d.F (coyoneda.obj (Opposite.op (q p).1.left)) :=
      SmallObject.preservesColimit Q κ (q p).1.hom (q p).2 f d
    have hF : d.F = c.F := rfl
    let _ : PreservesColimit c.F (coyoneda.obj (Opposite.op (q p).1.left)) := hF ▸ inferInstance
    let sourceIso : A ≅ (q p).1.left := Arrow.leftFunc.mapIso (e p)
    exact preservesColimit_of_natIso c.F (coyoneda.mapIso sourceIso.op)

/-- A genuine inclusion into the Q isomorphism closure supplies the same actual cardinal. -/
theorem isCardinalForSmallObjectArgument_of_isoClosure
    [P.IsSmall.{w}] [LocallySmall.{w} C] [HasPushouts C] [HasCoproducts.{w} C]
    [HasIterationOfShape κ.ord.ToType C] [Q.IsCardinalForSmallObjectArgument κ]
    (h : P ≤ Q.isoClosure) :
    P.IsCardinalForSmallObjectArgument κ := by
  have witness (p : P.toSet) :
      ∃ q : Q.toSet, Nonempty (Arrow.mk p.1.hom ≅ Arrow.mk q.1.hom) := by
    obtain ⟨A, B, f, hf, ⟨e⟩⟩ := h p.1.hom p.2
    exact ⟨⟨Arrow.mk f, hf⟩, ⟨e.symm⟩⟩
  let q (p : P.toSet) : Q.toSet := (witness p).choose
  let e (p : P.toSet) : Arrow.mk p.1.hom ≅ Arrow.mk (q p).1.hom :=
    (witness p).choose_spec.some
  exact isCardinalForSmallObjectArgument_of_arrowIso P Q κ q e

end CategoryTheory.MorphismProperty
