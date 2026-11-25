/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.CategoryTheory.SmallObject.IsoEligibility

/-!# Original chains and actual same-cardinal isomorphic-family eligibility -/
set_option autoImplicit false
noncomputable section
universe w t u v
open CategoryTheory Limits MorphismProperty Opposite

namespace MathlibExtTest.IsoEligibility

variable {C : Type u} [Category.{v} C] (P Q : MorphismProperty C)
  (q : P.toSet → Q.toSet)
  (e : ∀ p : P.toSet, Arrow.mk p.1.hom ≅ Arrow.mk (q p).1.hom)

section OriginalChain

variable {J : Type t} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : C} {f : X ⟶ Y}
  (c : HomotopicalAlgebra.RelativeCellComplex.{w} (fun _ : J => P.homFamily) f)

example : HomotopicalAlgebra.RelativeCellComplex.{w} (fun _ : J => Q.homFamily) f :=
  c.reindexByArrowIso P Q q e

example : (c.reindexByArrowIso P Q q e).F = c.F :=
  c.reindexByArrowIso_F P Q q e

example : (c.reindexByArrowIso P Q q e).incl = c.incl :=
  c.reindexByArrowIso_incl P Q q e

example (j : J) : (c.reindexByArrowIso P Q q e).incl.app j = c.incl.app j :=
  NatTrans.congr_app (c.reindexByArrowIso_incl P Q q e) j

example : (c.reindexByArrowIso P Q q e).toTransfiniteCompositionOfShape =
    c.toTransfiniteCompositionOfShape :=
  c.reindexByArrowIso_transfinite P Q q e

end OriginalChain

section SameCardinal

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [P.IsSmall.{w}] [LocallySmall.{w} C] [HasPushouts C] [HasCoproducts.{w} C]
  [HasIterationOfShape κ.ord.ToType C] [Q.IsCardinalForSmallObjectArgument κ]

example : P.IsCardinalForSmallObjectArgument κ :=
  isCardinalForSmallObjectArgument_of_arrowIso P Q κ q e

example : P.IsSmall.{w} ∧ LocallySmall.{w} C ∧ HasPushouts C ∧ HasCoproducts.{w} C ∧
    HasIterationOfShape κ.ord.ToType C := by
  have h := isCardinalForSmallObjectArgument_of_arrowIso P Q κ q e
  exact ⟨h.isSmall, h.locallySmall, h.hasPushouts, h.hasCoproducts, h.hasIterationOfShape⟩

example {A B X Y : C} (i : A ⟶ B) (hi : P i) (f : X ⟶ Y)
    (c : HomotopicalAlgebra.RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => P.homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (op A)) :=
  (isCardinalForSmallObjectArgument_of_arrowIso P Q κ q e).preservesColimit i hi f c

example (h : P ≤ Q.isoClosure) : P.IsCardinalForSmallObjectArgument κ :=
  isCardinalForSmallObjectArgument_of_isoClosure P Q κ h

end SameCardinal

end MathlibExtTest.IsoEligibility
