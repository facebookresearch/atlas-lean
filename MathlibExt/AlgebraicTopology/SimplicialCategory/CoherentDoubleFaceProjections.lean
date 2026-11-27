/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentDoubleCompositionFace

/-!
# Original interval projections of the double composition face

The actual triple-Hom chart projects to each original positive face by
the corresponding original union composition. Both parenthesizations
retain their literal scalar maps and original interval endpoints.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.DoubleFaceProjections
open CompositionFace DoubleCompositionFace
variable {J : Type u} [LinearOrder J] (i j k l : J) (hjk : j ≤ k)

/-- The actual first projection from the double composition face. -/
def first : (DoubleCompositionFace.face i j k l : SSet.{u}) ⟶ positive i j l :=
  SSet.Subcomplex.homOfLE (show DoubleCompositionFace.face i j k l ≤ positive i j l from
    inf_le_left)

/-- The actual second projection from the same double composition face. -/
def second : (DoubleCompositionFace.face i j k l : SSet.{u}) ⟶ positive i k l :=
  SSet.Subcomplex.homOfLE (show DoubleCompositionFace.face i j k l ≤ positive i k l from
    inf_le_right)

/-- The first projection reads back the whole right short-leg union before the original
positive chart. -/
theorem first_chart : (faceIso i j k l hjk).hom ≫ first i j k l =
    nerve (SimplicialThickening.Path i j) ◁ CompositionFace.composition j k l ≫
      (positiveIso i j l).hom := by
  apply (cancel_mono (positive i j l).ι).mp
  have h₁ := (Category.assoc (faceIso i j k l hjk).hom (first i j k l) (positive i j l).ι).trans
    (congrArg (fun g => (faceIso i j k l hjk).hom ≫ g)
      (SSet.Subcomplex.homOfLE_ι (show DoubleCompositionFace.face i j k l ≤ positive i j
        l from inf_le_left)))
  have h₂ := (Category.assoc (nerve (SimplicialThickening.Path i j) ◁
    CompositionFace.composition j k l)
    (positiveIso i j l).hom (positive i j l).ι).trans
      (congrArg (fun g => (nerve (SimplicialThickening.Path i j) ◁
        CompositionFace.composition j k l) ≫ g)
        (positiveIso_composition i j l))
  exact h₁.trans ((faceIso_composition i j k l hjk).trans h₂.symm)

/-- The other projection reads back the whole left short-leg union with the actual original
associator. -/
theorem second_chart : (faceIso i j k l hjk).hom ≫ second i j k l =
    (α_ (nerve (SimplicialThickening.Path i j)) (nerve (SimplicialThickening.Path j k))
      (nerve (SimplicialThickening.Path k l))).inv ≫
        CompositionFace.composition i j k ▷ nerve (SimplicialThickening.Path k l) ≫
          (positiveIso i k l).hom := by
  apply (cancel_mono (positive i k l).ι).mp
  have h₁ := (Category.assoc (faceIso i j k l hjk).hom (second i j k l) (positive i k l).ι).trans
    (congrArg (fun g => (faceIso i j k l hjk).hom ≫ g)
      (SSet.Subcomplex.homOfLE_ι (show DoubleCompositionFace.face i j k l ≤ positive i k
        l from inf_le_right)))
  have h₂ : ((α_ (nerve (SimplicialThickening.Path i j)) (nerve (SimplicialThickening.Path j k))
      (nerve (SimplicialThickening.Path k l))).inv ≫
        CompositionFace.composition i j k ▷ nerve (SimplicialThickening.Path k l) ≫
          (positiveIso i k l).hom) ≫
          (positive i k l).ι = DoubleCompositionFace.composition i j k l := by
    rw [Category.assoc, Category.assoc, positiveIso_composition]
    exact left_composition i j k l
  exact h₁.trans ((faceIso_composition i j k l hjk).trans h₂.symm)

end CategoryTheory.CoherentRealization.DoubleFaceProjections
