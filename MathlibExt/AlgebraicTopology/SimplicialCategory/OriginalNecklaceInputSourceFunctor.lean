/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceRawCoefficientFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceSourceNaturality

/-!
# The SAME entire original necklace input source functor

Every original source simplicial map retains each whole native necklace,
its entire input composition and both actual endpoint images. Every
native arrow and its complete raw Hom coefficient remain unchanged.
The original source identities and compositions are retained literally.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

variable {K L M : SSet.{u}} {x y : K _⦋0⦌}

/-- The SAME original input source image retains the entire native necklace and original input composition. -/
def sourceObject (f : K ⟶ L) (T : Object K x y) :
    Object L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) where
  necklace := T.necklace
  input := T.input ≫ f
  source_eq :=
    ((congrArg SSet.yonedaEquiv (Category.assoc T.necklace.source T.input f).symm).trans
      (SSet.yonedaEquiv_comp (T.necklace.source ≫ T.input) f)).trans
        (congrArg (f.app (op ⦋0⦌)) T.source_eq)
  target_eq :=
    ((congrArg SSet.yonedaEquiv (Category.assoc T.necklace.target T.input f).symm).trans
      (SSet.yonedaEquiv_comp (T.necklace.target ≫ T.input) f)).trans
        (congrArg (f.app (op ⦋0⦌)) T.target_eq)

/-- Every actual whole original native arrow retains its SAME full input square under the source map. -/
def sourceHom (f : K ⟶ L) {T U : Object K x y} (g : T ⟶ U) : sourceObject f T ⟶ sourceObject f U where
  necklaceMap := g.necklaceMap
  over := (Category.assoc g.necklaceMap.map U.input f).symm.trans (congrArg (fun a => a ≫ f) g.over)

/-- The actual full original native input source functor, preserving all original native maps. -/
def sourceFunctor (f : K ⟶ L) (x y : K _⦋0⦌) :
    Object K x y ⥤ Object L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) where
  obj := sourceObject f
  map := sourceHom f
  map_id _T := Hom.ext rfl
  map_comp _g _h := Hom.ext rfl

/-- The full original source identity is the SAME entire original input-category identity. -/
theorem sourceFunctor_id (K : SSet.{u}) (x y : K _⦋0⦌) : sourceFunctor (𝟙 K) x y = 𝟭 (Object K x y) := rfl

/-- Both full original source maps compose by the SAME entire original input composition. -/
theorem sourceFunctor_comp (f : K ⟶ L) (g : L ⟶ M) (x y : K _⦋0⦌) :
    sourceFunctor (f ≫ g) x y = sourceFunctor f x y ⋙
      sourceFunctor g (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) := rfl

/-- The complete original source functor retains every literal original native object. -/
theorem sourceFunctor_forget (f : K ⟶ L) (x y : K _⦋0⦌) :
    sourceFunctor f x y ⋙ forget L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) = forget K x y := rfl

/-- The SAME whole original source map retains the literal raw coefficient diagram. -/
theorem rawCoefficientDiagram_source (f : K ⟶ L) (x y : K _⦋0⦌) :
    sourceFunctor f x y ⋙ rawCoefficientDiagram L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) =
      rawCoefficientDiagram K x y := rfl

/-- The SAME whole original source map retains the literal joint-coefficient diagram. -/
theorem fullCoefficientDiagram_source (f : K ⟶ L) (x y : K _⦋0⦌) :
    sourceFunctor f x y ⋙ fullCoefficientDiagram L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) =
      fullCoefficientDiagram K x y := rfl

/-- EVERY original flagged coefficient element retains the SAME full original source input. -/
theorem toFlaggedObject_source (f : K ⟶ L) {q : SimplexCategoryᵒᵖ}
    (E : (degreeCoefficient K x y q).Elements) :
    OriginalFlaggedNecklace.sourceObject f (toFlaggedObject E) =
      toFlaggedObject ((degreeCoefficient L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) q).elementsMk
        (sourceObject f E.obj) E.val) := rfl

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
