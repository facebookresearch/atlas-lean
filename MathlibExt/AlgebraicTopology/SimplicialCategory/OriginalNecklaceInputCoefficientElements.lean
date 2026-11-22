/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceInputCategory
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceFullCoefficientFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceScalarDiagram
import Mathlib.CategoryTheory.Elements

/-!
# The SAME full flagged category is the original coefficient elements category

The full input indexing category and the entire native joint-coefficient
diagram have exactly the original flagged objects and morphisms as their
category of elements in each scalar degree. Both actual functors and
strict inverse identities retain every input map and coefficient flag.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

open OriginalNecklaceHom

/-- The full original joint-coefficient diagram over the SAME native input category. -/
def fullCoefficientDiagram (K : SSet.{u}) (x y : K _⦋0⦌) : Object K x y ⥤ SSet.{u} :=
  forget K x y ⋙ fullCoefficientFunctor

/-- The SAME full original coefficient diagram evaluated in an arbitrary scalar degree. -/
def degreeCoefficient (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) : Object K x y ⥤ Type u :=
  fullCoefficientDiagram K x y ⋙ (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj q

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q r : SimplexCategoryᵒᵖ}

/-- Every original coefficient element retains its entire original flagged object. -/
def toFlaggedObject (E : (degreeCoefficient K x y q).Elements) : OriginalFlaggedNecklace.Object K x y q :=
  ⟨E.obj.necklace, E.obj.input, E.obj.source_eq, E.obj.target_eq, E.val.val, E.val.property⟩

/-- Every original full flagged object retains its SAME native input and coefficient element. -/
def fromFlaggedObject (T : OriginalFlaggedNecklace.Object K x y q) : (degreeCoefficient K x y q).Elements :=
  (degreeCoefficient K x y q).elementsMk
    ⟨T.necklace, T.input, T.source_eq, T.target_eq⟩ ⟨T.coefficient, T.joints⟩

/-- The actual full original coefficient elements functor to flagged necklaces. -/
def toFlaggedFunctor (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (degreeCoefficient K x y q).Elements ⥤ OriginalFlaggedNecklace.Object K x y q where
  obj := toFlaggedObject
  map f := ⟨f.hom.necklaceMap, f.hom.over, congrArg Subtype.val f.map_val⟩
  map_id _E := OriginalFlaggedNecklace.Hom.ext rfl
  map_comp _f _g := OriginalFlaggedNecklace.Hom.ext rfl

/-- The actual full original flagged functor to its SAME coefficient elements. -/
def fromFlaggedFunctor (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    OriginalFlaggedNecklace.Object K x y q ⥤ (degreeCoefficient K x y q).Elements where
  obj := fromFlaggedObject
  map f := Functor.Elements.homMk ⟨f.necklaceMap, f.over⟩ (Subtype.ext f.flags)
  map_id _T := Functor.Elements.hom_ext rfl
  map_comp _f _g := Functor.Elements.hom_ext rfl

/-- Both actual full original element functors compose to the SAME elements identity. -/
theorem toFlagged_fromFlagged (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    toFlaggedFunctor K x y q ⋙ fromFlaggedFunctor K x y q = 𝟭 (degreeCoefficient K x y q).Elements := by
  refine Functor.ext (fun E => ?_) ?_
  · cases E with
    | mk val =>
      cases val
      rfl
  · intro E F f
    apply Functor.Elements.hom_ext
    change f.hom = 𝟙 E.obj ≫ f.hom ≫ 𝟙 F.obj
    simp

/-- Both actual full original element functors compose to the SAME flagged identity. -/
theorem fromFlagged_toFlagged (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    fromFlaggedFunctor K x y q ⋙ toFlaggedFunctor K x y q = 𝟭 (OriginalFlaggedNecklace.Object K x y q) := by
  refine Functor.ext (fun T => ?_) ?_
  · cases T
    rfl
  · intro T U f
    apply OriginalFlaggedNecklace.Hom.ext
    change f.necklaceMap = 𝟙 T.necklace ≫ f.necklaceMap ≫ 𝟙 U.necklace
    simp

/-- Both full original inverse functors give the actual category isomorphism in each scalar degree. -/
def elementsCatIso (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Cat.of (degreeCoefficient K x y q).Elements ≅ Cat.of (OriginalFlaggedNecklace.Object K x y q) where
  hom := (toFlaggedFunctor K x y q).toCatHom
  inv := (fromFlaggedFunctor K x y q).toCatHom
  hom_inv_id := Cat.ext (toFlagged_fromFlagged K x y q)
  inv_hom_id := Cat.ext (fromFlagged_toFlagged K x y q)

/-- The entire original elements nerve is the SAME full original flagged-category nerve. -/
def elementsNerveIso (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    nerve (degreeCoefficient K x y q).Elements ≅ nerve (OriginalFlaggedNecklace.Object K x y q) :=
  CategoryTheory.nerveFunctor.mapIso (elementsCatIso K x y q)

/-- Every original scalar operator acts on the SAME full original coefficient elements. -/
def degreeCoefficientMap (K : SSet.{u}) (x y : K _⦋0⦌) (θ : q ⟶ r) :
    degreeCoefficient K x y q ⟶ degreeCoefficient K x y r where
  app T := (fullCoefficient T.necklace).map θ
  naturality T U f := by
    change (fullCoefficientMap f.necklaceMap).app q ≫ (fullCoefficient U.necklace).map θ =
      (fullCoefficient T.necklace).map θ ≫ (fullCoefficientMap f.necklaceMap).app r
    exact ((fullCoefficientMap f.necklaceMap).naturality θ).symm

/-- Every original scalar operator retains the SAME full coefficient-to-flagged functor square. -/
theorem toFlagged_scalar (K : SSet.{u}) (x y : K _⦋0⦌) (θ : q ⟶ r) :
    (degreeCoefficientMap K x y θ).mapElements ⋙ toFlaggedFunctor K x y r =
      toFlaggedFunctor K x y q ⋙ OriginalFlaggedNecklace.scalarFunctor K x y θ := by
  refine Functor.ext (fun _E => rfl) ?_
  intro E F f
  apply OriginalFlaggedNecklace.Hom.ext
  change f.hom.necklaceMap = 𝟙 E.obj.necklace ≫ f.hom.necklaceMap ≫ 𝟙 F.obj.necklace
  simp

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
