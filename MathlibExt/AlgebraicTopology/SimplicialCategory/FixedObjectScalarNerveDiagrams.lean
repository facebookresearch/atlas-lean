/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectScalarCategories
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderNerveSourceMaps
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# The SAME original fixed-label scalar nerve diagrams

Every native scalar category uses the actual original fixed labels and
entire original Hom simplices. Full canonical ScalarObject coordinates
have inverse functors retaining every original Hom. Both original scalar
operators and enriched maps give the same full native nerve diagrams.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.SimplicialEnrichment.FixedObjects
variable {O : Type u}

/-- The SAME fixed-label scalar category bundled at the specified native degree. -/
def scalarCat (C : FixedObjects O) (q : SimplexCategoryᵒᵖ) : Cat.{u,u} :=
  @Cat.of O (scalarCategory C q)

/-- The entire original fixed-label scalar functor uses the SAME full Hom map. -/
def scalarCatMap {C D : FixedObjects O} (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) : scalarCat C q ⟶ scalarCat D q :=
  @CategoryTheory.Functor.toCatHom O O (scalarCategory C q) (scalarCategory D q) (scalarFunctor F q)

/-- The original canonical scalar wrappers map to their SAME actual original labels and Homs. -/
def scalarToLabels (C : FixedObjects O) (q : SimplexCategoryᵒᵖ) : SSet.ScalarObject C.val q ⥤ scalarCat C q where
  obj a := label C a.obj
  map {a b} f := (originalHomIso C a.obj b.obj).hom.app q f
  map_id a := by
    exact congr($(identity_originalHomIso C a.obj).app q PUnit.unit)
  map_comp {a b c} f g := by
    exact congr($(composition_originalHomIso C a.obj b.obj c.obj).app q (f,g))

/-- The SAME original labels restore the native scalar wrapper while retaining full Hom simplices. -/
def labelsToScalar (C : FixedObjects O) (q : SimplexCategoryᵒᵖ) : scalarCat C q ⥤ SSet.ScalarObject C.val q where
  obj x := SSet.ScalarObject.mk (vertex C x)
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual label-to-scalar functor is faithful on every SAME original Hom simplex. -/
instance labelsToScalar_faithful (C : FixedObjects O) (q : SimplexCategoryᵒᵖ) :
    (labelsToScalar C q).Faithful where
  map_injective {_x _y} _f _g h := h

/-- The actual label-to-scalar functor is full on every SAME original Hom simplex. -/
instance labelsToScalar_full (C : FixedObjects O) (q : SimplexCategoryᵒᵖ) :
    (labelsToScalar C q).Full where
  map_surjective f := ⟨f,rfl⟩

/-- Every actual canonical scalar object is the SAME original labelled vertex. -/
instance labelsToScalar_essSurj (C : FixedObjects O) (q : SimplexCategoryᵒᵖ) :
    (labelsToScalar C q).EssSurj where
  mem_essImage a := ⟨label C a.obj, ⟨eqToIso
    (congrArg (SSet.ScalarObject.mk (Δ := q)) (vertex_label C a.obj))⟩⟩

/-- The SAME full actual original scalar label functor is a genuine equivalence. -/
instance labelsToScalar_isEquivalence (C : FixedObjects O) (q : SimplexCategoryᵒᵖ) :
    (labelsToScalar C q).IsEquivalence where

/-- The SAME original fixed-label scalar categories are equivalent to the native canonical wrappers. -/
def labelsScalarEquivalence (C : FixedObjects O) (q : SimplexCategoryᵒᵖ) : scalarCat C q ≌ SSet.ScalarObject C.val q :=
  (labelsToScalar C q).asEquivalence

/-- The entire original scalar label diagram retains every native ordinal operator. -/
def scalarCatDiagram (C : FixedObjects O) : SimplexCategoryᵒᵖ ⥤ Cat.{u,u} where
  obj := scalarCat C
  map f := @CategoryTheory.Functor.toCatHom O O (scalarCategory C _) (scalarCategory C _) (scalarOperator C f)
  map_id q := by
    apply Cat.ext
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun x y a =>
      heq_of_eq (Functor.map_id_apply (hom C x y) q a))
  map_comp f g := by
    apply Cat.ext
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun x y a =>
      heq_of_eq (Functor.map_comp_apply (hom C x y) f g a))

/-- The SAME full original fixed-label scalar nerve diagram. -/
def scalarLabelNerveDiagram (C : FixedObjects O) : SimplicialObject SSet.{u} := scalarCatDiagram C ⋙ nerveFunctor

/-- The SAME actual original fixed-label scalar nerve diagonal. -/
def scalarLabelBase (C : FixedObjects O) : SSet.{u} := SSet.simplicialDiagonalFunctor.obj (scalarLabelNerveDiagram C)

end CategoryTheory.SimplicialEnrichment.FixedObjects
