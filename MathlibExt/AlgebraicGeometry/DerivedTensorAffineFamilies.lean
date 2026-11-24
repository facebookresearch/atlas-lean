/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
public import MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
public import Mathlib.Algebra.Category.CommAlgCat.Monoidal

/-!
# Actual tensor-product affine families

The index retains two actual algebras, a common simplex and a family
of each prestack. It maps to the product prestack using the native
algebra tensor inclusions. Both nonreduced coefficients and all simplex
maps remain. This is the source index for affine relative de Rham
projection and its full global descent.

Reference: PTVV arXiv:1111.3209v4, §2.1, pp.30–31.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedTensorAffineFamilies

open _root_.CategoryTheory _root_.Opposite _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- The literal simplicial algebra map a↦a⊗1. -/
def includeLeft (A B : SAlg k) : A ⟶ A ⊗ B where
  app n := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  naturality i j f := by
    ext a
    simp [CommAlgCat.tensorHom_hom]

/-- The literal simplicial algebra map b↦1⊗b. -/
def includeRight (A B : SAlg k) : B ⟶ A ⊗ B where
  app n := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  naturality i j f := by
    ext b
    simp [CommAlgCat.tensorHom_hom]

theorem includeLeft_natural {A B A' B' : SAlg k} (f : A ⟶ A') (g : B ⟶ B') :
    f ≫ includeLeft A' B' = includeLeft A B ≫ (f ⊗ₘ g) := by
  ext n a
  simp [includeLeft, CommAlgCat.tensorHom_hom]

theorem includeRight_natural {A B A' B' : SAlg k} (f : A ⟶ A') (g : B ⟶ B') :
    g ≫ includeRight A' B' = includeRight A B ≫ (f ⊗ₘ g) := by
  ext n b
  simp [includeRight, CommAlgCat.tensorHom_hom]

/-- The actual two-algebra simplex-valued family functor. -/
def pairPrestack (F X : Prestack k) : (SAlg k × SAlg k) ⥤ SSet.{u + 1} :=
  (_root_.CategoryTheory.Prod.fst _ _ ⋙ F) ⊗ (_root_.CategoryTheory.Prod.snd _ _ ⋙ X)

/-- Every tensor chart family and every actual algebra/simplex arrow. -/
abbrev TensorFamilies (F X : Prestack k) := (Functor.uncurry.obj (pairPrestack F X)).Elements

/-- The first actual family projection. -/
def first (F X : Prestack k) : TensorFamilies F X ⥤ Families F where
  obj j := family F j.obj.1.1 j.obj.2 j.val.1
  map f := ⟨(f.hom.1.1, f.hom.2), congrArg Prod.fst f.map_val⟩

/-- The second actual family projection. -/
def second (F X : Prestack k) : TensorFamilies F X ⥤ Families X where
  obj j := family X j.obj.1.2 j.obj.2 j.val.2
  map f := ⟨(f.hom.1.2, f.hom.2), congrArg Prod.snd f.map_val⟩

/-- The product chart carries exactly the two native tensor-inclusion pullbacks. -/
def productFamilies (F X : Prestack k) :
    pairPrestack F X ⟶ tensor (SAlg k) ⋙ (F ⊗ X) where
  app AB := F.map (includeLeft AB.1 AB.2) ⊗ₘ X.map (includeRight AB.1 AB.2)
  naturality AB CD f := by
    change (F.map f.1 ⊗ₘ X.map f.2) ≫
      (F.map (includeLeft CD.1 CD.2) ⊗ₘ X.map (includeRight CD.1 CD.2)) =
      (F.map (includeLeft AB.1 AB.2) ⊗ₘ X.map (includeRight AB.1 AB.2)) ≫
        (F.map (f.1 ⊗ₘ f.2) ⊗ₘ X.map (f.1 ⊗ₘ f.2))
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      ← F.map_comp, ← X.map_comp, ← F.map_comp, ← X.map_comp,
      includeLeft_natural, includeRight_natural]

/-- Native category-of-elements maps produce the full product chart reindexing. -/
def product (F X : Prestack k) : TensorFamilies F X ⥤ Families (F ⊗ X) :=
  (Functor.uncurry.map (productFamilies F X)).mapElements ⋙
    Functor.Elements.precomp
      ((tensor (SAlg k)).prod (𝟭 SimplexCategoryᵒᵖ)) (uncurried (F ⊗ X))

/-- The affine augmentation is retained in every X-family simplex. -/
def affineTensor (Q : AlgebraReplacementFunctor k) (A : SAlg k) (X : Prestack k) :
    Families X ⥤ TensorFamilies (affineMapping k Q A) X where
  obj j := (Functor.uncurry.obj (pairPrestack (affineMapping k Q A) X)).elementsMk
    ((A, j.obj.1), j.obj.2) (ULift.up (affineAugmentationSimplex Q A j.obj.2), j.val)
  map f :=
    { hom := ((𝟙 A, f.hom.1), f.hom.2)
      map_val := by
        apply Prod.ext
        · simp [pairPrestack, affineMapping, affineAugmentationSimplex,
            liftSimplicial, derivedSpecFunctor]
          rfl
        · exact f.map_val }

/-- The actual affine-product chart functor uses the literal Q augmentation. -/
def affineProduct (Q : AlgebraReplacementFunctor k) (A : SAlg k) (X : Prestack k) :
    Families X ⥤ Families (affineMapping k Q A ⊗ X) :=
  affineTensor Q A X ⋙ product (affineMapping k Q A) X

end MathlibExt.AlgebraicGeometry.DerivedTensorAffineFamilies
