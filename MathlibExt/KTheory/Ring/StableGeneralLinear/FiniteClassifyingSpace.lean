/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpaceFundamentalGroup

/-!
# Finite general-linear classifying spaces and stabilization

For a semiring `R`, the finite general linear groups form the existing
`ℕ`-indexed diagram `finiteGLDiagram.obj (SemiRingCat.of R)`. This file sends
that diagram through opposite single-object categories and native CGWH
classifying spaces. It also constructs the coherent finite-stage maps to
stable algebraic `BGL(R)`.

These are the diagrammatic inputs for the mapping telescope in the
group-completion/plus-construction comparison. No colimit, telescope, plus
construction, or `Q`-construction equivalence is claimed here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe w u

namespace AlgebraicKTheory
namespace StableGL

/-- The finite `GL` diagram with every group replaced by its opposite
monoid. -/
noncomputable def finiteOppositeMonoidDiagram
    (R : Type u) [Semiring R] : ℕ ⥤ MonCat.{u} where
  obj n := MonCat.of
    (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ
  map {n m} f := MonCat.ofHom
    (MonoidHom.op
      ((finiteGLDiagram.obj (SemiRingCat.of R)).map f).hom)
  map_id n := by
    apply MonCat.hom_ext
    ext g
    change MulOpposite.op
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map (𝟙 n)
          (MulOpposite.unop g)) = g
    rw [(finiteGLDiagram.obj (SemiRingCat.of R)).map_id]
    exact MulOpposite.op_unop g
  map_comp {n m k} f g := by
    apply MonCat.hom_ext
    ext x
    change MulOpposite.op
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map (f ≫ g)
          (MulOpposite.unop x)) =
      MulOpposite.op
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map g
          ((finiteGLDiagram.obj (SemiRingCat.of R)).map f
            (MulOpposite.unop x)))
    rw [(finiteGLDiagram.obj (SemiRingCat.of R)).map_comp]
    rfl

@[simp]
theorem finiteOppositeMonoidDiagram_obj
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteOppositeMonoidDiagram R).obj n =
      MonCat.of
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ :=
  rfl

@[simp]
theorem finiteOppositeMonoidDiagram_map_apply
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (finiteOppositeMonoidDiagram R).map f g =
      MulOpposite.op
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map f
          (MulOpposite.unop g)) :=
  rfl

/-- The `ℕ`-indexed diagram of finite stable-`GL` one-object categories. -/
noncomputable def finiteClassifyingCategoryDiagram
    (R : Type u) [Semiring R] : ℕ ⥤ Cat.{u, 0} :=
  finiteOppositeMonoidDiagram R ⋙ MonCat.toCat

@[simp]
theorem finiteClassifyingCategoryDiagram_obj
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteClassifyingCategoryDiagram R).obj n =
      Cat.of (SingleObj
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :=
  rfl

@[simp]
theorem finiteClassifyingCategoryDiagram_map_toFunctor
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    ((finiteClassifyingCategoryDiagram R).map f).toFunctor =
      SingleObj.mapHom _ _
        (MonoidHom.op
          ((finiteGLDiagram.obj (SemiRingCat.of R)).map f).hom) :=
  rfl

@[simp]
theorem finiteClassifyingCategoryDiagram_map_obj
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m)
    (X : (finiteClassifyingCategoryDiagram R).obj n) :
    ((finiteClassifyingCategoryDiagram R).map f).toFunctor.obj X = X :=
  rfl

@[simp]
theorem finiteClassifyingCategoryDiagram_map_map
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m)
    {X Y : (finiteClassifyingCategoryDiagram R).obj n}
    (g : X ⟶ Y) :
    ((finiteClassifyingCategoryDiagram R).map f).toFunctor.map g =
      MulOpposite.op
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map f
          (MulOpposite.unop g)) :=
  rfl

/-- Equality transports in a finite one-object classifying category are the
identity group element. -/
@[simp]
theorem finiteClassifyingCategoryDiagram_eqToHom
    (R : Type u) [Semiring R] {n : ℕ}
    {X Y : (finiteClassifyingCategoryDiagram R).obj n}
    (h : X = Y) :
    (eqToHom h : X ⟶ Y) =
      (1 : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) := by
  subst h
  rfl

@[simp]
theorem finiteClassifyingCategoryDiagram_id_as_one
    (R : Type u) [Semiring R] {n : ℕ}
    (X : (finiteClassifyingCategoryDiagram R).obj n) :
    (𝟙 X : X ⟶ X) =
      (1 : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :=
  rfl

theorem finiteClassifyingCategoryDiagram_comp_as_mul
    (R : Type u) [Semiring R] {n : ℕ}
    {X Y Z : (finiteClassifyingCategoryDiagram R).obj n}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g =
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from g) *
        (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from f) :=
  rfl

/-- The canonical CGWH diagram `n ↦ BGLₙ(R)`. -/
noncomputable def finiteBGLDiagram
    (R : Type u) [Semiring R] : ℕ ⥤ CGWH.{w, u} :=
  finiteClassifyingCategoryDiagram R ⋙
    CategoryTheory.classifyingSpaceCGWH.{w, u, 0}

/-- The finite algebraic classifying space `BGLₙ(R)` in CGWH. -/
noncomputable abbrev FiniteBGL
    (R : Type u) [Semiring R] (n : ℕ) : CGWH.{w, u} :=
  (finiteBGLDiagram.{w} R).obj n

/-- The canonical pointed-CGWH diagram `n ↦ BGLₙ(R)`. -/
noncomputable def finitePointedBGLDiagram
    (R : Type u) [Semiring R] : ℕ ⥤ PointedCGWH.{w, u} where
  obj n := CategoryTheory.classifyingSpaceCGWHPointed.{w}
    (SingleObj.star
      (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
  map {n m} f := Under.homMk
    ((finiteBGLDiagram.{w} R).map f) (by
      exact CategoryTheory.classifyingSpaceCGWH_basepointMap_naturality
        ((finiteClassifyingCategoryDiagram R).map f).toFunctor
        (SingleObj.star
          (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))
  map_id n := by
    apply Under.UnderMorphism.ext
    exact (finiteBGLDiagram.{w} R).map_id n
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact (finiteBGLDiagram.{w} R).map_comp f g

/-- The finite algebraic classifying space `BGLₙ(R)` with its canonical
basepoint. -/
noncomputable abbrev pointedFiniteBGL
    (R : Type u) [Semiring R] (n : ℕ) : PointedCGWH.{w, u} :=
  (finitePointedBGLDiagram.{w} R).obj n

/-- The canonical functor from the `n`th finite-`GL` single-object category
to the stable-`GL` single-object category. -/
noncomputable def finiteToStableCategoryMap
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteClassifyingCategoryDiagram R).obj n ⟶
      Cat.of (ClassifyingCategory R) :=
  (SingleObj.mapHom _ _
    (MonoidHom.op
      ((StableGL.inclusion n).app (SemiRingCat.of R)).hom)).toCatHom

/-- The finite-to-stable functors form a cocone on the finite classifying
category diagram. -/
theorem finiteToStableCategoryMap_naturality
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    (finiteClassifyingCategoryDiagram R).map f ≫
        finiteToStableCategoryMap R m =
      finiteToStableCategoryMap R n := by
  apply Cat.Hom.ext
  change ((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
      (finiteToStableCategoryMap R m).toFunctor =
    (finiteToStableCategoryMap R n).toFunctor
  let hObj : ∀ X,
      ((((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
        (finiteToStableCategoryMap R m).toFunctor).obj X) =
        ((finiteToStableCategoryMap R n).toFunctor.obj X) := fun _ => rfl
  refine CategoryTheory.Functor.ext hObj ?_
  intro X Y g
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (hObj X) (hObj Y)).2
  have hι :=
    (GrpCat.FilteredColimits.colimitCocone
      (F := finiteGLDiagram.obj (SemiRingCat.of R))).ι.naturality f
  simp only [Functor.const_obj_map] at hι
  have hιHom := congrArg GrpCat.Hom.hom hι
  have hιApply := DFunLike.congr_fun hιHom (MulOpposite.unop g)
  exact heq_of_eq (congrArg MulOpposite.op hιApply)

/-- The canonical finite-stage map `BGLₙ(R) → BGL(R)` in CGWH. -/
noncomputable def finiteBGLToBGL
    (R : Type u) [Semiring R] (n : ℕ) :
    FiniteBGL.{w} R n ⟶ BGL.{w} R :=
  CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
    (finiteToStableCategoryMap R n)

/-- The finite-stage maps to stable `BGL` are compatible with every diagram
transition. -/
theorem finiteBGLToBGL_naturality
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    (finiteBGLDiagram.{w} R).map f ≫ finiteBGLToBGL.{w} R m =
      finiteBGLToBGL.{w} R n := by
  change CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
        ((finiteClassifyingCategoryDiagram R).map f) ≫
      CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
        (finiteToStableCategoryMap R m) =
    CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
      (finiteToStableCategoryMap R n)
  rw [← CategoryTheory.classifyingSpaceCGWH.map_comp]
  exact congrArg
    (CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map)
    (finiteToStableCategoryMap_naturality R f)

/-- The canonical finite-stage map to stable `BGL`, as a strictly pointed
CGWH map. -/
noncomputable def pointedFiniteBGLToBGL
    (R : Type u) [Semiring R] (n : ℕ) :
    pointedFiniteBGL.{w} R n ⟶ pointedBGL.{w} R :=
  Under.homMk (finiteBGLToBGL.{w} R n) (by
    exact CategoryTheory.classifyingSpaceCGWH_basepointMap_naturality
      (finiteToStableCategoryMap R n).toFunctor
      (SingleObj.star
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))

/-- Pointed finite-stage maps are compatible with stabilization. -/
theorem pointedFiniteBGLToBGL_naturality
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    (finitePointedBGLDiagram.{w} R).map f ≫
        pointedFiniteBGLToBGL.{w} R m =
      pointedFiniteBGLToBGL.{w} R n := by
  apply Under.UnderMorphism.ext
  exact finiteBGLToBGL_naturality R f

end StableGL
end AlgebraicKTheory

end
