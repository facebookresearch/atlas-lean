/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.PointedCGWH
public import MathlibExt.KTheory.Ring.StableGeneralLinear.Basic
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.CategoryTheory.SingleObj

/-!
# Classifying space of the algebraic stable general linear group

For a semiring `R`, this file defines the algebraic stable-`GL` classifying
space as the native CGWH realization of the nerve of the opposite
single-object category of `StableGL R`.

The opposite is intentional. In Mathlib's `SingleObj`, categorical
composition is reversed multiplication; using `(StableGL R)ᵐᵒᵖ` matches the
orientation of the standard classifying bar construction. Ring maps act
through the existing functoriality of `StableGL`, and the selected unique
object gives a strictly functorial PointedCGWH refinement.

This is the unmodified `BGL(R)` input to Quillen's plus construction. No plus
construction, group-completion theorem, or comparison with Quillen `Q` is
claimed here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicKTheory
namespace StableGL

/-- The opposite stable general linear group, functorial in the semiring. -/
noncomputable def oppositeMonoidFunctor : SemiRingCat.{u} ⥤ MonCat.{u} where
  obj R := MonCat.of (StableGL (R : Type u))ᵐᵒᵖ
  map {R S} f := MonCat.ofHom (MonoidHom.op (StableGL.functor.map f).hom)
  map_id R := by
    apply MonCat.hom_ext
    ext g
    change MulOpposite.op
        ((StableGL.functor.map (𝟙 R)).hom (MulOpposite.unop g)) = g
    rw [StableGL.functor.map_id]
    exact MulOpposite.op_unop g
  map_comp {R S T} f g := by
    apply MonCat.hom_ext
    ext x
    change MulOpposite.op
        ((StableGL.functor.map (f ≫ g)).hom (MulOpposite.unop x)) =
      MulOpposite.op
        ((StableGL.functor.map g).hom
          ((StableGL.functor.map f).hom (MulOpposite.unop x)))
    rw [StableGL.functor.map_comp]
    rfl

/-- The one-object category whose endomorphism group is the opposite stable
general linear group. -/
abbrev ClassifyingCategory (R : Type u) [Semiring R] :=
  SingleObj (StableGL R)ᵐᵒᵖ

@[simp]
theorem classifyingCategory_eqToHom
    (R : Type u) [Semiring R]
    {X Y : ClassifyingCategory R} (h : X = Y) :
    (eqToHom h : X ⟶ Y) = (1 : (StableGL R)ᵐᵒᵖ) := by
  subst h
  rfl

@[simp]
theorem classifyingCategory_id_as_one
    (R : Type u) [Semiring R] (X : ClassifyingCategory R) :
    (𝟙 X : X ⟶ X) = (1 : (StableGL R)ᵐᵒᵖ) :=
  rfl

theorem classifyingCategory_comp_as_mul
    (R : Type u) [Semiring R]
    {X Y Z : ClassifyingCategory R}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g =
      (show (StableGL R)ᵐᵒᵖ from g) *
        (show (StableGL R)ᵐᵒᵖ from f) :=
  rfl

/-- The stable-`GL` single-object category, functorial in the semiring. -/
noncomputable def classifyingCategoryFunctor : SemiRingCat.{u} ⥤ Cat.{u, 0} :=
  oppositeMonoidFunctor ⋙ MonCat.toCat

/-- The canonical functor on stable-`GL` single-object categories induced by
a semiring homomorphism. -/
noncomputable def classifyingCategoryMap {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) : ClassifyingCategory R ⥤ ClassifyingCategory S :=
  SingleObj.mapHom _ _
    (MonoidHom.op (StableGL.functor.map (SemiRingCat.ofHom f)).hom)

@[simp]
theorem classifyingCategoryMap_obj {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) (X : ClassifyingCategory R) :
    (classifyingCategoryMap f).obj X = X :=
  rfl

@[simp]
theorem classifyingCategoryMap_map {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) {X Y : ClassifyingCategory R} (g : X ⟶ Y) :
    (classifyingCategoryMap f).map g =
      MulOpposite.op
        ((StableGL.functor.map (SemiRingCat.ofHom f)).hom
          (MulOpposite.unop g)) :=
  rfl

@[simp]
theorem classifyingCategoryMap_id (R : Type u) [Semiring R] :
    classifyingCategoryMap (RingHom.id R) = 𝟭 (ClassifyingCategory R) := by
  have hMap :
      (StableGL.functor.map
        (SemiRingCat.ofHom (RingHom.id R))).hom =
        MonoidHom.id (StableGL R) := by
    have h : SemiRingCat.ofHom (RingHom.id R) =
        𝟙 (SemiRingCat.of R) := rfl
    rw [h, StableGL.functor.map_id]
    rfl
  unfold classifyingCategoryMap
  rw [hMap]
  have hOp : MonoidHom.op (MonoidHom.id (StableGL R)) =
      MonoidHom.id (StableGL R)ᵐᵒᵖ := by
    ext g
    rfl
  rw [hOp, SingleObj.mapHom_id]

@[simp]
theorem classifyingCategoryMap_comp {R S T : Type u}
    [Semiring R] [Semiring S] [Semiring T]
    (f : R →+* S) (g : S →+* T) :
    classifyingCategoryMap (g.comp f) =
      classifyingCategoryMap f ⋙ classifyingCategoryMap g := by
  have hMap :
      (StableGL.functor.map
        (SemiRingCat.ofHom (g.comp f))).hom =
        (StableGL.functor.map (SemiRingCat.ofHom g)).hom.comp
          (StableGL.functor.map (SemiRingCat.ofHom f)).hom := by
    have h : SemiRingCat.ofHom (g.comp f) =
        SemiRingCat.ofHom f ≫ SemiRingCat.ofHom g := rfl
    rw [h, StableGL.functor.map_comp]
    rfl
  unfold classifyingCategoryMap
  rw [hMap]
  have hOp :
      MonoidHom.op
          ((StableGL.functor.map (SemiRingCat.ofHom g)).hom.comp
            (StableGL.functor.map (SemiRingCat.ofHom f)).hom) =
        (MonoidHom.op
          (StableGL.functor.map (SemiRingCat.ofHom g)).hom).comp
          (MonoidHom.op
            (StableGL.functor.map (SemiRingCat.ofHom f)).hom) := by
    ext x
    rfl
  rw [hOp, SingleObj.mapHom_comp]

/-- A finite matrix, regarded as a loop in the stable-`GL` single-object
category. -/
def finiteClassifyingArrow {R : Type u} [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (SingleObj.star (StableGL R)ᵐᵒᵖ) ⟶
      SingleObj.star (StableGL R)ᵐᵒᵖ :=
  MulOpposite.op (StableGL.of g)

@[simp]
theorem classifyingCategoryMap_map_of {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (classifyingCategoryMap f).map
        (finiteClassifyingArrow g) =
      finiteClassifyingArrow
        (Matrix.GeneralLinearGroup.mapRingHom f g) := by
  unfold finiteClassifyingArrow
  rw [classifyingCategoryMap_map, MulOpposite.unop_op, StableGL.map_of]

/-- The algebraic stable general linear classifying space `BGL(R)` in CGWH. -/
noncomputable def BGL (R : Type u) [Semiring R] : CGWH.{w, u} :=
  CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.obj
    (Cat.of (ClassifyingCategory R))

/-- The classifying-space map induced by a semiring homomorphism. -/
noncomputable def BGLMap {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) : BGL.{w} R ⟶ BGL.{w} S :=
  CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
    (classifyingCategoryMap f).toCatHom

@[simp]
theorem BGLMap_id (R : Type u) [Semiring R] :
    BGLMap.{w} (RingHom.id R) = 𝟙 (BGL.{w} R) := by
  change CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
      (classifyingCategoryMap (RingHom.id R)).toCatHom =
    𝟙 (CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.obj
      (Cat.of (ClassifyingCategory R)))
  rw [classifyingCategoryMap_id]
  exact CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map_id _

@[simp]
theorem BGLMap_comp {R S T : Type u}
    [Semiring R] [Semiring S] [Semiring T]
    (f : R →+* S) (g : S →+* T) :
    BGLMap.{w} (g.comp f) = BGLMap.{w} f ≫ BGLMap.{w} g := by
  change CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
      (classifyingCategoryMap (g.comp f)).toCatHom =
    CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
        (classifyingCategoryMap f).toCatHom ≫
      CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
        (classifyingCategoryMap g).toCatHom
  rw [classifyingCategoryMap_comp]
  change CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
      ((classifyingCategoryMap f).toCatHom ≫
        (classifyingCategoryMap g).toCatHom) = _
  exact CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map_comp _ _

/-- The unique object supplies the canonical basepoint of algebraic `BGL`. -/
noncomputable def pointedBGL (R : Type u) [Semiring R] : PointedCGWH.{w, u} :=
  CategoryTheory.classifyingSpaceCGWHPointed.{w}
    (SingleObj.star (StableGL R)ᵐᵒᵖ)

/-- The classifying-space map induced by a semiring homomorphism, as a
strictly pointed CGWH map. -/
noncomputable def pointedBGLMap {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) : pointedBGL.{w} R ⟶ pointedBGL.{w} S :=
  Under.homMk (BGLMap.{w} f) (by
    exact CategoryTheory.classifyingSpaceCGWH_basepointMap_naturality
      (classifyingCategoryMap f)
      (SingleObj.star (StableGL R)ᵐᵒᵖ))

@[simp]
theorem pointedBGLMap_right {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) :
    (pointedBGLMap.{w} f).right = BGLMap.{w} f :=
  rfl

@[simp]
theorem pointedBGLMap_id (R : Type u) [Semiring R] :
    pointedBGLMap.{w} (RingHom.id R) = 𝟙 (pointedBGL.{w} R) := by
  apply Under.UnderMorphism.ext
  exact BGLMap_id R

@[simp]
theorem pointedBGLMap_comp {R S T : Type u}
    [Semiring R] [Semiring S] [Semiring T]
    (f : R →+* S) (g : S →+* T) :
    pointedBGLMap.{w} (g.comp f) =
      pointedBGLMap.{w} f ≫ pointedBGLMap.{w} g := by
  apply Under.UnderMorphism.ext
  exact BGLMap_comp f g

end StableGL
end AlgebraicKTheory

end
