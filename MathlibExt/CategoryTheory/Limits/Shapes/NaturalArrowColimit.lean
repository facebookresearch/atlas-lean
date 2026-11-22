/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The whole Arrow colimit of an actual natural transformation

Both endpoint cocones, descent maps, factor equations and uniqueness are
constructed from the original endpoint colimits in the same categories.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace CategoryTheory
section source_ProfileCellDecomposition_ArrowColimits
universe uj vj u v


open CategoryTheory Limits

variable {J : Type uj} [Category.{vj} J] {C : Type u} [Category.{v} C]
variable {A B : J ⥤ C} [HasColimit A] [HasColimit B]

/-- The original transformation gives its actual diagram of complete Arrow squares. -/
def naturalArrowFunctor (a : A ⟶ B) : J ⥤ Arrow C where
  obj j := Arrow.mk (a.app j)
  map f := Arrow.homMk (A.map f) (B.map f) (a.naturality f)
  map_id j := Arrow.hom_ext _ _ (A.map_id j) (B.map_id j)
  map_comp f g := Arrow.hom_ext _ _ (A.map_comp f g) (B.map_comp f g)

/-- The actual two original colimit projections form the original Arrow cofan. -/
def naturalArrowCocone (a : A ⟶ B) : Cocone (naturalArrowFunctor a) where
  pt := Arrow.mk (colimMap a)
  ι.app j := Arrow.homMk (colimit.ι A j) (colimit.ι B j) (ι_colimMap a j)
  ι.naturality j k f := by
    apply Arrow.hom_ext
    · exact (colimit.w A f).trans (Category.comp_id _).symm
    · exact (colimit.w B f).trans (Category.comp_id _).symm

/-- The left projections of a whole Arrow cocone form its actual source cocone. -/
def naturalArrowTargetLeft (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a)) : Cocone A where
  pt := c.pt.left
  ι.app j := (c.ι.app j).left
  ι.naturality _ _ f := (congrArg Arrow.Hom.left (c.w f)).trans (Category.comp_id _).symm

/-- The right projections of a whole Arrow cocone form its actual target cocone. -/
def naturalArrowTargetRight (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a)) : Cocone B where
  pt := c.pt.right
  ι.app j := (c.ι.app j).right
  ι.naturality _ _ f := (congrArg Arrow.Hom.right (c.w f)).trans (Category.comp_id _).symm

theorem naturalArrowDesc_square (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a)) :
    colimit.desc A (naturalArrowTargetLeft a c) ≫ c.pt.hom =
      colimMap a ≫ colimit.desc B (naturalArrowTargetRight a c) := by
  let l := colimit.desc A (naturalArrowTargetLeft a c)
  let r := colimit.desc B (naturalArrowTargetRight a c)
  apply colimit.hom_ext (F := A)
  intro j
  have hl : colimit.ι A j ≫ (l ≫ c.pt.hom) = (c.ι.app j).left ≫ c.pt.hom :=
    (Category.assoc _ l _).symm.trans
      (congrArg (· ≫ c.pt.hom) (colimit.ι_desc (naturalArrowTargetLeft a c) j))
  have hr : colimit.ι A j ≫ (colimMap a ≫ r) = a.app j ≫ (c.ι.app j).right :=
    (Category.assoc _ _ r).symm.trans
      ((congrArg (· ≫ r) (ι_colimMap a j)).trans
        ((Category.assoc _ _ r).trans
          (congrArg (a.app j ≫ ·) (colimit.ι_desc (naturalArrowTargetRight a c) j))))
  exact hl.trans ((c.ι.app j).w.trans hr.symm)

/-- Descend both original cocones through their actual colimit universal properties. -/
def naturalArrowDesc (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a)) :
    (naturalArrowCocone a).pt ⟶ c.pt :=
  Arrow.homMk (colimit.desc A (naturalArrowTargetLeft a c))
    (colimit.desc B (naturalArrowTargetRight a c)) (naturalArrowDesc_square a c)

theorem naturalArrowDesc_fac (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a)) (j : J) :
    (naturalArrowCocone a).ι.app j ≫ naturalArrowDesc a c = c.ι.app j := by
  apply Arrow.hom_ext
  · exact colimit.ι_desc (naturalArrowTargetLeft a c) j
  · exact colimit.ι_desc (naturalArrowTargetRight a c) j

theorem naturalArrowDesc_unique (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a))
    (m : (naturalArrowCocone a).pt ⟶ c.pt)
    (w : ∀ j, (naturalArrowCocone a).ι.app j ≫ m = c.ι.app j) : m = naturalArrowDesc a c := by
  apply Arrow.hom_ext
  · exact (colimit.isColimit A).uniq (naturalArrowTargetLeft a c) m.left
      (fun j => congrArg Arrow.Hom.left (w j))
  · exact (colimit.isColimit B).uniq (naturalArrowTargetRight a c) m.right
      (fun j => congrArg Arrow.Hom.right (w j))

/-- The complete actual Arrow colimit is constructed from the actual two
source diagram colimits, with full desc, both factors and whole uniqueness. -/
def naturalArrowIsColimit (a : A ⟶ B) : IsColimit (naturalArrowCocone a) where
  desc := naturalArrowDesc a
  fac := naturalArrowDesc_fac a
  uniq := naturalArrowDesc_unique a
end source_ProfileCellDecomposition_ArrowColimits

end CategoryTheory

namespace CategoryTheory

universe uj vj u v
variable {J : Type uj} [Category.{vj} J] {C : Type u} [Category.{v} C]

/-- A whole arrow of diagrams retains its component squares as a diagram of arrows. -/
def pointwiseArrowFunctor : Arrow (J ⥤ C) ⥤ J ⥤ Arrow C where
  obj p := naturalArrowFunctor p.hom
  map f :=
    { app j := Arrow.homMk (f.left.app j) (f.right.app j) (congr_app f.w j)
      naturality _ _ g := Arrow.hom_ext _ _ (f.left.naturality g) (f.right.naturality g) }
  map_id _ := by
    ext j <;> rfl
  map_comp _ _ := by
    ext j <;> rfl

end CategoryTheory
