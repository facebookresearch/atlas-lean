/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.LiftingProperties.LeibnizPushoutMaps
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The canonical Leibniz corner in the original model-category source frame

These names retain the original source arrows and chosen pushout projections.
The entire object/map construction is the existing `NatTrans.leibnizPushout`
functor; no second pushout functor is constructed.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.NaturalTransformationCorner

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C] [HasPushouts C]
  {P Q : D ⥤ C} (α : P ⟶ Q)

/-- The original domain is the chosen domain of the canonical Leibniz corner. -/
abbrev domain (g : Arrow D) : C := pushout (α.app g.left) (P.map g.hom)

/-- The source carrier is the literal chosen domain of the canonical corner. -/
theorem domain_eq_canonical (g : Arrow D) :
    domain α g = ((NatTrans.leibnizPushout α).obj g).left :=
  (NatTrans.leibnizPushout_obj_left α g).symm

/-- The original corner map is the canonical Leibniz pushout component. -/
abbrev corner (g : Arrow D) : domain α g ⟶ Q.obj g.right :=
  ((NatTrans.leibnizPushout α).obj g).hom

/-- The first original projection retains the actual target-functor arrow. -/
theorem inl_corner (g : Arrow D) :
    pushout.inl (α.app g.left) (P.map g.hom) ≫ corner α g = Q.map g.hom :=
  pushout.inl_desc _ _ _

/-- The second original projection retains the actual transformation component. -/
theorem inr_corner (g : Arrow D) :
    pushout.inr (α.app g.left) (P.map g.hom) ≫ corner α g = α.app g.right :=
  pushout.inr_desc _ _ _

/-- The original whole corner Arrow is the canonical functor's object. -/
abbrev object (g : Arrow D) : Arrow C := (NatTrans.leibnizPushout α).obj g

/-- The source-square domain map is the canonical corner square's left map. -/
abbrev domainMap {g h : Arrow D} (f : g ⟶ h) : domain α g ⟶ domain α h :=
  ((NatTrans.leibnizPushout α).map f).left

/-- The first original projection retains the source square's left leg. -/
theorem domainMap_inl {g h : Arrow D} (f : g ⟶ h) :
    pushout.inl (α.app g.left) (P.map g.hom) ≫ domainMap α f =
      Q.map f.left ≫ pushout.inl (α.app h.left) (P.map h.hom) :=
  NatTrans.leibnizPushout_map_left_inl α f

/-- The second original projection retains the source square's right leg. -/
theorem domainMap_inr {g h : Arrow D} (f : g ⟶ h) :
    pushout.inr (α.app g.left) (P.map g.hom) ≫ domainMap α f =
      P.map f.right ≫ pushout.inr (α.app h.left) (P.map h.hom) :=
  NatTrans.leibnizPushout_map_left_inr α f

/-- The complete canonical corner square commutes on both original endpoints. -/
theorem map_square {g h : Arrow D} (f : g ⟶ h) :
    domainMap α f ≫ corner α h = corner α g ≫ Q.map f.right :=
  ((NatTrans.leibnizPushout α).map f).w

/-- Every original whole source square uses the canonical Leibniz pushout map. -/
abbrev map {g h : Arrow D} (f : g ⟶ h) : object α g ⟶ object α h :=
  (NatTrans.leibnizPushout α).map f

/-- The original corner functor is the existing canonical Leibniz pushout functor. -/
abbrev functor : Arrow D ⥤ Arrow C := NatTrans.leibnizPushout α

/-- The public source functor retains the entire canonical object/map construction. -/
theorem functor_eq_leibnizPushout : functor α = NatTrans.leibnizPushout α := rfl

end HomotopicalAlgebra.NaturalTransformationCorner
