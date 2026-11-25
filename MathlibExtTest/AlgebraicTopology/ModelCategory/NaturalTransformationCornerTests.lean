/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

import MathlibExt.AlgebraicTopology.ModelCategory.NaturalTransformationCorner

/-!
# Public natural-transformation corner clients

The two original pushout legs and every Arrow square remain visible through
the corner interface, with independent source and target category universes.
-/

set_option autoImplicit false
noncomputable section

universe uC vC uD vD

open CategoryTheory Limits
open HomotopicalAlgebra.NaturalTransformationCorner

namespace MathlibExtTest.NaturalCorner

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C] [HasPushouts C]
  {P Q : D ⥤ C} (α : P ⟶ Q)

example (g : Arrow D) : ((functor α).obj g).left = pushout (α.app g.left) (P.map g.hom) :=
  rfl

example (g : Arrow D) : ((functor α).obj g).hom = corner α g := rfl

example (g : Arrow D) :
    pushout.inl (α.app g.left) (P.map g.hom) ≫ corner α g = Q.map g.hom :=
  inl_corner α g

example (g : Arrow D) :
    pushout.inr (α.app g.left) (P.map g.hom) ≫ corner α g = α.app g.right :=
  inr_corner α g

example {g h : Arrow D} (f : g ⟶ h) :
    pushout.inl (α.app g.left) (P.map g.hom) ≫ domainMap α f =
      Q.map f.left ≫ pushout.inl (α.app h.left) (P.map h.hom) :=
  domainMap_inl α f

example {g h : Arrow D} (f : g ⟶ h) :
    pushout.inr (α.app g.left) (P.map g.hom) ≫ domainMap α f =
      P.map f.right ≫ pushout.inr (α.app h.left) (P.map h.hom) :=
  domainMap_inr α f

example {g h : Arrow D} (f : g ⟶ h) :
    domainMap α f ≫ corner α h = corner α g ≫ Q.map f.right :=
  map_square α f

example {g h i : Arrow D} (f : g ⟶ h) (f' : h ⟶ i) :
    (functor α).map (f ≫ f') = (functor α).map f ≫ (functor α).map f' :=
  (functor α).map_comp f f'

end MathlibExtTest.NaturalCorner
