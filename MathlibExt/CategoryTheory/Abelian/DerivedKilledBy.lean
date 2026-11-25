/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Preadditive.KilledBy
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Additive
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Additive

/-!
# Integer torsion and derived functors

Additive left- and right-derived functors preserve the condition that an
integer kills an object. The corresponding integer also kills morphisms
from or into that derived object.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Preadditive
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Every degree of the left derived functor preserves the coefficient torsion. -/
theorem leftDerived_obj_isKilledBy [HasProjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    {X : C} {m : ℕ} (hX : IsKilledBy X m) (n : ℕ) :
    IsKilledBy ((F.leftDerived n).obj X) m :=
  hX.map (F.leftDerived n)

/-- Every degree of the right derived functor preserves the coefficient torsion. -/
theorem rightDerived_obj_isKilledBy [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    {X : C} {m : ℕ} (hX : IsKilledBy X m) (n : ℕ) :
    IsKilledBy ((F.rightDerived n).obj X) m :=
  hX.map (F.rightDerived n)

/-- Derived coefficient arrows are killed by the source object's torsion. -/
theorem rightDerived_map_nsmul_eq_zero [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    {X Y : C} {m : ℕ} (hX : IsKilledBy X m) (f : X ⟶ Y) (n : ℕ) :
    m • (F.rightDerived n).map f = 0 :=
  (F.rightDerived_obj_isKilledBy hX n).nsmul_hom_source _

/-- Derived coefficient natural transformations retain the object-level torsion. -/
theorem rightDerived_transformation_neg_eq_self [HasInjectiveResolutions C]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (α : F ⟶ G)
    {X : C} (hX : IsKilledBy X 2) (n : ℕ) :
    -(NatTrans.rightDerived α n).app X = (NatTrans.rightDerived α n).app X :=
  (F.rightDerived_obj_isKilledBy hX n).neg_hom_source _

end CategoryTheory.Functor
