/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentRealization

/-! # Tests for realization of the additive S⁻¹S zero component -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits ZeroObject

universe w v u

namespace MathlibExtTest.SInverseSZeroComponentRealization

open CategoryTheory.SInverseS

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check zeroComponentClassifyingSpaceComponentIso
#check zeroComponentClassifyingSpaceComponentIso_hom_comp_inclusion
#check zeroComponentClassifyingSpaceComponentTopIso
#check zeroComponentClassifyingSpaceComponentTopIso_hom_comp_inclusion
#check zeroComponentClassifyingSpaceComponentRealizationTopIso

example :
    zeroComponentClassifyingSpace.{w} C ≅
      SSet.toCGWH.{w, max u v}.obj
        (zeroComponentNerveComponent C : SSet) :=
  zeroComponentClassifyingSpaceComponentIso.{w} C

example :
    zeroComponentClassifyingSpaceComponentIso.{w} C =
      SSet.toCGWH.{w, max u v}.mapIso (zeroComponentNerveIso C) :=
  rfl

example :
    (zeroComponentClassifyingSpaceComponentIso.{w} C).hom ≫
        SSet.toCGWH.{w, max u v}.map
          (zeroComponentNerveComponent C).ι =
      zeroComponentClassifyingSpaceInclusion.{w} C :=
  zeroComponentClassifyingSpaceComponentIso_hom_comp_inclusion.{w} C

example :
    CGWH.cgwhToTop.obj (zeroComponentClassifyingSpace.{w} C) ≅
      CGWH.cgwhToTop.obj
        (SSet.toCGWH.{w, max u v}.obj
          (zeroComponentNerveComponent C : SSet)) :=
  zeroComponentClassifyingSpaceComponentTopIso.{w} C

example :
    (zeroComponentClassifyingSpaceComponentTopIso.{w} C).hom ≫
        CGWH.cgwhToTop.{w, max u v}.map
          (SSet.toCGWH.{w, max u v}.map
            (zeroComponentNerveComponent C).ι) =
      CGWH.cgwhToTop.{w, max u v}.map
        (zeroComponentClassifyingSpaceInclusion.{w} C) :=
  zeroComponentClassifyingSpaceComponentTopIso_hom_comp_inclusion.{w} C

example :
    CGWH.cgwhToTop.obj (zeroComponentClassifyingSpace.{w} C) ≅
      SSet.toTop.obj (zeroComponentNerveComponent C : SSet) :=
  zeroComponentClassifyingSpaceComponentRealizationTopIso.{w} C

-- Universe-polymorphic surface checks.
#check @zeroComponentClassifyingSpaceComponentIso.{0, 0, 0}
#check @zeroComponentClassifyingSpaceComponentIso.{1, 0, 0}
#check @zeroComponentClassifyingSpaceComponentIso.{0, 1, 1}
#check @zeroComponentClassifyingSpaceComponentRealizationTopIso.{1, 1, 1}

private abbrev ZeroCategory := SingleObj (ZMod 1)

private instance (X Y : ZeroCategory) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ZMod 1))

private instance : HasZeroObject ZeroCategory where
  zero :=
    ⟨SingleObj.star (ZMod 1),
      (IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _)⟩

private instance : HasBinaryBiproducts ZeroCategory where
  has_binary_biproduct X Y := by
    apply hasBinaryBiproduct_of_total
      { pt := SingleObj.star (ZMod 1)
        fst := 0
        snd := 0
        inl := 0
        inr := 0
        inl_fst := Subsingleton.elim _ _
        inl_snd := Subsingleton.elim _ _
        inr_fst := Subsingleton.elim _ _
        inr_snd := Subsingleton.elim _ _ }
    exact Subsingleton.elim _ _

example :
    zeroComponentClassifyingSpace.{0} ZeroCategory ≅
      SSet.toCGWH.{0, 0}.obj
        (zeroComponentNerveComponent ZeroCategory : SSet) :=
  zeroComponentClassifyingSpaceComponentIso.{0} ZeroCategory

example :
    (zeroComponentClassifyingSpaceComponentIso.{0} ZeroCategory).hom ≫
        SSet.toCGWH.{0, 0}.map
          (zeroComponentNerveComponent ZeroCategory).ι =
      zeroComponentClassifyingSpaceInclusion.{0} ZeroCategory :=
  zeroComponentClassifyingSpaceComponentIso_hom_comp_inclusion.{0}
    ZeroCategory

#print axioms zeroComponentClassifyingSpaceComponentIso
#print axioms zeroComponentClassifyingSpaceComponentIso_hom_comp_inclusion
#print axioms zeroComponentClassifyingSpaceComponentTopIso
#print axioms zeroComponentClassifyingSpaceComponentTopIso_hom_comp_inclusion
#print axioms zeroComponentClassifyingSpaceComponentRealizationTopIso

end MathlibExtTest.SInverseSZeroComponentRealization

end
