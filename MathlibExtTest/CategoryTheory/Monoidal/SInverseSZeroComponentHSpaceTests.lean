/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentHSpace

/-! # Tests for the additive S⁻¹S zero-component weak H-space -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits ZeroObject

universe w u

namespace MathlibExtTest.SInverseSZeroComponentHSpace

open CategoryTheory.SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example : zeroComponentClassifyingSpace.{w} C :=
  zeroComponentBasepoint.{w} C

example :
    zeroComponentClassifyingSpace.{w} C ⨯
        zeroComponentClassifyingSpace.{w} C ⟶
      zeroComponentClassifyingSpace.{w} C :=
  zeroComponentClassifyingSpaceMul.{w} C

example :
    Path
      (zeroComponentClassifyingSpaceMul.{w} C
        (CGWH.prodPoint _ _
          (zeroComponentBasepoint.{w} C)
          (zeroComponentBasepoint.{w} C)))
      (zeroComponentBasepoint.{w} C) :=
  zeroComponentClassifyingSpaceRootPath.{w} C

example :
    CGWH.WeakHSpaceData (zeroComponentClassifyingSpace.{w} C) :=
  zeroComponentClassifyingSpaceWeakHSpaceData.{w} C

example :
    (zeroComponentClassifyingSpaceWeakHSpaceData.{w} C).mul =
      zeroComponentClassifyingSpaceMul.{w} C := by
  simp

example :
    (zeroComponentClassifyingSpaceWeakHSpaceData.{w} C).e =
      zeroComponentBasepoint.{w} C := by
  simp

example :
    (zeroComponentClassifyingSpaceWeakHSpaceData.{w} C).rootPath =
      zeroComponentClassifyingSpaceRootPath.{w} C := by
  simp

/-- The root path starts at the realized coordinatewise `0 ⊞ 0` pair
vertex. -/
example :
    zeroComponentClassifyingSpaceRootPath.{w} C 0 =
      classifyingSpaceCGWHPoint.{w}
        ((zeroComponentBiprodFunctor (C := C)).obj
          (zeroComponentBaseObject (C := C),
            zeroComponentBaseObject (C := C))) :=
  (zeroComponentClassifyingSpaceRootPath.{w} C).source.trans
    (zeroComponentClassifyingSpaceMul_basepoint.{w} C)

/-- The same forward path ends at the selected zero vertex. -/
example :
    zeroComponentClassifyingSpaceRootPath.{w} C 1 =
      zeroComponentBasepoint.{w} C :=
  (zeroComponentClassifyingSpaceRootPath.{w} C).target

example :
    ((zeroComponentBiprodFunctor (C := C)).obj
      (zeroComponentBaseObject (C := C),
        zeroComponentBaseObject (C := C))).obj =
      pairBiprodObj
        (zeroComponentBaseObject (C := C)).obj
        (zeroComponentBaseObject (C := C)).obj :=
  zeroComponentBiprodFunctor_obj_obj _

/-- The specialization does not identify the `0 ⊞ 0` object with the
selected zero object definitionally. -/
example : True := by
  fail_if_success
    exact (rfl :
      (zeroComponentBiprodFunctor (C := C)).obj
          (zeroComponentBaseObject (C := C),
            zeroComponentBaseObject (C := C)) =
        zeroComponentBaseObject (C := C))
  trivial

example (p q : FundamentalGroup
    (CGWH.cgwhToTop.obj (zeroComponentClassifyingSpace.{w} C))
    (zeroComponentBasepoint.{w} C)) :
    p * q = q * p :=
  zeroComponentClassifyingSpace_fundamentalGroup_mul_comm.{w} C p q

example : True := by
  fail_if_success
    let _ := inferInstanceAs (CommGroup (FundamentalGroup
      (CGWH.cgwhToTop.obj (zeroComponentClassifyingSpace.{w} C))
      (zeroComponentBasepoint.{w} C)))
  trivial

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
    CGWH.WeakHSpaceData
      (zeroComponentClassifyingSpace.{0} ZeroCategory) :=
  zeroComponentClassifyingSpaceWeakHSpaceData.{0} ZeroCategory

example (p q : FundamentalGroup
    (CGWH.cgwhToTop.obj
      (zeroComponentClassifyingSpace.{0} ZeroCategory))
    (zeroComponentBasepoint.{0} ZeroCategory)) :
    p * q = q * p :=
  zeroComponentClassifyingSpace_fundamentalGroup_mul_comm.{0}
    ZeroCategory p q

/-- The category remains small while only the native CGWH carrier universe is
raised. -/
example :
    CGWH.WeakHSpaceData
      (zeroComponentClassifyingSpace.{1} ZeroCategory) :=
  zeroComponentClassifyingSpaceWeakHSpaceData.{1} ZeroCategory

example (p q : FundamentalGroup
    (CGWH.cgwhToTop.obj
      (zeroComponentClassifyingSpace.{1} ZeroCategory))
    (zeroComponentBasepoint.{1} ZeroCategory)) :
    p * q = q * p :=
  zeroComponentClassifyingSpace_fundamentalGroup_mul_comm.{1}
    ZeroCategory p q

#print axioms zeroComponentBasepoint
#print axioms zeroComponentClassifyingSpaceMul
#print axioms zeroComponentClassifyingSpaceRootPath
#print axioms zeroComponentClassifyingSpaceMul_prodPoint
#print axioms zeroComponentClassifyingSpaceMul_basepoint
#print axioms zeroComponentClassifyingSpaceWeakHSpaceData
#print axioms zeroComponentClassifyingSpaceWeakHSpaceData_mul
#print axioms zeroComponentClassifyingSpaceWeakHSpaceData_e
#print axioms zeroComponentClassifyingSpaceWeakHSpaceData_rootPath
#print axioms zeroComponentClassifyingSpace_fundamentalGroup_mul_comm

end MathlibExtTest.SInverseSZeroComponentHSpace

end
