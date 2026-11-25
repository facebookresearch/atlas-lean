/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Algebra.NonUnitalIdeal
public import Mathlib.LinearAlgebra.Prod

/-!
# Original linear coordinates of a k-split nonunital ideal extension

The actual section of the actual quotient determines the original kernel
projection a minus section(q(a)). Native module-quotient exactness puts this
value in the original ideal. The resulting product linear equivalence is
constructed from these actual maps. No algebra splitting or desired Iso is
an input.
-/

@[expose] public section

noncomputable section

universe u v

namespace NonUnitalSubalgebra.KSplit

variable {k : Type u} [CommRing k] {A : Type v} [NonUnitalRing A] [Module k A]
  {I : NonUnitalSubalgebra k A} [I.IsTwoSided] (s : I.KSplit)

/-- The original section and quotient determine the actual ideal component. -/
def projection : A →ₗ[k] I.toSubmodule :=
  (LinearMap.id - s.sectionMap.comp I.quotientLinearMap).codRestrict I.toSubmodule (fun a => by
    apply (Submodule.Quotient.mk_eq_zero I.toSubmodule).mp
    change I.quotientLinearMap (a - s.sectionMap (I.quotientLinearMap a)) = 0
    rw [map_sub, s.quotient_section, sub_self])

omit [I.IsTwoSided] in
@[simp]
theorem projection_val (a : A) :
    (s.projection a : A) = a - s.sectionMap (I.quotientLinearMap a) := rfl

omit [I.IsTwoSided] in
/-- The actual ideal projection is identity on the original ideal inclusion. -/
@[simp]
theorem projection_subtype (x : I.toSubmodule) : s.projection x.val = x := by
  apply Subtype.ext
  rw [s.projection_val]
  have hx : I.quotientLinearMap x.val = 0 := (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr x.property
  rw [hx, map_zero, sub_zero]

omit [I.IsTwoSided] in
/-- The original section has zero ideal coordinate. -/
@[simp]
theorem projection_section (x : I.Quotient) : s.projection (s.sectionMap x) = 0 := by
  apply Subtype.ext
  rw [s.projection_val, s.quotient_section, sub_self]
  rfl

omit [I.IsTwoSided] in
/-- The actual ideal and quotient coordinates reconstruct every original ambient element. -/
theorem reconstruct (a : A) :
    (s.projection a : A) + s.sectionMap (I.quotientLinearMap a) = a := by
  rw [s.projection_val, sub_add_cancel]

/-- Both original coordinate maps enter the actual product module. -/
def toProduct : A →ₗ[k] I.toSubmodule × I.Quotient :=
  s.projection.prod I.quotientLinearMap

/-- The actual ideal inclusion and actual source section reconstruct the ambient module. -/
def fromProduct : I.toSubmodule × I.Quotient →ₗ[k] A :=
  I.toSubmodule.subtype.comp (LinearMap.fst k I.toSubmodule I.Quotient) +
    s.sectionMap.comp (LinearMap.snd k I.toSubmodule I.Quotient)

omit [I.IsTwoSided] in
@[simp]
theorem fromProduct_apply (x : I.toSubmodule) (q : I.Quotient) :
    s.fromProduct (x, q) = x.val + s.sectionMap q := rfl

/-- The source k-module splitting is the earned product equivalence of the original maps. -/
def productEquiv : (I.toSubmodule × I.Quotient) ≃ₗ[k] A :=
  { s.fromProduct with
    invFun := s.toProduct
    left_inv := fun ⟨x, q⟩ => by
      apply Prod.ext
      · change s.projection (x.val + s.sectionMap q) = x
        rw [map_add, s.projection_subtype, s.projection_section, add_zero]
      · change I.quotientLinearMap (x.val + s.sectionMap q) = q
        have hx : I.quotientLinearMap x.val = 0 := (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr x.property
        rw [map_add, hx, s.quotient_section, zero_add]
    right_inv := fun a => s.reconstruct a }

omit [I.IsTwoSided] in
/-- The earned source coordinates keep the exact original ideal inclusion and section. -/
@[simp]
theorem productEquiv_apply (x : I.toSubmodule) (q : I.Quotient) :
    s.productEquiv (x, q) = x.val + s.sectionMap q := rfl

omit [I.IsTwoSided] in
/-- The inverse keeps the exact original quotient map and the earned original ideal component. -/
@[simp]
theorem productEquiv_symm_apply (a : A) :
    s.productEquiv.symm a = (s.projection a, I.quotientLinearMap a) := rfl

end NonUnitalSubalgebra.KSplit
