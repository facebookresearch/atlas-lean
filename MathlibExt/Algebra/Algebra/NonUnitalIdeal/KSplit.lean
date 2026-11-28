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
# Linear decomposition along a split nonunital ideal

Let `I` be a two-sided nonunital subalgebra of a nonunital ring `A` over a commutative ring
`k`. A `k`-linear section `s : A/I → A` of the quotient map `q` determines the projection
`π(a) = a - s(q(a)) ∈ I`.

The maps `a ↦ (π(a), q(a))` and `(x, y) ↦ x + s(y)` are inverse `k`-linear maps, giving `I ×
(A/I) ≃ₗ[k] A`. This decomposition uses the module structure and the section equation.
-/

@[expose] public section

noncomputable section

universe u v

namespace NonUnitalSubalgebra.KSplit

variable {k : Type u} [CommRing k] {A : Type v} [NonUnitalRing A] [Module k A]
  {I : NonUnitalSubalgebra k A} [I.IsTwoSided] (s : I.KSplit)

/-- The ideal projection associated to a quotient section.

For `q : A → A/I` and a `k`-linear section `s`, the projection sends `a` to `a - s(q(a))`,
which belongs to `I` because `q ∘ s = id`. -/
def projection : A →ₗ[k] I.toSubmodule :=
  (LinearMap.id - s.sectionMap.comp I.quotientLinearMap).codRestrict I.toSubmodule (fun a => by
    apply (Submodule.Quotient.mk_eq_zero I.toSubmodule).mp
    change I.quotientLinearMap (a - s.sectionMap (I.quotientLinearMap a)) = 0
    rw [map_sub, s.quotient_section, sub_self])

omit [I.IsTwoSided] in
/-- The value of the split ideal projection.

The underlying element of `π(a) ∈ I` is `a - s(q(a))`. -/
@[simp]
theorem projection_val (a : A) :
    (s.projection a : A) = a - s.sectionMap (I.quotientLinearMap a) := rfl

omit [I.IsTwoSided] in
/-- The split projection on the ideal.

For `x ∈ I`, applying the projection to its value in `A` returns `x`. -/
@[simp]
theorem projection_subtype (x : I.toSubmodule) : s.projection x.val = x := by
  apply Subtype.ext
  rw [s.projection_val]
  have hx : I.quotientLinearMap x.val = 0 :=
    (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr x.property
  rw [hx, map_zero, sub_zero]

omit [I.IsTwoSided] in
/-- The split projection vanishes on the section image.

For a class `x ∈ A/I`, one has `π(s(x)) = 0`. -/
@[simp]
theorem projection_section (x : I.Quotient) : s.projection (s.sectionMap x) = 0 := by
  apply Subtype.ext
  rw [s.projection_val, s.quotient_section, sub_self]
  rfl

omit [I.IsTwoSided] in
/-- Reconstruction from ideal and quotient components.

For every `a ∈ A`, the inclusion of `π(a)` plus `s(q(a))` equals `a`. -/
theorem reconstruct (a : A) :
    (s.projection a : A) + s.sectionMap (I.quotientLinearMap a) = a := by
  rw [s.projection_val, sub_add_cancel]

/-- The component map of a split ideal sequence.

The `k`-linear map `A → I × (A/I)` sends `a` to `(π(a), q(a))`. -/
def toProduct : A →ₗ[k] I.toSubmodule × I.Quotient :=
  s.projection.prod I.quotientLinearMap

/-- The reconstruction map of a split ideal sequence.

The `k`-linear map `I × (A/I) → A` sends `(x, y)` to `x.val + s(y)`. -/
def fromProduct : I.toSubmodule × I.Quotient →ₗ[k] A :=
  I.toSubmodule.subtype.comp (LinearMap.fst k I.toSubmodule I.Quotient) +
    s.sectionMap.comp (LinearMap.snd k I.toSubmodule I.Quotient)

omit [I.IsTwoSided] in
/-- The formula for split ideal reconstruction.

For an ideal element `x` and quotient class `y`, the reconstruction map has value `x.val +
s(y)`. -/
@[simp]
theorem fromProduct_apply (x : I.toSubmodule) (q : I.Quotient) :
    s.fromProduct (x, q) = x.val + s.sectionMap q := rfl

/-- The linear product decomposition of a split ideal sequence.

A `k`-linear section of `A → A/I` gives `I × (A/I) ≃ₗ[k] A`, with forward map `(x, y) ↦ x.val
+ s(y)` and inverse `a ↦ (π(a), q(a))`. -/
def productEquiv : (I.toSubmodule × I.Quotient) ≃ₗ[k] A :=
  { s.fromProduct with
    invFun := s.toProduct
    left_inv := fun ⟨x, q⟩ => by
      apply Prod.ext
      · change s.projection (x.val + s.sectionMap q) = x
        rw [map_add, s.projection_subtype, s.projection_section, add_zero]
      · change I.quotientLinearMap (x.val + s.sectionMap q) = q
        have hx : I.quotientLinearMap x.val = 0 :=
          (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr x.property
        rw [map_add, hx, s.quotient_section, zero_add]
    right_inv := fun a => s.reconstruct a }

omit [I.IsTwoSided] in
/-- The forward formula for the split ideal equivalence.

The product equivalence sends `(x, y)` to `x.val + s(y)`. -/
@[simp]
theorem productEquiv_apply (x : I.toSubmodule) (q : I.Quotient) :
    s.productEquiv (x, q) = x.val + s.sectionMap q := rfl

omit [I.IsTwoSided] in
/-- The inverse formula for the split ideal equivalence.

The inverse product equivalence sends `a ∈ A` to `(π(a), q(a))`. -/
@[simp]
theorem productEquiv_symm_apply (a : A) :
    s.productEquiv.symm a = (s.projection a, I.quotientLinearMap a) := rfl

end NonUnitalSubalgebra.KSplit
