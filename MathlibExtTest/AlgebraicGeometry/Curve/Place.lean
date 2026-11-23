/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.Place

@[expose] public section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

-- `exactSource` consumer with the original binders.
example {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f :=
  v.ord_nonneg_of_mem hf

example {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring :=
  v.mem_of_ord_nonneg hf h

example {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  v.mem_iff_ord_nonneg hf

-- Boundary: zero is in the subring although the iff needs `f ≠ 0`, and the
-- inverse of a uniformizer has negative order, so it is outside.
example : (0 : F) ∈ v.toValuationSubring := zero_mem _

example {π : v.toValuationSubring} (hπ : Irreducible π) :
    v.ord ((π : F)⁻¹) = -1 := by
  rw [v.ord_inv, v.ord_coe_irreducible hπ]

example {π : v.toValuationSubring} (hπ : Irreducible π) :
    (π : F)⁻¹ ∉ v.toValuationSubring := by
  intro hmem
  have h := v.ord_nonneg_of_mem hmem
  rw [v.ord_inv, v.ord_coe_irreducible hπ] at h
  omega

end AlgebraicCurve
