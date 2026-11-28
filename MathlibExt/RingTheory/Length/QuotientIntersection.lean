/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Length

/-!
# Actual quotient intersections and finite module length

The quotient of an original closed-support quotient by the image of a
second ideal is the quotient by the original sum of ideals. The actual
surjective quotient map constructs the comparison, and its module length
is preserved along the original quotient algebra map.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Let `R` be a commutative ring and `I`, `J` ideals. If `R/(I+J)` has
finite composition length as an `R`-module, then the double quotient of
`R/I` by the image of `J` has finite length as an `R/I`-module. The double
quotient and the sum-ideal quotient are the given quotient rings. -/
theorem quotientMapIdeal_length_ne_top (I J : Ideal R)
    (h : Module.length R (R ⧸ (I ⊔ J)) ≠ ⊤) :
    Module.length (R ⧸ I) ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≠ ⊤ := by
  rw [← Module.length_eq_of_surjective (R := R ⧸ I) (S := R)
    (M := ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))) Ideal.Quotient.mk_surjective]
  change Module.length R ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mkₐ R I)) ≠ ⊤
  rw [(DoubleQuot.quotQuotEquivQuotSupₐ R I J).toLinearEquiv.length_eq]
  exact h

end Ideal
