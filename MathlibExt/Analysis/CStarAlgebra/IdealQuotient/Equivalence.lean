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

public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Equality transport for actual closed-ideal quotients

Equality induction identifies the same canonical algebraic quotient structures.
The characteristic law retains the actual quotient projection. No new quotient
carrier, norm, instance, model or externally supplied equivalence is introduced.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped NonUnitalStarSubalgebra.Quotient

universe u

namespace ClosedStarIdeal

/-- **Quotient equivalence from ideal equality.** Let `D` be a nonunital complex C*-algebra and `I,J`
closed two-sided star ideals of `D`. An equality `I = J` defines a complex star-algebra equivalence
`D/I ≃ D/J`. -/
noncomputable def quotientStarAlgEquivOfEq
    {D : Type u} [NonUnitalCStarAlgebra D]
    (I J : ClosedStarIdeal D) (h : I = J) :
    letI : I.carrier.IsTwoSided := I.isTwoSided;
    letI : J.carrier.IsTwoSided := J.isTwoSided;
    I.Quotient ≃⋆ₐ[ℂ] J.Quotient := by
  subst J
  let : I.carrier.IsTwoSided := I.isTwoSided
  exact StarAlgEquiv.refl ℂ I.Quotient

/-- **Classes under ideal-equality transport.** Let `D` be a nonunital complex C*-algebra and `I,J`
closed two-sided star ideals of `D`. For an equality `I = J`, the induced quotient equivalence sends
the class of every `d ∈ D` modulo `I` to its class modulo `J`. -/
theorem quotientStarAlgEquivOfEq_quotientMap
    {D : Type u} [NonUnitalCStarAlgebra D]
    (I J : ClosedStarIdeal D) (h : I = J) :
    letI : I.carrier.IsTwoSided := I.isTwoSided;
    letI : J.carrier.IsTwoSided := J.isTwoSided;
    ∀ x : D, quotientStarAlgEquivOfEq I J h (I.quotientMap x) = J.quotientMap x := by
  subst J
  let : I.carrier.IsTwoSided := I.isTwoSided
  dsimp only
  intro x
  rfl

end ClosedStarIdeal
