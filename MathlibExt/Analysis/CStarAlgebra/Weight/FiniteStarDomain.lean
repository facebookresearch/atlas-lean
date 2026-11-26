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

public import MathlibExt.Analysis.CStarAlgebra.Weight

/-!
# The star-invariant domain of two finite weight squares

For an extended positive weight `φ` on a nonunital complex C-star algebra `A`, put `D_φ = {x :
φ(x* x) < ∞ ∧ φ(x x*) < ∞}`. Taking adjoints exchanges the two finiteness conditions, so `x ↦
x*` is an involution of `D_φ`.

The carrier is a subtype of `A`; its involution is the restriction of the algebra involution.
Traciality, faithfulness and density of `φ` are not required for this star-invariant domain.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped NNReal ENNReal

namespace CStarAlgebra.ScalarWeight

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Adjoint reverses a positive square.** In a nonunital complex C-star algebra, the positive
element `(x*) (x*)*` is `x* x` for every `x`. -/
theorem rightSquare_star (x : A) : rightSquare (star x) = leftSquare x := by
  apply Subtype.ext
  simp only [rightSquare, leftSquare, star_star]

/-- **Domain of two finite weight squares.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. `finiteStarSquareDomain φ = {x : φ(x* x) < ∞ ∧ φ(x x*) < ∞}`. -/
def Weight.finiteStarSquareDomain (φ : Weight A) : Set A :=
  {x | φ.value (leftSquare x) < ⊤ ∧ φ.value (rightSquare x) < ⊤}

/-- **Star invariance of the two-square domain.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. `x* ∈ finiteStarSquareDomain φ ↔ x ∈ finiteStarSquareDomain φ`, since the
involution exchanges `x* x` and `x x*`. -/
theorem Weight.finiteStarSquareDomain_star_iff (φ : Weight A) (x : A) :
    star x ∈ φ.finiteStarSquareDomain ↔ x ∈ φ.finiteStarSquareDomain := by
  change φ.value (leftSquare (star x)) < ⊤ ∧ φ.value (rightSquare (star x)) < ⊤ ↔
    φ.value (leftSquare x) < ⊤ ∧ φ.value (rightSquare x) < ⊤
  rw [leftSquare_star, rightSquare_star, and_comm]

/-- **Carrier of the finite star domain.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. `FiniteStarSquareCarrier φ` is the subtype of elements `x : A` for which both `φ(x*
x)` and `φ(x x*)` are finite. -/
abbrev Weight.FiniteStarSquareCarrier (φ : Weight A) : Type u :=
  φ.finiteStarSquareDomain

/-- **Restricted involution of the finite star domain.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. on the subtype `{x : φ(x* x) < ∞ ∧ φ(x x*) < ∞}`, the star operation
sends `x` to the element represented by `x* : A`. -/
instance Weight.instStarFiniteStarSquareCarrier (φ : Weight A) : Star φ.FiniteStarSquareCarrier where
  star x := ⟨star (x : A), (φ.finiteStarSquareDomain_star_iff (x : A)).2 x.property⟩

/-- **Underlying element of the restricted adjoint.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. for `x : FiniteStarSquareCarrier φ`, coercing `star x` to `A` gives
the adjoint of the element underlying `x`. -/
@[simp]
theorem Weight.finiteStarSquareCarrier_star_coe (φ : Weight A) (x : φ.FiniteStarSquareCarrier) :
    ((star x : φ.FiniteStarSquareCarrier) : A) = star (x : A) :=
  rfl

/-- **Involutivity on the finite star domain.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. the restricted star operation on `{x : φ(x* x) < ∞ ∧ φ(x x*) < ∞}`
satisfies `star (star x) = x`. -/
instance Weight.instInvolutiveStarFiniteStarSquareCarrier (φ : Weight A) :
    InvolutiveStar φ.FiniteStarSquareCarrier where
  star_involutive x := by
    apply Subtype.ext
    change star (star (x : A)) = (x : A)
    exact star_star (x : A)

end CStarAlgebra.ScalarWeight
