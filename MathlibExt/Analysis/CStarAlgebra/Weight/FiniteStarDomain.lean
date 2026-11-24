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
# The literal two-square-finite domain of a global weight

The two-square-finite domain of a global scalar weight consists of the
original elements x for which both phi(x*x) and phi(xx*) are finite. This
module constructs that actual set and its inherited involution. It supplies
the domain carrier needed by the later weight left-Hilbert-algebra statement.

The original ambient norm is not the weight norm. Addition, multiplication,
weight inner products, completion and Tomita closure are not asserted here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped NNReal ENNReal

namespace CStarAlgebra.ScalarWeight

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Taking star exchanges the original right square and left square. -/
theorem rightSquare_star (x : A) : rightSquare (star x) = leftSquare x := by
  apply Subtype.ext
  simp only [rightSquare, leftSquare, star_star]

/-- The actual core is finite for both original positive squares. -/
def Weight.finiteStarSquareDomain (φ : Weight A) : Set A :=
  {x | φ.value (leftSquare x) < ⊤ ∧ φ.value (rightSquare x) < ⊤}

/-- The two original finite-square conditions are exchanged by star. -/
theorem Weight.finiteStarSquareDomain_star_iff (φ : Weight A) (x : A) :
    star x ∈ φ.finiteStarSquareDomain ↔ x ∈ φ.finiteStarSquareDomain := by
  change φ.value (leftSquare (star x)) < ⊤ ∧ φ.value (rightSquare (star x)) < ⊤ ↔
    φ.value (leftSquare x) < ⊤ ∧ φ.value (rightSquare x) < ⊤
  rw [leftSquare_star, rightSquare_star, and_comm]

/-- The original elements satisfying both finite-square conditions, without an asserted weight norm. -/
abbrev Weight.FiniteStarSquareCarrier (φ : Weight A) : Type u :=
  φ.finiteStarSquareDomain

/-- The actual involution retains the original ambient algebra element. -/
instance Weight.instStarFiniteStarSquareCarrier (φ : Weight A) : Star φ.FiniteStarSquareCarrier where
  star x := ⟨star (x : A), (φ.finiteStarSquareDomain_star_iff (x : A)).2 x.property⟩

/-- The inherited carrier involution has exactly the original algebra values. -/
@[simp]
theorem Weight.finiteStarSquareCarrier_star_coe (φ : Weight A) (x : φ.FiniteStarSquareCarrier) :
    ((star x : φ.FiniteStarSquareCarrier) : A) = star (x : A) :=
  rfl

/-- The actual domain involution squares to the identity by the original star law. -/
instance Weight.instInvolutiveStarFiniteStarSquareCarrier (φ : Weight A) :
    InvolutiveStar φ.FiniteStarSquareCarrier where
  star_involutive x := by
    apply Subtype.ext
    change star (star (x : A)) = (x : A)
    exact star_star (x : A)

end CStarAlgebra.ScalarWeight
