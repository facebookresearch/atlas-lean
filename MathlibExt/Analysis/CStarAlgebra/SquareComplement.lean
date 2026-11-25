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

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# The computed norm-square complement in a C-star algebra

The positive CFC square root of the norm-square scalar minus the adjoint
square supplies an actual complement. It also remains in any commutant
containing both the original element and its adjoint. No nonzero-algebra or
supplied square-complement premise is needed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarAlgebra

universe u

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- **Square complement of an adjoint product.** Let `D` be a unital complex C*-algebra with a
star-compatible partial order and `a ∈ D`. Its norm-square complement is the positive
continuous-functional-calculus square root `b = √(‖a‖² 1 - a* a)`. This defines the complement
element `b ∈ D`. -/
def normSquareComplement (a : D) : D :=
  CFC.sqrt (algebraMap ℝ D (‖a‖ ^ 2) - star a * a)

/-- **Positivity of the square complement.** Let `D` be a unital complex C*-algebra with a
star-compatible partial order and `a ∈ D`. Its norm-square complement is the positive
continuous-functional-calculus square root `b = √(‖a‖² 1 - a* a)`. The complement element `b` is
positive. -/
theorem normSquareComplement_nonneg (a : D) : 0 ≤ normSquareComplement a :=
  CFC.sqrt_nonneg _

/-- **Adjoint square and complement square.** Let `D` be a unital complex C*-algebra with a
star-compatible partial order and `a ∈ D`. Its norm-square complement is the positive
continuous-functional-calculus square root `b = √(‖a‖² 1 - a* a)`. The identity `a* a + b* b = ‖a‖²
1` holds in `D`. -/
theorem star_mul_self_add_normSquareComplement (a : D) :
    star a * a + star (normSquareComplement a) * normSquareComplement a =
      algebraMap ℝ D (‖a‖ ^ 2) := by
  have hd : 0 ≤ algebraMap ℝ D (‖a‖ ^ 2) - star a * a :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq a)
  have hSquare : star (normSquareComplement a) * normSquareComplement a =
      algebraMap ℝ D (‖a‖ ^ 2) - star a * a := by
    rw [(normSquareComplement_nonneg a).star_eq]
    exact CFC.sqrt_mul_sqrt_self _ hd
  rw [add_comm (star a * a) _, hSquare]
  exact sub_add_cancel _ _

/-- **Commutant of the square complement.** Let `D` be a unital complex C*-algebra with a
star-compatible partial order and `a ∈ D`. Its norm-square complement is the positive
continuous-functional-calculus square root `b = √(‖a‖² 1 - a* a)`. If an element `c ∈ D` commutes
with both `a` and `a*`, it commutes with the complement `b`. -/
theorem normSquareComplement_commute (a b : D)
    (hab : Commute a b) (hstarab : Commute (star a) b) :
    Commute (normSquareComplement a) b := by
  have hSquare : Commute (star a * a) b := hstarab.mul_left hab
  have hd : Commute (algebraMap ℝ D (‖a‖ ^ 2) - star a * a) b :=
    (Algebra.commute_algebraMap_left (‖a‖ ^ 2) b).sub_left hSquare
  simpa only [normSquareComplement, CFC.sqrt] using hd.cfcₙ_nnreal NNReal.sqrt

end CStarAlgebra
