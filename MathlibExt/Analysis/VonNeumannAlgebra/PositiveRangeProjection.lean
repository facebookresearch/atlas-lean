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

public import MathlibExt.Analysis.VonNeumannAlgebra.Basic
public import MathlibExt.Analysis.VonNeumannAlgebra.RangeProjection
public import MathlibExt.Analysis.InnerProductSpace.ClosedRangeProjection
public import MathlibExt.Analysis.CStarAlgebra.Weight
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The actual support projection of an original positive operator

The stock orthogonal projection onto the closure of the original positive
operator's range belongs to the same concrete von Neumann algebra. Every
original commutant operator and its adjoint preserve that closed range and
its orthogonal complement, hence commute with its original projection.
Double-commutant membership supplies the actual algebra element.

This is the support DATA needed for positive cutoff/local domination in
an actual order-normal/predual construction. No source projection, normal
functional, predual certificate or desired representation model is input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original positive operator's generic closed-range projection is an actual algebra element. -/
def positiveRangeProjection (M : VonNeumannAlgebra H) (a : PositiveElement M) : M :=
  ⟨ContinuousLinearMap.closedRangeProjection ((a : M) : H →L[ℂ] H),
    closedRangeProjection_mem M ((a : M) : H →L[ℂ] H) (a : M).property⟩

/-- The constructed algebra element is exactly the stock projection onto the original closed range. -/
theorem positiveRangeProjection_coe (M : VonNeumannAlgebra H) (a : PositiveElement M) :
    (positiveRangeProjection M a : H →L[ℂ] H) =
      (LinearMap.range ((a : M) : H →L[ℂ] H).toLinearMap).topologicalClosure.starProjection :=
  rfl

/-- The same original closed-range projection is a genuine star projection. -/
theorem positiveRangeProjection_isStarProjection (M : VonNeumannAlgebra H) (a : PositiveElement M) :
    IsStarProjection (positiveRangeProjection M a : H →L[ℂ] H) := by
  rw [positiveRangeProjection_coe]
  exact isStarProjection_starProjection

/-- Its actual operator range is precisely the original operator's closed range. -/
theorem positiveRangeProjection_range (M : VonNeumannAlgebra H) (a : PositiveElement M) :
    (positiveRangeProjection M a : H →L[ℂ] H).range =
      (LinearMap.range ((a : M) : H →L[ℂ] H).toLinearMap).topologicalClosure := by
  rw [positiveRangeProjection_coe]
  exact Submodule.range_starProjection _

/-- The actual original support projection fixes the original positive operator. -/
theorem positiveRangeProjection_mul_self (M : VonNeumannAlgebra H) (a : PositiveElement M) :
    positiveRangeProjection M a * (a : M) = (a : M) := by
  apply Subtype.ext
  change ContinuousLinearMap.closedRangeProjection ((a : M) : H →L[ℂ] H) *
    ((a : M) : H →L[ℂ] H) = ((a : M) : H →L[ℂ] H)
  exact ContinuousLinearMap.closedRangeProjection_mul_self _

/-- An original operator annihilating a positive operator annihilates its actual support. -/
theorem mul_positiveRangeProjection_eq_zero (M : VonNeumannAlgebra H) (a : PositiveElement M)
    (b : M) (hba : b * (a : M) = 0) : b * positiveRangeProjection M a = 0 := by
  have hBT : (b : H →L[ℂ] H).comp ((a : M) : H →L[ℂ] H) = 0 := by
    change (b : H →L[ℂ] H) * ((a : M) : H →L[ℂ] H) = 0
    exact congrArg (fun x : M => (x : H →L[ℂ] H)) hba
  apply Subtype.ext
  change (b : H →L[ℂ] H).comp
    (ContinuousLinearMap.closedRangeProjection ((a : M) : H →L[ℂ] H)) = 0
  exact ContinuousLinearMap.comp_closedRangeProjection_eq_zero _ _ hBT

end

end VonNeumannAlgebra
