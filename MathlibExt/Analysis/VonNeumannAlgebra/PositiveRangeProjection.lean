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
# Support projection of a positive von Neumann operator

For positive `a` in a concrete von Neumann algebra `M ⊆ B(H)`, the support `s(a)` is the
orthogonal projection onto `closure(range a)`. It belongs to `M`, satisfies `s(a)²=s(a)`,
`s(a)*=s(a)`, and `s(a)a=a`.

If `b∈M` satisfies `ba=0`, then `b s(a)=0`. The Hilbert space is complete; zero positive
elements and zero spaces are allowed.
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

/-- **Support projection as an element of the von Neumann algebra.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a ∈ M`
in its spectral order, let `s(a)` be the projection onto `closure(range a)`.
`positiveRangeProjection M a=s(a)` is an element of `M`, with the inherited operator norm. -/
def positiveRangeProjection (M : VonNeumannAlgebra H) (a : PositiveElement M) : M :=
  ⟨ContinuousLinearMap.closedRangeProjection ((a : M) : H →L[ℂ] H),
    closedRangeProjection_mem M ((a : M) : H →L[ℂ] H) (a : M).property⟩

/-- **Operator formula of a positive support projection.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a ∈ M` in its
spectral order, let `s(a)` be the projection onto `closure(range a)`. the operator
underlying `positiveRangeProjection M a` is the star projection of the closed submodule
`closure(range a)`. -/
theorem positiveRangeProjection_coe (M : VonNeumannAlgebra H) (a : PositiveElement M) :
    (positiveRangeProjection M a : H →L[ℂ] H) =
      (LinearMap.range ((a : M) : H →L[ℂ] H).toLinearMap).topologicalClosure.starProjection :=
  rfl

/-- **Star projection equations for a positive support.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a ∈ M` in its
spectral order, let `s(a)` be the projection onto `closure(range a)`. `s(a)²=s(a)` and
`s(a)*=s(a)`. -/
theorem positiveRangeProjection_isStarProjection (M : VonNeumannAlgebra H) (a : PositiveElement M) :
    IsStarProjection (positiveRangeProjection M a : H →L[ℂ] H) := by
  rw [positiveRangeProjection_coe]
  exact isStarProjection_starProjection

/-- **Range of the positive support projection.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a ∈ M` in its spectral order,
let `s(a)` be the projection onto `closure(range a)`. `range(s(a))=closure(range a)`. -/
theorem positiveRangeProjection_range (M : VonNeumannAlgebra H) (a : PositiveElement M) :
    (positiveRangeProjection M a : H →L[ℂ] H).range =
      (LinearMap.range ((a : M) : H →L[ℂ] H).toLinearMap).topologicalClosure := by
  rw [positiveRangeProjection_coe]
  exact Submodule.range_starProjection _

/-- **Support projection fixes its positive operator.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a ∈ M` in its spectral
order, let `s(a)` be the projection onto `closure(range a)`. `s(a)a=a` in `M`. -/
theorem positiveRangeProjection_mul_self (M : VonNeumannAlgebra H) (a : PositiveElement M) :
    positiveRangeProjection M a * (a : M) = (a : M) := by
  apply Subtype.ext
  change ContinuousLinearMap.closedRangeProjection ((a : M) : H →L[ℂ] H) *
    ((a : M) : H →L[ℂ] H) = ((a : M) : H →L[ℂ] H)
  exact ContinuousLinearMap.closedRangeProjection_mul_self _

/-- **Annihilation of a positive operator passes to its support.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a ∈ M`
in its spectral order, let `s(a)` be the projection onto `closure(range a)`. if `b∈M`
satisfies `ba=0`, then `b s(a)=0`. -/
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
