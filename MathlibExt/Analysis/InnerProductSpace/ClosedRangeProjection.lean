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

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The canonical closed-range projection of a Hilbert-space operator

The orthogonal projection is computed on the actual closure of the original
operator range. No closed-range, positivity, algebra-membership or projection
certificate is an input. Textbook and concrete von Neumann consumers share
this single generic construction and its literal stock range contracts.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ContinuousLinearMap

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The orthogonal projection onto the actual closure of the operator's range. -/
def closedRangeProjection (T : H →L[ℂ] H) : H →L[ℂ] H :=
  T.range.topologicalClosure.starProjection

/-- The canonical closed-range projection is the original stock star projection. -/
theorem closedRangeProjection_eq_starProjection (T : H →L[ℂ] H) :
    closedRangeProjection T = T.range.topologicalClosure.starProjection :=
  rfl

/-- The constructed closed-range operator is a genuine star projection. -/
theorem isStarProjection_closedRangeProjection (T : H →L[ℂ] H) :
    IsStarProjection (closedRangeProjection T) :=
  isStarProjection_starProjection

/-- Its actual operator range equals the closure of the original range. -/
theorem range_closedRangeProjection (T : H →L[ℂ] H) :
    (closedRangeProjection T).range = T.range.topologicalClosure :=
  Submodule.range_starProjection _

/-- Each projected vector lies in the original closed range. -/
theorem closedRangeProjection_apply_mem (T : H →L[ℂ] H) (x : H) :
    closedRangeProjection T x ∈ T.range.topologicalClosure :=
  Submodule.starProjection_apply_mem _ _

/-- The actual closed-range projection fixes every value of the original operator. -/
theorem closedRangeProjection_mul_self (T : H →L[ℂ] H) :
    closedRangeProjection T * T = T := by
  apply ContinuousLinearMap.ext
  intro x
  change T.range.topologicalClosure.starProjection (T x) = T x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact Submodule.le_topologicalClosure _ ⟨x, rfl⟩

variable {K : Type v} [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- A continuous linear map annihilating T also annihilates its closed-range projection. -/
theorem comp_closedRangeProjection_eq_zero (T : H →L[ℂ] H) (B : H →L[ℂ] K)
    (hBT : B.comp T = 0) : B.comp (closedRangeProjection T) = 0 := by
  let N : Submodule ℂ H := LinearMap.ker B.toLinearMap
  have hNclosed : IsClosed (N : Set H) := by
    change IsClosed (B ⁻¹' ({0} : Set K))
    exact isClosed_singleton.preimage B.continuous
  have hrange : T.range ≤ N := by
    rintro x ⟨y, rfl⟩
    change B (T y) = 0
    have h := congrArg (fun C : H →L[ℂ] K => C y) hBT
    simpa only [comp_apply, zero_apply] using h
  have hclosure : T.range.topologicalClosure ≤ N :=
    Submodule.topologicalClosure_minimal _ hrange hNclosed
  apply ContinuousLinearMap.ext
  intro x
  change B (closedRangeProjection T x) = 0
  exact hclosure (closedRangeProjection_apply_mem T x)

end

end ContinuousLinearMap
