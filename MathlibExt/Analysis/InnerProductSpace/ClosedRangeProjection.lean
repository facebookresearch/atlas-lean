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
# Orthogonal projection onto an operator's closed range span

For a bounded operator `T` on a complete complex Hilbert space `H`, let `P_T` be the orthogonal
projection onto `closure(range T)`. It satisfies `P_T²=P_T`, `P_T*=P_T`, `range
P_T=closure(range T)` and `P_T T=T`.

If a bounded complex-linear map `B : H → K` to any complex normed space annihilates `T`, it also
annihilates `P_T`. Closedness of `range T` is not assumed, nor completeness or an inner product
on `K`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ContinuousLinearMap

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Orthogonal projection onto the range closure.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H`. Write `P_T` for the orthogonal projection onto the norm closure
of `range T`. `closedRangeProjection T` is `P_T : H →L[ℂ] H`, the orthogonal projection
onto `closure(range T)`; no closed-range hypothesis is required. -/
def closedRangeProjection (T : H →L[ℂ] H) : H →L[ℂ] H :=
  T.range.topologicalClosure.starProjection

/-- **Range-closure subspace projection.** Let `H` be a complete complex Hilbert space and `T
: H →L[ℂ] H`. Write `P_T` for the orthogonal projection onto the norm closure of `range
T`. `closedRangeProjection T` equals the star projection of the closed submodule
`T.range.topologicalClosure`. -/
theorem closedRangeProjection_eq_starProjection (T : H →L[ℂ] H) :
    closedRangeProjection T = T.range.topologicalClosure.starProjection :=
  rfl

/-- **Self-adjoint idempotence of the range-closure projection.** Let `H` be a complete
complex Hilbert space and `T : H →L[ℂ] H`. Write `P_T` for the orthogonal projection onto
the norm closure of `range T`. `P_T²=P_T` and `P_T*=P_T`. -/
theorem isStarProjection_closedRangeProjection (T : H →L[ℂ] H) :
    IsStarProjection (closedRangeProjection T) :=
  isStarProjection_starProjection

/-- **Range of the range-closure projection.** Let `H` be a complete complex Hilbert space and
`T : H →L[ℂ] H`. Write `P_T` for the orthogonal projection onto the norm closure of `range
T`. `range(closedRangeProjection T)=closure(range T)`. -/
theorem range_closedRangeProjection (T : H →L[ℂ] H) :
    (closedRangeProjection T).range = T.range.topologicalClosure :=
  Submodule.range_starProjection _

/-- **Projected vector belongs to the operator range closure.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H`. Write `P_T` for the orthogonal projection onto the norm
closure of `range T`. for every `x ∈ H`, `closedRangeProjection T x ∈ closure(range T)`. -/
theorem closedRangeProjection_apply_mem (T : H →L[ℂ] H) (x : H) :
    closedRangeProjection T x ∈ T.range.topologicalClosure :=
  Submodule.starProjection_apply_mem _ _

/-- **Range-closure projection fixes the operator image.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H`. Write `P_T` for the orthogonal projection onto the norm
closure of `range T`. `closedRangeProjection T * T=T`, where multiplication is
composition. -/
theorem closedRangeProjection_mul_self (T : H →L[ℂ] H) :
    closedRangeProjection T * T = T := by
  apply ContinuousLinearMap.ext
  intro x
  change T.range.topologicalClosure.starProjection (T x) = T x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact Submodule.le_topologicalClosure _ ⟨x, rfl⟩

variable {K : Type v} [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- **Annihilation passes to the range-closure projection.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H`. Write `P_T` for the orthogonal projection onto the norm
closure of `range T`. for any complex normed space `K` and `B : H →L[ℂ] K`, `B∘T=0`
implies `B∘closedRangeProjection T=0`; `K` may be incomplete. -/
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
