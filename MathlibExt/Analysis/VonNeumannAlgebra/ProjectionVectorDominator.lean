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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalFunctional
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Real.Sqrt

/-!
# Range vectors dominating a bounded functional on a projection

Let `M ⊆ B(H)` be a concrete von Neumann algebra, `φ ∈ M*` any bounded complex-linear
functional, and `e∈M` a nonzero star projection. There is `ξ∈H` with `eξ=ξ` and `Re φ(e)<Re
⟨ξ,eξ⟩=‖ξ‖²`.

This is a strict scalar comparison obtained by scaling a nonzero range vector. Positivity or
normality of `φ` is not required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Range vector with strictly dominating diagonal coefficient.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. for any `φ ∈ M*` and
nonzero star projection `e ∈ M`, `projectionVectorDominator M φ e` returns `ξ ∈ H` with
`eξ=ξ` and `Re φ(e)<Re(vectorFunctional M ξ ξ e)=‖ξ‖²`. No positivity or normality of `φ`
is assumed. -/
def projectionVectorDominator (M : VonNeumannAlgebra H) (φ : StrongDual ℂ M)
    (e : M) (he : IsStarProjection e) (hne : e ≠ 0) :
    {ξ : H // (e : H →L[ℂ] H) ξ = ξ ∧ (φ e).re < (vectorFunctional M ξ ξ e).re} := by
  classical
  let T : H →L[ℂ] H := e
  have hT : T * T = T := congrArg (fun p : M => (p : H →L[ℂ] H)) he.isIdempotentElem.eq
  have hTNonzero : T ≠ 0 := by
    intro hzero
    apply hne
    apply Subtype.ext
    exact hzero
  have hexists : ∃ v : H, T v ≠ 0 := by
    by_contra hnot
    apply hTNonzero
    apply ContinuousLinearMap.ext
    intro v
    change T v = 0
    by_contra hv
    exact hnot ⟨v, hv⟩
  let v : H := Classical.choose hexists
  have hv : T v ≠ 0 := Classical.choose_spec hexists
  let w : H := T v
  have hwNonzero : w ≠ 0 := hv
  have hwNorm : 0 < ‖w‖ := norm_pos_iff.mpr hwNonzero
  have hwFixed : T w = w := by
    have h := congrArg (fun A : H →L[ℂ] H => A v) hT
    simpa only [mul_apply_eq_comp] using h
  let N : ℝ := ‖φ e‖ + 1
  have hN : 0 < N := by
    dsimp only [N]
    linarith [norm_nonneg (φ e)]
  let r : ℝ := Real.sqrt N / ‖w‖
  have hr : 0 ≤ r := div_nonneg (Real.sqrt_nonneg N) hwNorm.le
  let ξ : H := r • w
  have hξFixed : T ξ = ξ := by
    change T (r • w) = r • w
    rw [T.map_smul_of_tower, hwFixed]
  have hξNorm : ‖ξ‖ = Real.sqrt N := by
    change ‖r • w‖ = Real.sqrt N
    rw [norm_smul, Real.norm_of_nonneg hr]
    dsimp only [r]
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hwNorm.ne', mul_one]
  have hξNormSq : ‖ξ‖ ^ 2 = N := by
    rw [hξNorm]
    exact Real.sq_sqrt hN.le
  have hvalue : (vectorFunctional M ξ ξ e).re = ‖ξ‖ ^ 2 := by
    rw [vectorFunctional_apply]
    change RCLike.re ⟪ξ, T ξ⟫_ℂ = ‖ξ‖ ^ 2
    rw [hξFixed]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ
  have hstrict : (φ e).re < (vectorFunctional M ξ ξ e).re := by
    rw [hvalue, hξNormSq]
    exact (Complex.re_le_norm (φ e)).trans_lt (by dsimp only [N]; linarith)
  exact ⟨ξ, hξFixed, hstrict⟩

end

end VonNeumannAlgebra
