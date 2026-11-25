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

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Finite-coordinate rank-one expansions

Arbitrary finite vector families give a literal double rank-one expansion.
Their sums need not be projections. For genuine Hilbert bases, the same
identity uses the existing finite-coordinate projections. Neither finite
identity assumes ambient completeness or compactness, and neither asserts
operator-norm convergence or a matrix-completion comparison.
-/

@[expose] public section

open scoped BigOperators

universe u𝕜 uE uF uι uκ

namespace InnerProductSpace

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : Type uE} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type uF} [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {ι : Type uι} {κ : Type uκ}

/-- Let `𝕜` be a real or complex scalar field and let `E` and `F` be seminormed inner-product spaces
over `𝕜`. Specify arbitrary vector families indexed by types `ι` and `κ`, finite index subsets,
and a continuous linear map `T : E →L[𝕜] F`.

Finite rank-one sums sandwich a bounded map with its coefficients. The families need not be
orthonormal or bases; the coefficient is linear in the source image, not its conjugate. Empty
and repeated families are allowed. -/
theorem sum_rankOne_comp_sum_rankOne
    (u : ι → E) (v : κ → F) (T : E →L[𝕜] F)
    (s : Finset ι) (t : Finset κ) :
    (∑ j ∈ t, rankOne 𝕜 (v j) (v j)).comp
        (T.comp (∑ i ∈ s, rankOne 𝕜 (u i) (u i))) =
      ∑ j ∈ t, ∑ i ∈ s,
        inner 𝕜 (v j) (T (u i)) • rankOne 𝕜 (v j) (u i) := by
  rw [ContinuousLinearMap.finsetSum_comp]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.comp_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [comp_rankOne, rankOne_comp_rankOne]

end InnerProductSpace

namespace HilbertBasis

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {ι : Type uι} {κ : Type uκ}

/-- Let `𝕜` be a real or complex scalar field and let `E` and `F` be normed inner-product spaces
over `𝕜`. Specify finite coordinate subsets and the indicated vector families or Hilbert bases,
and a continuous linear map `T : E →L[𝕜] F`.

The finite projections of two Hilbert bases expose the bounded map's coefficient matrix, with
target row before source column. No separate ambient completeness or compactness assumption is
needed. -/
theorem proj_comp_proj_eq_sum_rankOne
    (bE : HilbertBasis ι 𝕜 E) (bF : HilbertBasis κ 𝕜 F)
    (T : E →L[𝕜] F) (s : Finset ι) (t : Finset κ) :
    (bF.toUnconditionalSchauderBasis.proj t).comp
        (T.comp (bE.toUnconditionalSchauderBasis.proj s)) =
      ∑ j ∈ t, ∑ i ∈ s,
        inner 𝕜 (bF j) (T (bE i)) •
          InnerProductSpace.rankOne 𝕜 (bF j) (bE i) := by
  have hE : bE.toUnconditionalSchauderBasis.proj s =
      ∑ i ∈ s, InnerProductSpace.rankOne 𝕜 (bE i) (bE i) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [GeneralSchauderBasis.proj_apply]
    change (∑ i ∈ s, inner 𝕜 (bE i) x • bE i) =
      (∑ i ∈ s, InnerProductSpace.rankOne 𝕜 (bE i) (bE i)) x
    simp only [sum_apply, InnerProductSpace.rankOne_apply]
  have hF : bF.toUnconditionalSchauderBasis.proj t =
      ∑ j ∈ t, InnerProductSpace.rankOne 𝕜 (bF j) (bF j) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [GeneralSchauderBasis.proj_apply]
    change (∑ j ∈ t, inner 𝕜 (bF j) x • bF j) =
      (∑ j ∈ t, InnerProductSpace.rankOne 𝕜 (bF j) (bF j)) x
    simp only [sum_apply, InnerProductSpace.rankOne_apply]
  rw [hF, hE]
  exact InnerProductSpace.sum_rankOne_comp_sum_rankOne bE bF T s t

end HilbertBasis

end
