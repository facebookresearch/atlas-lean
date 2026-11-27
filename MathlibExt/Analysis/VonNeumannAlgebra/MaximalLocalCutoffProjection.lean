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

public import MathlibExt.Analysis.VonNeumannAlgebra.MaximalLocalCutoffSupremum
public import MathlibExt.Analysis.VonNeumannAlgebra.MultiplicationPredual
public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveLUBLimit
public import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# The supremum of maximal-family cutoffs is a projection

For a positive bounded functional `ψ`, let `s` be the constructed positive least upper bound of
finite sums from its maximal local orthogonal projection family.

This supremum satisfies `s²=s` and `s*=s`. The conclusion uses the bounded positive cutoff limit
and does not assume the supremum is a projection.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set CStarAlgebra.ScalarWeight
open scoped Topology

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Star projection property of the maximal-family cutoff supremum.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a
positive bounded complex-linear functional for the spectral orders. Let `S` be the
constructed maximal set of pairwise orthogonal nonzero star projections, each admitting a
vector `ξ` with `Re ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`.
the supremum `s=maximalLocalCutoffSupremum M ψ` satisfies `s²=s` and `s*=s`. -/
theorem maximalLocalCutoffSupremum_isStarProjection (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      IsStarProjection ((maximalLocalCutoffSupremum M ψ).val : M) := by
  classical
  let sourceOrder : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder M := sourceOrder
  let : Preorder M := sourceOrder.toPreorder
  let : LE M := sourceOrder.toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let : IsOrderedAddMonoid M := StarOrderedRing.toIsOrderedAddMonoid
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  let P := maximalLocalPositiveFiniteCutoffs M ψ
  let s := maximalLocalCutoffSupremum M ψ
  let a := fun t => (P.val t : M)
  have hlimit : Tendsto (fun t => (ultraweakLinearEquiv M).symm (a t)) atTop
      (𝓝 ((ultraweakLinearEquiv M).symm (s.val : M))) :=
    boundedPositiveIsLUB_tendsto_ultraweak M a (s.val : M)
      (maximalLocalPositiveFiniteCutoffs_monotone M ψ) (fun t => (P.val t).property)
      ⟨1, (maximalLocalPositiveFiniteCutoffs_norm_le_one M ψ)⟩ (maximalLocalCutoffSupremum_isLUB M ψ)
  have hfix (t) : (s.val : M) * a t = a t := by
    have hP : IsStarProjection (a t) := (maximalLocalPositiveFiniteCutoffs_isStarProjection M ψ) t
    have hPs : a t ≤ (s.val : M) := (maximalLocalCutoffSupremum_isLUB M ψ).1 (Set.mem_range_self t)
    have hres : 0 ≤ (1 : M) - (s.val : M) := sub_nonneg.mpr (maximalLocalCutoffSupremum_le_one M ψ)
    have hresle : (1 : M) - (s.val : M) ≤ 1 - a t := sub_le_sub_left hPs 1
    have h := hP.one_sub.mul_right_and_mul_left_of_nonneg_of_le hres hresle
    have hzero : ((1 : M) - (s.val : M)) * a t = 0 := by
      have hproduct := h.1
      rw [mul_sub, mul_one] at hproduct
      exact (sub_eq_self.mp hproduct)
    have hid := hzero
    rw [sub_mul, one_mul, sub_eq_zero] at hid
    exact hid.symm
  have hmult := (ultraweak_left_mul_continuous M (s.val : M)).continuousAt.tendsto.comp hlimit
  have hsame : (fun t => (ultraweakLinearEquiv M).symm ((s.val : M) * a t)) =
      (fun t => (ultraweakLinearEquiv M).symm (a t)) := by
    funext t
    rw [hfix]
  have htarget : Tendsto (fun t => (ultraweakLinearEquiv M).symm ((s.val : M) * a t)) atTop
      (𝓝 ((ultraweakLinearEquiv M).symm ((s.val : M) * (s.val : M)))) := by
    simpa only [Function.comp_def, LinearEquiv.apply_symm_apply] using hmult
  rw [hsame] at htarget
  have hid : (s.val : M) * (s.val : M) = (s.val : M) :=
    (ultraweakLinearEquiv M).symm.injective (tendsto_nhds_unique htarget hlimit)
  exact ⟨hid, IsSelfAdjoint.of_nonneg s.val.property⟩

end

end VonNeumannAlgebra
