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

public import MathlibExt.Analysis.VonNeumannAlgebra.ProjectionVectorDominator
public import MathlibExt.Analysis.VonNeumannAlgebra.LocalVectorComparison
public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveCutoffLocalization

/-!
# Nonzero projection with a locally dominating vector coefficient

For a positive bounded functional `ψ` on a concrete von Neumann algebra and nonzero star
projection `e`, there is a nonzero star projection `p≤e` and vector `ξ∈H` such that `Re ψ(b)≤Re
⟨ξ,bξ⟩` for every positive `b≤p`.

The projection and vector are constructed from `ψ,e`; normality of the functional or a vector
domination bound is not an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Nonzero local projection and vector dominating its positive corner.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M →
ℂ` be a positive bounded complex-linear functional for the spectral orders. for a nonzero
star projection `e∈M`, the construction returns `(p,ξ)` with `p` a nonzero star
projection, `p≤e`, and `Re ψ(b)≤Re ⟨ξ,bξ⟩` whenever `0≤b≤p`. -/
def localVectorDominatedProjection (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) → (e : M) → IsStarProjection e → e ≠ 0 →
      {q : M × H // IsStarProjection q.1 ∧ q.1 ≠ 0 ∧
        @LE.le M (CStarAlgebra.spectralOrder M).toLE q.1 e ∧
        ∀ t : PositiveElement M,
          @LE.le M (CStarAlgebra.spectralOrder M).toLE (t : M) q.1 →
          (ψ.toContinuousLinearMap (t : M)).re ≤ (vectorFunctional M q.2 q.2 (t : M)).re} := by
  classical
  let sourceOrder : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder M := sourceOrder
  letI : Preorder M := sourceOrder.toPreorder
  letI : LE M := sourceOrder.toLE
  letI : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  letI : IsOrderedAddMonoid M := StarOrderedRing.toIsOrderedAddMonoid
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ e he hne
  let φ : StrongDual ℂ M := ψ.toContinuousLinearMap
  let v := projectionVectorDominator M φ e he hne
  let ξ : H := v.val
  have he0 : @LE.le M (CStarAlgebra.spectralOrder M).toLE 0 e := by
    simpa only [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq] using star_mul_self_nonneg e
  let a : PositiveElement M := ⟨e, he0⟩
  let b := localVectorComparisonPositiveElement M ψ a ξ v.property.2
  have hbNonzero : (b.val : M) ≠ 0 := b.property.2.1
  let thresholdExists := exists_positiveCutoffProjection_nonzero M b.val hbNonzero
  let r : ℝ := Classical.choose thresholdExists
  have hthreshold := Classical.choose_spec thresholdExists
  have hr : 0 < r := hthreshold.1
  let p : M := positiveCutoffProjection M b.val r
  have hp : IsStarProjection p := positiveCutoffProjection_isStarProjection M b.val r
  have hpNonzero : p ≠ 0 := hthreshold.2
  have hpBelow : @LE.le M (CStarAlgebra.spectralOrder M).toLE p e :=
    positiveCutoffProjection_le_projection M b.val e he r hr b.property.1
  have hrp : @LE.le M (CStarAlgebra.spectralOrder M).toLE (r • p) (b.val : M) :=
    positiveCutoffProjection_threshold M b.val r
  have hlocal (t : PositiveElement M)
      (htp : @LE.le M (CStarAlgebra.spectralOrder M).toLE (t : M) p) :
      (φ (t : M)).re ≤ (vectorFunctional M ξ ξ (t : M)).re := by
    by_cases htzero : (t : M) = 0
    · rw [htzero]
      simp
    · let u : PositiveElement M := positiveSmul (NNReal.mk r hr.le) t
      have huNonzero : (u : M) ≠ 0 := by
        intro huzero
        have hraw := congrArg (fun x : M => r⁻¹ • x) huzero
        have h : (r⁻¹ * ((NNReal.mk r hr.le : NNReal) : ℝ)) • (t : M) = 0 := by
          simpa only [u, positiveSmul, smul_smul, smul_zero] using hraw
        have hcast : ((NNReal.mk r hr.le : NNReal) : ℝ) = r := rfl
        rw [hcast, inv_mul_cancel₀ hr.ne', one_smul] at h
        exact htzero h
      have huBelow : @LE.le M (CStarAlgebra.spectralOrder M).toLE (u : M) (b.val : M) := by
        change r • (t : M) ≤ (b.val : M)
        exact (smul_le_smul_of_nonneg_left htp hr.le).trans hrp
      have hstrict := b.property.2.2 u huNonzero huBelow
      have hφ : (φ (r • (t : M))).re = r * (φ (t : M)).re := by
        change RCLike.re (φ (r • (t : M))) = r * RCLike.re (φ (t : M))
        rw [φ.map_smul_of_tower, RCLike.smul_re]
      have hvector : (vectorFunctional M ξ ξ (r • (t : M))).re =
          r * (vectorFunctional M ξ ξ (t : M)).re := by
        change RCLike.re (vectorFunctional M ξ ξ (r • (t : M))) =
          r * RCLike.re (vectorFunctional M ξ ξ (t : M))
        rw [(vectorFunctional M ξ ξ).map_smul_of_tower, RCLike.smul_re]
      change (φ (r • (t : M))).re < (vectorFunctional M ξ ξ (r • (t : M))).re at hstrict
      rw [hφ, hvector] at hstrict
      have hsmall : (φ (t : M)).re < (vectorFunctional M ξ ξ (t : M)).re := by
        nlinarith
      exact hsmall.le
  exact ⟨(p, ξ), hp, hpNonzero, hpBelow, hlocal⟩

end

end VonNeumannAlgebra
