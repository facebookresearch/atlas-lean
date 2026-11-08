/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The spectrum of the unilateral shift is the closed unit ball

For the unilateral shift `S` on `ℓ²(ℕ, 𝕜)` and its adjoint, the
backward shift `B`, the spectrum is `Metric.closedBall 0 1` in the scalar field:
the closed unit disc for `ℂ` and the interval `[-1, 1]` for `ℝ`. The proof has
three parts:

* `‖S‖ ≤ 1` (and `‖B‖ ≤ 1`), so either spectrum is contained in the
  closed unit ball (`spectrum.norm_le_norm_mul_of_mem`).
* The open unit ball is contained in either spectrum: if `‖μ‖ < 1`,
  the geometric vector `v = (1, c, c², …)` with `c = star μ`
  satisfies `B v = (star μ) • v`; pairing `(μ • 1 - S) x = v`
  against `v` gives `‖v‖² = 0`, a contradiction, so
  `μ • 1 - S` is not a unit.
  Dually, `v = (1, μ, μ², …)` is in the kernel of `μ • 1 - B`, so
  `μ • 1 - B` is not injective, hence not a unit.
* The boundary follows because the spectrum is closed
  (`spectrum.isClosed`) and the closed unit ball is the closure of the
  open unit ball (`closure_ball`).

These spectrum computations are new derived results. The archived
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean` provide
related context; they do not supply an exact shift-spectrum target or proof.
The proof below uses the geometric vectors, the adjoint relation, and Mathlib's
unit/bijectivity, spectrum-bound and closedness APIs.

## Main declarations

* `geometricVec` : the geometric vector `(1, c, c², …)` in `ℓ²(ℕ, 𝕜)`
  for `‖c‖ < 1`.
* `backwardCLM_geometricVec` : it is an eigenvector of the backward
  shift, `B v = c • v`.
* `spectrum_shiftCLM` : `spectrum 𝕜 S = Metric.closedBall 0 1`.
* `spectrum_backwardCLM` : `spectrum 𝕜 B = Metric.closedBall 0 1`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.LpShiftOperatorSpectrum

open Filter Topology Set Metric
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The geometric vector `(1, c, c², …)` is in `ℓ²` when `‖c‖ < 1`. -/
theorem memℓp_geometric {c : 𝕜} (hc : ‖c‖ < 1) : Memℓp (fun i : ℕ => c ^ i) 2 := by
  apply memℓp_gen
  have hsq : ‖c‖ ^ 2 < 1 := (sq_lt_one_iff₀ (norm_nonneg _)).mpr hc
  have hsum : Summable (fun i : ℕ => (‖c‖ ^ 2) ^ i) :=
    summable_geometric_of_lt_one (by positivity) hsq
  have heq : (fun i : ℕ => ‖(c : 𝕜) ^ i‖ ^ (2 : ℝ≥0∞).toReal)
      = fun i => (‖c‖ ^ 2) ^ i := by
    funext i
    rw [norm_pow, show (2 : ℝ≥0∞).toReal = (2 : ℝ) from by simp, Real.rpow_two,
      ← pow_mul, mul_comm i 2, pow_mul]
  rw [heq]
  exact hsum

/-- The geometric vector `(1, c, c², …)` in `ℓ²(ℕ, 𝕜)`, for `‖c‖ < 1`. -/
noncomputable def geometricVec {c : 𝕜} (hc : ‖c‖ < 1) : ℓ²(ℕ, 𝕜) :=
  ⟨fun i => c ^ i, memℓp_geometric hc⟩

/-- Pointwise action of the geometric vector. -/
theorem geometricVec_apply {c : 𝕜} (hc : ‖c‖ < 1) (i : ℕ) :
    geometricVec hc i = c ^ i :=
  rfl

/-- The geometric vector is nonzero: its `0`-th coordinate is `1`. -/
theorem geometricVec_ne_zero {c : 𝕜} (hc : ‖c‖ < 1) : geometricVec hc ≠ 0 := by
  intro h
  have h0 := congr_fun (congr_arg (fun z : ℓ²(ℕ, 𝕜) => (z : ℕ → 𝕜)) h) 0
  rw [geometricVec_apply] at h0
  simp at h0

/-- The geometric vector is an eigenvector of the backward shift:
`B v = c • v`. -/
theorem backwardCLM_geometricVec {c : 𝕜} (hc : ‖c‖ < 1) :
    backwardCLM (geometricVec hc) = c • geometricVec hc := by
  apply lp.ext
  funext i
  simp only [backwardCLM_apply, backwardFun_apply, geometricVec_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, pow_succ']

/-- The operator norm of the identity on `ℓ²(ℕ, 𝕜)` is at most `1`. -/
theorem norm_one_le : ‖(1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    (fun x => by simp [one_apply_eq_self])
/-- Applying `μ • 1 - T` to a vector, where `μ • 1` is the scalar
operator from the algebra structure on continuous linear maps. -/
theorem algebraMap_sub_apply (T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) (μ : 𝕜)
    (x : ℓ²(ℕ, 𝕜)) :
    (algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) μ - T) x = μ • x - T x := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [sub_apply, smul_apply, one_apply_eq_self]

/-- Every point of the open unit ball is in the spectrum of the
unilateral shift: if `μ • 1 - S` were a unit, it would be surjective, but
pairing `(μ • 1 - S) x = v` against the geometric eigenvector `v` of
`B` with eigenvalue `star μ` gives `‖v‖² = 0`. -/
theorem mem_spectrum_shiftCLM_of_norm_lt {μ : 𝕜} (hμ : ‖μ‖ < 1) :
    μ ∈ spectrum 𝕜 (shiftCLM (𝕜 := 𝕜)) := by
  have hc : ‖star μ‖ < 1 := by rwa [norm_star]
  rw [spectrum.mem_iff]
  intro hunit
  have hbij : Function.Bijective
      ⇑(algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) μ - shiftCLM (𝕜 := 𝕜)) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  obtain ⟨x, hx⟩ := hbij.2 (geometricVec hc)
  have hinner : ⟪(algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) μ - shiftCLM (𝕜 := 𝕜)) x,
      geometricVec hc⟫_𝕜 = ⟪geometricVec hc, geometricVec hc⟫_𝕜 := by
    rw [hx]
  have hLHS : ⟪(algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) μ - shiftCLM (𝕜 := 𝕜)) x,
      geometricVec hc⟫_𝕜 = 0 := by
    rw [algebraMap_sub_apply, inner_sub_left, inner_smul_left,
      ← ContinuousLinearMap.adjoint_inner_right, adjoint_shiftCLM,
      backwardCLM_geometricVec hc, inner_smul_right, starRingEnd_apply, sub_self]
  exact geometricVec_ne_zero hc
    (inner_self_eq_zero.mp (hinner.symm.trans hLHS))

/-- Every point of the open unit ball is in the spectrum of the
backward shift: the geometric vector is in the kernel of `μ • 1 - B`,
so `μ • 1 - B` is not injective, hence not a unit. -/
theorem mem_spectrum_backwardCLM_of_norm_lt {μ : 𝕜} (hμ : ‖μ‖ < 1) :
    μ ∈ spectrum 𝕜 (backwardCLM (𝕜 := 𝕜)) := by
  rw [spectrum.mem_iff]
  intro hunit
  have hinj : Function.Injective
      ⇑(algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) μ - backwardCLM (𝕜 := 𝕜)) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
  have hmap : (algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) μ - backwardCLM (𝕜 := 𝕜))
      (geometricVec hμ) = 0 := by
    rw [algebraMap_sub_apply, backwardCLM_geometricVec hμ, sub_self]
  exact geometricVec_ne_zero hμ (hinj (by rw [hmap, map_zero]))

/-- The spectrum of the unilateral shift is the closed unit ball. -/
theorem spectrum_shiftCLM :
    spectrum 𝕜 (shiftCLM (𝕜 := 𝕜)) = Metric.closedBall 0 1 := by
  apply Subset.antisymm
  · intro μ hμ
    have hmem : ‖μ‖ ≤ ‖shiftCLM (𝕜 := 𝕜)‖ * ‖(1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))‖ :=
      spectrum.norm_le_norm_mul_of_mem hμ
    rw [norm_shiftCLM] at hmem
    have hμ1 : ‖μ‖ ≤ 1 := by
      refine hmem.trans ?_
      calc (1 : ℝ) * ‖(1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))‖
          ≤ 1 * 1 := mul_le_mul (le_refl 1) norm_one_le (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    exact Metric.mem_closedBall.mpr (by rwa [dist_eq_norm, sub_zero])
  · rw [← closure_ball (0 : 𝕜) (by norm_num : (1 : ℝ) ≠ 0)]
    apply (spectrum.isClosed _).closure_subset_iff.mpr
    intro μ hμ
    exact mem_spectrum_shiftCLM_of_norm_lt (by
      simpa [Metric.mem_ball, dist_eq_norm] using hμ)

/-- The spectrum of the backward shift is the closed unit ball. -/
theorem spectrum_backwardCLM :
    spectrum 𝕜 (backwardCLM (𝕜 := 𝕜)) = Metric.closedBall 0 1 := by
  apply Subset.antisymm
  · intro μ hμ
    have hmem : ‖μ‖ ≤ ‖backwardCLM (𝕜 := 𝕜)‖ *
        ‖(1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))‖ :=
      spectrum.norm_le_norm_mul_of_mem hμ
    have hμ1 : ‖μ‖ ≤ 1 := by
      refine hmem.trans ?_
      calc ‖backwardCLM (𝕜 := 𝕜)‖ * ‖(1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))‖
          ≤ 1 * 1 := by
            exact mul_le_mul norm_backwardCLM_le norm_one_le (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    exact Metric.mem_closedBall.mpr (by rwa [dist_eq_norm, sub_zero])
  · rw [← closure_ball (0 : 𝕜) (by norm_num : (1 : ℝ) ≠ 0)]
    apply (spectrum.isClosed _).closure_subset_iff.mpr
    intro μ hμ
    exact mem_spectrum_backwardCLM_of_norm_lt (by
      simpa [Metric.mem_ball, dist_eq_norm] using hμ)

end MathlibExt.Analysis.InnerProductSpace.LpShiftOperatorSpectrum
