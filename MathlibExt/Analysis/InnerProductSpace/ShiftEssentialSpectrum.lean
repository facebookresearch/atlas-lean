/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator
public import MathlibExt.Analysis.InnerProductSpace.ShiftFredholmIndex

import MathlibExt.Analysis.Normed.Operator.FredholmIndexHomotopy
import Mathlib.Algebra.Module.LinearMap.FiniteRange
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.NormNum

/-!
# Essential spectrum of the unilateral shift on `ℓ²(ℕ, 𝕜)`

Let `S` be the unilateral (forward) shift on `ℓ²(ℕ, 𝕜)`. Its
spectrum is the closed unit disc (see e.g. Reed–Simon, *Methods of
Modern Mathematical Physics I: Functional Analysis*, Section VII.2).
This file computes the smaller **essential spectrum**: the set of
`μ` for which `S - μ • 1` is not a Fredholm operator.

* `essentialSpectrum_shiftCLM`: the essential spectrum of `S` is the
  unit circle `Metric.sphere 0 1`.
* `isFredholm_shift_sub_smul_one_of_norm_lt_one`: for `‖μ‖ < 1`,
  `S - μ • 1` is Fredholm of index `-1`.
* `isFredholm_shift_sub_smul_one_of_one_lt_norm`: for `‖μ‖ > 1`,
  `S - μ • 1` is Fredholm of index `0` (it is a unit).
* `not_isFredholm_shift_sub_smul_one_of_norm_eq_one`: for `‖μ‖ = 1`,
  `S - μ • 1` is not Fredholm, because the truncated geometric
  vectors `(1, μ̄, μ̄², …, μ̄ᴺ, 0, …)` are approximate eigenvectors
  with `‖(S - μ) v_N‖² = 2` while `‖v_N‖² = N + 1`, so `S - μ • 1`
  is not bounded below, whereas a Fredholm operator with trivial
  kernel is.

This is a companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the spectral theorem, the Fredholm alternative). It is derived
supporting content rather than one of the 72 v1 targets. The file
uses the established unilateral and backward shifts from
`LpShiftOperator`, their Fredholmness and index from `ShiftFredholmIndex`,
and the general continuous-path index theorem from `FredholmIndexHomotopy`.
The additional essential-spectrum definition uses Mathlib's general
`ContinuousLinearMap.IsFredholm` convention.

## Main declarations

* `essentialSpectrum`: `μ` is in the essential spectrum of `T` iff
  `T - μ • 1` is not a Fredholm operator.
* The operators in these statements are
  `LpShiftOperator.shiftCLM` and `LpShiftOperator.backwardCLM`.
* `essentialSpectrum_shiftCLM`: the essential spectrum of the shift
  is the unit circle.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.ShiftEssentialSpectrum

open Filter Topology Set
open LpShiftOperator
open scoped _root_.lp ENNReal
open scoped LinearMap.FiniteRangeSetoid

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **essential spectrum** of a bounded operator `T`: the set of
scalars `μ` for which `T - μ • 1` is not a Fredholm operator. -/
def essentialSpectrum {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : E →L[𝕜] E) : Set 𝕜 :=
  {μ | ¬ (T - μ • 1).IsFredholm}

section ShiftSub

/-- Pointwise action of `1 - μ • B`. -/
theorem one_sub_smul_backward_apply (μ : 𝕜) (x : ℓ²(ℕ, 𝕜)) (j : ℕ) :
    ((1 - μ • LpShiftOperator.backwardCLM (𝕜 := 𝕜)) x : ℕ → 𝕜) j =
      (x : ℕ → 𝕜) j - μ * (x : ℕ → 𝕜) (j + 1) := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul,
    Pi.sub_apply, Pi.smul_apply, backwardCLM_apply, backwardFun_apply, smul_eq_mul]

/-- The key factorization: `S - μ = S (1 - μ B) + μ (S B - 1)`. -/
theorem shift_sub_smul_one_eq (μ : 𝕜) :
    LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1 =
      LpShiftOperator.shiftCLM (𝕜 := 𝕜) ∘L (1 - μ • LpShiftOperator.backwardCLM (𝕜 := 𝕜)) +
        μ • (LpShiftOperator.shiftCLM (𝕜 := 𝕜) ∘L LpShiftOperator.backwardCLM (𝕜 := 𝕜) - 1) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  cases i with
  | zero =>
      simp only [sub_apply, smul_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply, add_apply, lp.coeFn_sub, lp.coeFn_add,
        lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, shiftCLM_apply, shiftFun_zero,
        zero_sub, zero_add, mul_neg]
  | succ n =>
      simp only [sub_apply, smul_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply, add_apply, lp.coeFn_sub, lp.coeFn_add,
        lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, shiftCLM_apply, backwardCLM_apply, backwardFun_apply, shiftFun_succ,
        sub_self, mul_zero, add_zero]

/-- `S - μ • 1` has trivial kernel for every `μ`: the coordinate
equations force every coordinate to vanish. -/
theorem injective_shift_sub (μ : 𝕜) :
    Function.Injective ⇑(LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have heq : ∀ m, shiftFun (x : ℕ → 𝕜) m = μ * (x : ℕ → 𝕜) m := by
    intro m
    have hm := congr_fun (congr_arg (fun z : ℓ²(ℕ, 𝕜) => (z : ℕ → 𝕜)) hx) m
    simp only [ContinuousLinearMap.coe_coe, sub_apply, smul_apply,
      one_apply_eq_self, shiftCLM_apply, lp.coeFn_sub, lp.coeFn_smul, lp.coeFn_zero,
      Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, sub_eq_zero] at hm
    exact hm
  apply lp.ext
  funext n
  simp only [lp.coeFn_zero, Pi.zero_apply]
  induction n with
  | zero =>
      by_cases hμ0 : μ = 0
      · have h1 := heq 1
        rw [hμ0, shiftFun_succ, zero_mul] at h1
        exact h1
      · have h0 := heq 0
        rw [shiftFun_zero] at h0
        have hmul : μ * (x : ℕ → 𝕜) 0 = 0 := h0.symm
        rcases mul_eq_zero.mp hmul with h | h
        · exact absurd h hμ0
        · exact h
  | succ n ih =>
      by_cases hμ0 : μ = 0
      · have h := heq (n + 2)
        rw [hμ0, shiftFun_succ, zero_mul] at h
        exact h
      · have h := heq (n + 1)
        rw [shiftFun_succ, ih] at h
        have hmul : μ * (x : ℕ → 𝕜) (n + 1) = 0 := h.symm
        rcases mul_eq_zero.mp hmul with h' | h'
        · exact absurd h' hμ0
        · exact h'

/-- `1 - μ • B` is a unit when `‖μ‖ < 1`, by the Neumann-series
criterion `isUnit_one_sub_of_norm_lt_one`. -/
theorem isUnit_one_sub_smul_backward {μ : 𝕜} (hμ : ‖μ‖ < 1) :
    IsUnit (1 - μ • LpShiftOperator.backwardCLM (𝕜 := 𝕜)) := by
  apply isUnit_one_sub_of_norm_lt_one
  calc ‖μ • LpShiftOperator.backwardCLM (𝕜 := 𝕜)‖ =
      ‖μ‖ * ‖LpShiftOperator.backwardCLM (𝕜 := 𝕜)‖ := norm_smul _ _
    _ ≤ ‖μ‖ * 1 := mul_le_mul_of_nonneg_left norm_backwardCLM_le (norm_nonneg _)
    _ = ‖μ‖ := mul_one _
    _ < 1 := hμ

/-- A unit operator is Fredholm, via `IsHomeomorph` and
`IsInvertible.isFredholm`. -/
theorem isFredholm_of_isUnit {T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)} (hT : IsUnit T) :
    T.IsFredholm := by
  have hhome : IsHomeomorph T := ContinuousLinearMap.isHomeomorph_of_isUnit hT
  exact (ContinuousLinearMap.IsInvertible.of_isHomeomorph hhome).isFredholm

/-- `1 - μ • B` is Fredholm when `‖μ‖ < 1`. -/
theorem isFredholm_one_sub_smul_backward {μ : 𝕜} (hμ : ‖μ‖ < 1) :
    (1 - μ • LpShiftOperator.backwardCLM (𝕜 := 𝕜)).IsFredholm :=
  isFredholm_of_isUnit (isUnit_one_sub_smul_backward hμ)

/-- For `‖μ‖ < 1`, `S - μ • 1` is Fredholm: it is the Fredholm
operator `S (1 - μ B)` plus the finite-rank operator `μ (S B - 1)`. -/
theorem isFredholm_shift_sub_smul_one_of_norm_lt_one {μ : 𝕜} (hμ : ‖μ‖ < 1) :
    (LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1).IsFredholm := by
  have hS : (LpShiftOperator.shiftCLM (𝕜 := 𝕜)).IsFredholm := by
    simpa only [pow_one] using ShiftFredholmIndex.isFredholm_shiftCLM_pow (𝕜 := 𝕜) 1
  have hdefect :
      (LpShiftOperator.shiftCLM (𝕜 := 𝕜) ∘L LpShiftOperator.backwardCLM -
        1).toLinearMap.HasFiniteRange := by
    have h := ShiftFredholmIndex.approx_shift_comp_backward (𝕜 := 𝕜) 1
    rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange] at h
    simp only [pow_one] at h
    have heq :
        (↑(LpShiftOperator.shiftCLM (𝕜 := 𝕜)) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) ∘ₗ
          ↑(LpShiftOperator.backwardCLM (𝕜 := 𝕜)) - LinearMap.id =
        (LpShiftOperator.shiftCLM (𝕜 := 𝕜) ∘L LpShiftOperator.backwardCLM - 1).toLinearMap := by
      ext x
      simp [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_sub,
        ContinuousLinearMap.toLinearMap_one]
    rw [heq] at h
    exact h
  rw [shift_sub_smul_one_eq μ]
  apply ContinuousLinearMap.IsFredholm.add_hasFiniteRange _ _
  · exact hS.comp (isFredholm_one_sub_smul_backward hμ)
  · exact hdefect.smul μ

/-- The index of `S - μ • 1` is `-1` for `‖μ‖ < 1`: the canonical
homotopy theorem makes the index constant along `S - (t μ) • 1`,
`t ∈ [0, 1]`, and the canonical shift has index `-1` at `t = 0`. -/
theorem index_shift_sub_smul_one_of_norm_lt_one {μ : 𝕜} (hμ : ‖μ‖ < 1) :
    (LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1).index = -1 := by
  have hfred : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (LpShiftOperator.shiftCLM (𝕜 := 𝕜) - ((t : 𝕜) * μ) • 1).IsFredholm := by
    intro t ht
    apply isFredholm_shift_sub_smul_one_of_norm_lt_one
    rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg ht.1]
    calc t * ‖μ‖ ≤ 1 * ‖μ‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ = ‖μ‖ := one_mul _
      _ < 1 := hμ
  have hcoef : Continuous (fun t : ℝ => (t : 𝕜) * μ) :=
    Continuous.mul RCLike.continuous_ofReal continuous_const
  have hγ :
      Continuous (fun t : ℝ => LpShiftOperator.shiftCLM (𝕜 := 𝕜) - ((t : 𝕜) * μ) • 1) :=
    continuous_const.sub (hcoef.smul continuous_const)
  have hconst :=
    MathlibExt.Analysis.Normed.Operator.FredholmIndexHomotopy.index_eq_of_continuous_path
      (𝕜 := 𝕜) hγ hfred
  simp only [RCLike.ofReal_zero, RCLike.ofReal_one, zero_mul, one_mul] at hconst
  rw [← hconst]
  have hz : (0 : 𝕜) • (1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) = 0 :=
    Module.zero_smul (R := 𝕜) (M := ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) _
  rw [hz, sub_zero]
  exact ShiftFredholmIndex.index_shiftCLM (𝕜 := 𝕜)

/-- For `‖μ‖ > 1`, `S - μ • 1` is a unit: it equals
`(algebraMap (-μ)) * (1 - μ⁻¹ • S)`, a product of units. -/
theorem isUnit_shift_sub_smul_one_of_one_lt_norm {μ : 𝕜} (hμ : 1 < ‖μ‖) :
    IsUnit (LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) := by
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hμ
    exact absurd hμ (by norm_num)
  have hnormS : ‖LpShiftOperator.shiftCLM (𝕜 := 𝕜)‖ ≤ 1 := (norm_shiftCLM (𝕜 := 𝕜)).le
  have hsmall : IsUnit (1 - μ⁻¹ • LpShiftOperator.shiftCLM (𝕜 := 𝕜)) := by
    apply isUnit_one_sub_of_norm_lt_one
    calc ‖μ⁻¹ • LpShiftOperator.shiftCLM (𝕜 := 𝕜)‖ =
        ‖μ⁻¹‖ * ‖LpShiftOperator.shiftCLM (𝕜 := 𝕜)‖ := norm_smul _ _
      _ ≤ ‖μ⁻¹‖ * 1 := mul_le_mul_of_nonneg_left hnormS (norm_nonneg _)
      _ = ‖μ‖⁻¹ := by rw [mul_one, norm_inv]
      _ < 1 := inv_lt_one_of_one_lt₀ hμ
  have hscalar : IsUnit (algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) (-μ)) :=
    IsUnit.map (algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)))
      (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hμ0))
  have hprod : algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) (-μ) *
      (1 - μ⁻¹ • LpShiftOperator.shiftCLM (𝕜 := 𝕜)) =
      LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1 := by
    ext x
    simp only [mul_apply_eq_comp, sub_apply,
      smul_apply, one_apply_eq_self,
      Algebra.algebraMap_eq_smul_one]
    rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hμ0, neg_one_smul, sub_neg_eq_add,
      neg_smul, add_comm, sub_eq_add_neg]
  rw [← hprod]
  exact hscalar.mul hsmall

/-- For `‖μ‖ > 1`, `S - μ • 1` is Fredholm, as it is a unit. -/
theorem isFredholm_shift_sub_smul_one_of_one_lt_norm {μ : 𝕜} (hμ : 1 < ‖μ‖) :
    (LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1).IsFredholm :=
  isFredholm_of_isUnit (isUnit_shift_sub_smul_one_of_one_lt_norm hμ)

/-- For `‖μ‖ > 1`, `S - μ • 1` has index `0`: a unit is bijective. -/
theorem index_shift_sub_smul_one_of_one_lt_norm {μ : 𝕜} (hμ : 1 < ‖μ‖) :
    (LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1).index = 0 := by
  have hhome : IsHomeomorph ⇑(LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) :=
    ContinuousLinearMap.isHomeomorph_of_isUnit
      (isUnit_shift_sub_smul_one_of_one_lt_norm hμ)
  have hbij : Function.Bijective ⇑(LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) :=
    (ContinuousLinearMap.IsInvertible.of_isHomeomorph hhome).bijective
  exact LinearMap.index_of_bijective hbij

end ShiftSub

section ApproximateEigenvectors

/-- The truncated geometric sequence `(1, μ̄, μ̄², …, μ̄ᴺ, 0, …)`. -/
def approxFun (μ : 𝕜) (N : ℕ) : ℕ → 𝕜 := fun n => if n ≤ N then (star μ) ^ n else 0

/-- The truncated geometric sequence is in `ℓ²`: it has finite support. -/
theorem memℓp_approxFun (μ : 𝕜) (N : ℕ) : Memℓp (approxFun μ N) 2 := by
  apply memℓp_gen
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  rw [Finset.mem_range] at hn
  have hle : ¬ n ≤ N := by omega
  simp [approxFun, hle]

/-- The truncated geometric sequence as an `ℓ²` vector. -/
noncomputable def approxVec (μ : 𝕜) (N : ℕ) : ℓ²(ℕ, 𝕜) := ⟨approxFun μ N, memℓp_approxFun μ N⟩

theorem approxVec_apply (μ : 𝕜) (N n : ℕ) :
    (approxVec μ N) n = approxFun μ N n := rfl

/-- The squared norm of the truncated geometric vector is `N + 1`,
when `‖μ‖ = 1`. -/
theorem norm_sq_approxVec {μ : 𝕜} (hμ : ‖μ‖ = 1) (N : ℕ) :
    ‖approxVec μ N‖ ^ 2 = (N + 1 : ℝ) := by
  have hpow := lp.norm_rpow_eq_tsum (p := 2) (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (approxVec μ N)
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  simp only [h2, Real.rpow_two] at hpow
  rw [hpow]
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · have hterm : ∀ i ∈ Finset.range (N + 1), ‖(approxVec μ N) i‖ ^ 2 = 1 := by
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [approxVec_apply, approxFun, ite_eq_left (show i ≤ N from by omega), norm_pow,
        norm_star, hμ, one_pow]
    refine (Finset.sum_congr rfl hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  · intro i hi
    rw [Finset.mem_range] at hi
    simp [approxVec_apply, approxFun, show ¬ i ≤ N from by omega]

/-- The coordinates of `(S - μ • 1)` applied to the truncated
geometric vector: `-μ` at `0`, `(star μ)^N` at `N + 1`, and `0`
elsewhere, when `‖μ‖ = 1`. -/
theorem sub_smul_one_approxVec_apply_zero {μ : 𝕜} (N : ℕ) :
    ((LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)) 0 = -μ := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shiftCLM_apply, shiftFun_zero,
    approxVec_apply, approxFun, ite_eq_left (Nat.zero_le N), pow_zero, mul_one, zero_sub]

theorem sub_smul_one_approxVec_apply_succ {μ : 𝕜} (_hμ : ‖μ‖ = 1) (N : ℕ) :
    ((LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)) (N + 1) = (star μ) ^ N := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shiftCLM_apply, shiftFun_succ,
    approxVec_apply, approxFun, ite_eq_right (by omega : ¬ N + 1 ≤ N), mul_zero, sub_zero,
    ite_eq_left (le_refl N)]

theorem sub_smul_one_approxVec_apply_of_ne {μ : 𝕜} (hμ : ‖μ‖ = 1) (N : ℕ) {m : ℕ}
    (hm0 : m ≠ 0) (hmN : m ≠ N + 1) :
    ((LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)) m = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : ((LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)) (k + 1) =
      (approxVec μ N) k - μ * (approxVec μ N) (k + 1) := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shiftCLM_apply, shiftFun_succ]
  rw [h1]
  by_cases hk : k + 1 ≤ N
  · have hkN : k ≤ N := by omega
    have hstar : μ * star μ = 1 := by
      rw [RCLike.star_def, RCLike.mul_conj, hμ]
      simp
    rw [approxVec_apply, approxVec_apply, approxFun, approxFun, ite_eq_left hk, ite_eq_left hkN,
      pow_succ]
    have key : μ * ((star μ) ^ k * star μ) = (star μ) ^ k := by
      calc μ * ((star μ) ^ k * star μ) = (star μ) ^ k * (μ * star μ) := by ring
        _ = (star μ) ^ k * 1 := by rw [hstar]
        _ = (star μ) ^ k := mul_one _
    rw [key, sub_self]
  · have hkN : ¬ k ≤ N := by omega
    rw [approxVec_apply, approxVec_apply, approxFun, approxFun, ite_eq_right hk, ite_eq_right hkN]
    simp

/-- The squared norm of `(S - μ • 1)` applied to the truncated
geometric vector is `2`, when `‖μ‖ = 1`. -/
theorem norm_sq_sub_smul_one_approxVec {μ : 𝕜} (hμ : ‖μ‖ = 1) (N : ℕ) :
    ‖(LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)‖ ^ 2 = 2 := by
  have hpow := lp.norm_rpow_eq_tsum (p := 2) (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    ((LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N))
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  simp only [h2, Real.rpow_two] at hpow
  rw [hpow]
  rw [tsum_eq_sum (s := {0, N + 1})]
  · rw [Finset.sum_pair (by omega : (0 : ℕ) ≠ N + 1),
      sub_smul_one_approxVec_apply_zero, sub_smul_one_approxVec_apply_succ hμ]
    have h1 : ‖-(μ : 𝕜)‖ ^ 2 = 1 := by simp [norm_neg, hμ]
    have h2 : ‖(star μ) ^ N‖ ^ 2 = 1 := by simp [norm_pow, hμ]
    rw [h1, h2]
    norm_num
  · intro i hi
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have hz : ((LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)) i = 0 :=
      sub_smul_one_approxVec_apply_of_ne hμ N hi.1 hi.2
    rw [hz]
    simp

/-- For `‖μ‖ = 1`, `S - μ • 1` is not Fredholm: it has trivial kernel
and closed range would make it bounded below, contradicting the
approximate eigenvectors. -/
theorem not_isFredholm_shift_sub_smul_one_of_norm_eq_one {μ : 𝕜} (hμ : ‖μ‖ = 1) :
    ¬ (LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1).IsFredholm := by
  intro hfred
  have hinj :
      Function.Injective
        ⇑(LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) :=
    injective_shift_sub μ
  have hclosed :
      IsClosed (Set.range ⇑(LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))) := by
    have h := hfred.isClosed_range
    rwa [LinearMap.coe_range] at h
  obtain ⟨K, hK⟩ :=
    ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range
      (LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) hinj hclosed
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * (K : ℝ) ^ 2 < (N : ℝ) := exists_nat_gt _
  have hnorm : ‖approxVec μ N‖ = Real.sqrt ((N : ℝ) + 1) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_approxVec hμ N]
  have hTnorm : ‖(LpShiftOperator.shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)‖ = Real.sqrt 2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_sub_smul_one_approxVec hμ N]
  have hanti := hK.le_mul_dist (approxVec μ N) 0
  simp only [map_zero, dist_zero_right] at hanti
  rw [hnorm, hTnorm] at hanti
  have hlt : (K : ℝ) * Real.sqrt 2 < Real.sqrt ((N : ℝ) + 1) := by
    have h1 : (K : ℝ) * Real.sqrt 2 = Real.sqrt ((K : ℝ) ^ 2 * 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by exact_mod_cast K.2)]
    rw [h1]
    apply Real.sqrt_lt_sqrt (by positivity)
    have hN' : 2 * (K : ℝ) ^ 2 < (N : ℝ) + 1 := by linarith [hN]
    linarith [hN']
  exact absurd hanti (not_le_of_gt hlt)

end ApproximateEigenvectors

section Main

/-- The essential spectrum of the unilateral shift is the unit circle:
`S - μ • 1` is Fredholm exactly off the circle. -/
theorem essentialSpectrum_shiftCLM :
    essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := 𝕜)) = Metric.sphere (0 : 𝕜) 1 := by
  ext μ
  simp only [essentialSpectrum, Set.mem_ofPred_eq, Metric.mem_sphere, dist_eq_norm, sub_zero]
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h (isFredholm_shift_sub_smul_one_of_norm_lt_one hlt)
    · exact h (isFredholm_shift_sub_smul_one_of_one_lt_norm hgt)
  · intro hnorm hfred
    exact not_isFredholm_shift_sub_smul_one_of_norm_eq_one hnorm hfred

/-- Membership form: `μ` is in the essential spectrum of the shift
iff `‖μ‖ = 1`. -/
theorem mem_essentialSpectrum_shiftCLM {μ : 𝕜} :
    μ ∈ essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := 𝕜)) ↔ ‖μ‖ = 1 := by
  rw [essentialSpectrum_shiftCLM, Metric.mem_sphere, dist_zero_right]

end Main

end MathlibExt.Analysis.InnerProductSpace.ShiftEssentialSpectrum
