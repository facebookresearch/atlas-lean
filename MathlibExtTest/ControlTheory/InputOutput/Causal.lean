/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.InputOutput.Causal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

open ControlTheory ContinuousLinearMap Filter Topology

/-- Diagonal filtration on `Fin n → ℝ`: `truncFilt t` keeps the
coordinates `i ≤ t`. -/
noncomputable def truncFilt {n : ℕ} (t : Fin n) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => if i ≤ t then ContinuousLinearMap.proj i else 0

lemma truncFilt_apply {n : ℕ} (t : Fin n) (x : Fin n → ℝ) (i : Fin n) :
    truncFilt t x i = if i ≤ t then x i else 0 := by
  by_cases h : i ≤ t <;> simp [truncFilt, h]

theorem truncFilt_law {n : ℕ} :
    ∀ s t : Fin n, (truncFilt s).comp (truncFilt t) = truncFilt (s ⊓ t) := by
  intro s t
  refine ContinuousLinearMap.ext fun x => funext fun i => ?_
  simp only [comp_apply, truncFilt_apply, le_inf_iff]
  by_cases hs : i ≤ s <;> by_cases ht : i ≤ t <;> simp [hs, ht]

/-- Pointwise idempotence of the truncation projections, derived
from the filtration law at `s = t`. -/
theorem truncFilt_idem {n : ℕ} :
    ∀ t : Fin n, (truncFilt t).comp (truncFilt t) = truncFilt t := by
  intro t
  have h := truncFilt_law t t
  rwa [inf_idem] at h

/-- The operator of a square array (row `i` is output coordinate `i`). -/
noncomputable def arrayOp {n : ℕ} (M : Fin n → Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ j, M i j • ContinuousLinearMap.proj j

lemma arrayOp_apply {n : ℕ} (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    arrayOp M x i = ∑ j, M i j * x j := by
  simp [arrayOp]

/-- Unit delay on `Fin 3 → ℝ`: `![0, x 0, x 1]`. -/
noncomputable def delayOp : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  arrayOp ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0]]

lemma delayOp_apply (x : Fin 3 → ℝ) : delayOp x = ![0, x 0, x 1] := by
  funext i; fin_cases i <;> simp [delayOp, arrayOp_apply, Fin.sum_univ_three]

/-- One-step advance on `Fin 3 → ℝ`: `![x 1, 0, 0]`. -/
noncomputable def advOp : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  arrayOp ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]]

lemma advOp_apply (x : Fin 3 → ℝ) : advOp x = ![x 1, 0, 0] := by
  funext i; fin_cases i <;> simp [advOp, arrayOp_apply, Fin.sum_univ_three]

-- The delay is prefix causal for both remaining filtration levels
-- (membership in the subalgebra is the predicate, by definition).
theorem delay_mem :
    delayOp ∈ prefixCausalSubalgebra truncFilt truncFilt_idem := by
  show IsPrefixCausal truncFilt delayOp
  intro t
  refine ContinuousLinearMap.ext fun x => funext fun i => ?_
  fin_cases t <;> fin_cases i <;> simp [comp_apply, truncFilt_apply, delayOp_apply]

-- The advance is not prefix causal: at `t = 0` on `![0, 1, 0]` the two
-- sides of the prefix law give `1` and `0`.
theorem adv_not_mem :
    advOp ∉ prefixCausalSubalgebra truncFilt truncFilt_idem := by
  intro h
  have h0 := congrFun (DFunLike.congr_fun (h 0) ![0, 1, 0]) 0
  simp [comp_apply, truncFilt_apply, advOp_apply] at h0

-- Subalgebra operations on members, through the algebra API.
example : delayOp + delayOp ∈ prefixCausalSubalgebra truncFilt truncFilt_idem :=
  Subalgebra.add_mem _ delay_mem delay_mem

example : delayOp * delayOp ∈ prefixCausalSubalgebra truncFilt truncFilt_idem :=
  Subalgebra.mul_mem _ delay_mem delay_mem

-- Neumann series of the half delay: causal by the theorem, and equal
-- to `1 + T + T ^ 2` since `T ^ 3 = 0`.
noncomputable abbrev halfDelay : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (2 : ℝ)⁻¹ • delayOp

lemma delay_norm_le (x : Fin 3 → ℝ) : ‖delayOp x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => ?_
  rw [delayOp_apply]
  fin_cases i
  · simp
  · simpa using norm_le_pi_norm x 0
  · simpa using norm_le_pi_norm x 1

theorem halfDelay_norm_lt : ‖halfDelay‖ < 1 := by
  refine lt_of_le_of_lt (b := 1 / 2) ?_ (by norm_num)
  refine opNorm_le_bound _ (by norm_num) fun x => ?_
  calc ‖halfDelay x‖ = (2 : ℝ)⁻¹ * ‖delayOp x‖ := by
        rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
    _ ≤ (2 : ℝ)⁻¹ * ‖x‖ := by
        exact mul_le_mul_of_nonneg_left (delay_norm_le x) (by norm_num)
    _ = (1 / 2) * ‖x‖ := by norm_num

theorem neumann_causal :
    IsPrefixCausal truncFilt (∑' k : ℕ, halfDelay ^ k) :=
  IsPrefixCausal.tsum_pow truncFilt truncFilt_idem
    (Subalgebra.smul_mem _ delay_mem _) halfDelay_norm_lt

lemma halfDelay_pow_three : halfDelay ^ 3 = 0 := by
  have hD : delayOp ^ 3 = 0 := by
    refine ContinuousLinearMap.ext fun x => funext fun i => ?_
    simp only [pow_succ, mul_apply_eq_comp, delayOp_apply]
    fin_cases i <;> simp
  rw [smul_pow, hD, smul_zero]

theorem neumann_eq :
    ∑' k : ℕ, halfDelay ^ k = 1 + halfDelay + halfDelay ^ 2 := by
  rw [tsum_eq_sum (s := Finset.range 3)
    (fun b hb => by
      have : 3 ≤ b := by simpa using hb
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le this
      rw [pow_add, halfDelay_pow_three, zero_mul])]
  simp [Finset.sum_range_succ]

example : (∑' k : ℕ, halfDelay ^ k) ![1, 2, 4] = ![1, 5 / 2, 21 / 4] := by
  rw [neumann_eq]
  funext i
  fin_cases i <;> simp [add_apply, smul_apply, delayOp_apply, pow_succ] <;> norm_num

#print axioms isClosed_prefixCausalCarrier
#print axioms IsPrefixCausal.tsum_pow
