/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Compound-interest limits for the exponential in a Banach algebra

The real limit `(1 + x / n) ^ n → exp x` (`Real.tendsto_one_add_div_pow_exp`) holds in every
real Banach algebra, with perturbed bases and exponents: if `Y M → X` and `m M / M → t`, then
`(1 + M⁻¹ • Y M) ^ m M → exp (t • X)`; no commutativity between the `Y M` is needed. The proof
compares `(1 + M⁻¹ • Y M) ^ m M` with `exp (M⁻¹ • Y M) ^ m M = exp ((m M / M) • Y M)` through
a telescoping estimate and the derivative of `exp` at `0`. This is the form used to
pass from discrete-time Markov chains with transition matrices `1 + Q / M + o(1/M)` to the
continuous-time chain with rate matrix `Q`.

## Main results

* `NormedSpace.norm_pow_sub_pow_le`: `‖a ^ m - b ^ m‖ ≤ m ‖a - b‖ max(‖a‖, ‖b‖) ^ (m - 1)`.
* `NormedSpace.tendsto_one_add_inv_smul_pow`: the compound-interest limit.

## References

The scalar case is Mathlib's `Real.tendsto_one_add_div_pow_exp`; the Banach-algebra argument is
the standard telescoping estimate and needs no further source.
-/

@[expose] public section

open Filter Topology

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-- Telescoping estimate for powers in a normed ring with `‖1‖ = 1`:
`‖a ^ m - b ^ m‖ ≤ m ‖a - b‖ max(‖a‖, ‖b‖) ^ (m - 1)`. -/
theorem norm_pow_sub_pow_le (a b : 𝔸) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ m * ‖a - b‖ * max ‖a‖ ‖b‖ ^ (m - 1) := by
  set K := max ‖a‖ ‖b‖
  have hK : 0 ≤ K := (norm_nonneg a).trans (le_max_left _ _)
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    have h1 : ‖a * (a ^ m - b ^ m)‖ ≤ m * ‖a - b‖ * K ^ m := by
      calc ‖a * (a ^ m - b ^ m)‖ ≤ K * (m * ‖a - b‖ * K ^ (m - 1)) :=
            (norm_mul_le _ _).trans (mul_le_mul (le_max_left _ _) ih (norm_nonneg _) hK)
        _ = m * ‖a - b‖ * K ^ m := by
            rcases Nat.eq_zero_or_pos m with rfl | hm
            · simp
            · rw [show K ^ m = K * K ^ (m - 1) by rw [← pow_succ']; congr 1; omega]
              ring
    have h2 : ‖(a - b) * b ^ m‖ ≤ ‖a - b‖ * K ^ m :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ((norm_pow_le b m).trans
        (pow_le_pow_left₀ (norm_nonneg b) (le_max_right _ _) m)) (norm_nonneg _))
    rw [hsplit, Nat.add_sub_cancel]
    calc _ ≤ ‖a * (a ^ m - b ^ m)‖ + ‖(a - b) * b ^ m‖ := norm_add_le _ _
      _ ≤ m * ‖a - b‖ * K ^ m + ‖a - b‖ * K ^ m := add_le_add h1 h2
      _ = ((m + 1 : ℕ) : ℝ) * ‖a - b‖ * K ^ m := by push_cast; ring

variable [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **Compound-interest limit in a Banach algebra.** If `Y M → X` and `m M / M → t`, then
`(1 + M⁻¹ • Y M) ^ m M → exp (t • X)` as `M → ∞`. -/
theorem tendsto_one_add_inv_smul_pow {Y : ℕ → 𝔸} {X : 𝔸} (hY : Tendsto Y atTop (𝓝 X))
    {m : ℕ → ℕ} {t : ℝ} (hm : Tendsto (fun M : ℕ => (m M : ℝ) / M) atTop (𝓝 t)) :
    Tendsto (fun M : ℕ => (1 + (M : ℝ)⁻¹ • Y M) ^ m M) atTop (𝓝 (exp (t • X))) := by
  set Z : ℕ → 𝔸 := fun M => (M : ℝ)⁻¹ • Y M with hZ
  set g : ℕ → ℝ := fun M => ‖exp (Z M) - (1 + Z M)‖ with hg
  -- `Y` is eventually bounded by `C`.
  set C := ‖X‖ + 1 with hC
  have hC0 : 0 ≤ C := by positivity
  have hYC : ∀ᶠ M in atTop, ‖Y M‖ ≤ C :=
    hY.norm.eventually (ge_mem_nhds (by linarith))
  have hinv : Tendsto (fun M : ℕ => (M : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hZ0 : Tendsto Z atTop (𝓝 0) := by
    simpa using hinv.smul hY
  have hZO : Z =O[atTop] (fun M : ℕ => (M : ℝ)⁻¹) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hYC] with M hM
    rw [hZ, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right hM (norm_nonneg _)
  -- `exp z - (1 + z) = o(z)` at `0`, hence `M * g M → 0`.
  have hexp : (fun z : 𝔸 => exp z - (1 + z)) =o[𝓝 0] (fun z => z) := by
    have h := (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).isLittleO
    simp only [exp_zero, sub_zero, one_apply_eq_self] at h
    refine h.congr_left fun z => ?_
    abel
  have hgo : g =o[atTop] (fun M : ℕ => (M : ℝ)⁻¹) :=
    ((hexp.comp_tendsto hZ0).trans_isBigO hZO).norm_left
  have hMg : Tendsto (fun M : ℕ => (M : ℝ) * g M) atTop (𝓝 0) := by
    refine hgo.tendsto_div_nhds_zero.congr fun M => ?_
    rw [div_inv_eq_mul, mul_comm]
  -- The exponential side: `exp (Z M) ^ m M = exp ((m M / M) • Y M) → exp (t • X)`.
  have hb : Tendsto (fun M => exp (Z M) ^ m M) atTop (𝓝 (exp (t • X))) := by
    let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
    have h := (exp_continuous.tendsto _).comp (hm.smul hY)
    refine h.congr fun M => ?_
    rw [Function.comp_apply, ← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, hZ, smul_smul,
      div_eq_mul_inv]
  -- The bound `max ‖1 + Z M‖ ‖exp (Z M)‖ ^ (m M - 1) ≤ B`.
  set B := Real.exp ((C + 1) * (t + 1)) with hB
  have hmt : ∀ᶠ M in atTop, (m M : ℝ) / M ≤ t + 1 := hm.eventually (ge_mem_nhds (by linarith))
  have hK : ∀ᶠ M in atTop, max ‖1 + Z M‖ ‖exp (Z M)‖ ^ (m M - 1) ≤ B := by
    filter_upwards [hYC, hmt, hMg.eventually (ge_mem_nhds one_pos), eventually_gt_atTop 0]
      with M hYM hmM hgM hM0
    have hM : (0 : ℝ) < M := by exact_mod_cast hM0
    have hZM : ‖Z M‖ ≤ C / M := by
      rw [hZ, norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hYM hM.le
    have hgM' : g M ≤ 1 / M := by rw [le_div_iff₀ hM]; linarith
    have h1 : ‖1 + Z M‖ ≤ 1 + ‖Z M‖ := (norm_add_le _ _).trans (by rw [norm_one])
    have h2 : ‖exp (Z M)‖ ≤ 1 + ‖Z M‖ + g M := by
      have := norm_add_le (exp (Z M) - (1 + Z M)) (1 + Z M)
      rw [sub_add_cancel] at this
      linarith
    have hKle : max ‖1 + Z M‖ ‖exp (Z M)‖ ≤ 1 + (C + 1) / M := by
      have : 1 + ‖Z M‖ + g M ≤ 1 + (C + 1) / M := by rw [add_div]; linarith
      exact max_le (by linarith [(norm_nonneg (exp (Z M) - (1 + Z M)))]) (h2.trans this)
    calc max ‖1 + Z M‖ ‖exp (Z M)‖ ^ (m M - 1) ≤ (1 + (C + 1) / M) ^ (m M - 1) :=
          pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) hKle _
      _ ≤ (1 + (C + 1) / M) ^ m M :=
          pow_le_pow_right₀ (by have : 0 ≤ (C + 1) / M := by positivity
                                linarith) (Nat.sub_le _ _)
      _ ≤ Real.exp ((C + 1) / M) ^ m M := by
          gcongr
          linarith [Real.add_one_le_exp ((C + 1) / M)]
      _ = Real.exp ((C + 1) * ((m M : ℝ) / M)) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ B := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hmM (by linarith))
  -- The difference tends to `0`.
  have hdiff : Tendsto (fun M => (1 + Z M) ^ m M - exp (Z M) ^ m M) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun M : ℕ => (m M : ℝ) / M * ((M : ℝ) * g M) * B) atTop
        (𝓝 (t * 0 * B)) := (hm.mul hMg).mul_const B
    rw [mul_zero, zero_mul] at hlim
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hK, eventually_gt_atTop 0] with M hKM hM0
    have hM : (0 : ℝ) < M := by exact_mod_cast hM0
    calc ‖(1 + Z M) ^ m M - exp (Z M) ^ m M‖
        ≤ m M * ‖(1 + Z M) - exp (Z M)‖ * max ‖1 + Z M‖ ‖exp (Z M)‖ ^ (m M - 1) :=
          norm_pow_sub_pow_le _ _ _
      _ ≤ m M * g M * B := by
          rw [norm_sub_rev]
          exact mul_le_mul_of_nonneg_left hKM (by positivity)
      _ = (m M : ℝ) / M * ((M : ℝ) * g M) * B := by field_simp
  simpa using hb.add hdiff

end NormedSpace
