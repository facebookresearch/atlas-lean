/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingSymbolReduction
import Code.FrontierA.QuantumIsingBogoliubovLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp









open Filter
open scoped Topology

namespace StatMech.FrontierA

private theorem cosh_sub_one_eq_two_sinh_half_sq (t : Real) :
    Real.cosh t - 1 = 2 * Real.sinh (t / 2) ^ 2 := by
  have hdouble := Real.cosh_two_mul (t / 2)
  have hcs := Real.cosh_sq_sub_sinh_sq (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hdouble
  nlinarith

theorem sinh_div_tendsto_one_right :
    Tendsto (fun t : Real => Real.sinh t / t) (𝓝[>] 0) (nhds 1) := by
  have h := (Real.hasDerivAt_sinh 0).tendsto_slope_zero_right
  simpa [div_eq_inv_mul, smul_eq_mul] using h

theorem cosh_sub_one_div_sq_tendsto_half_right :
    Tendsto (fun t : Real => (Real.cosh t - 1) / t ^ 2)
      (𝓝[>] 0) (nhds (1 / 2 : Real)) := by
  have hhalf : Tendsto (fun t : Real => t / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hfull : Tendsto (fun t : Real => t / 2) (nhds 0) (nhds 0) := by
        convert (tendsto_id : Tendsto (fun t : Real => t)
          (nhds 0) (nhds 0)).div_const 2 using 1 <;> norm_num
      exact hfull.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      exact div_pos ht (by norm_num)
  have hs := sinh_div_tendsto_one_right.comp hhalf
  have hsSq := hs.pow 2
  have hscaled := (tendsto_const_nhds.mul hsSq : Tendsto
    (fun t : Real => (1 / 2 : Real) * (Real.sinh (t / 2) / (t / 2)) ^ 2)
    (𝓝[>] 0) (nhds ((1 / 2 : Real) * 1 ^ 2)))
  have heq : (fun t : Real => (Real.cosh t - 1) / t ^ 2) =ᶠ[𝓝[>] 0]
      (fun t : Real => (1 / 2 : Real) * (Real.sinh (t / 2) / (t / 2)) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    rw [cosh_sub_one_eq_two_sinh_half_sq]
    field_simp [ht.ne']
  simpa using hscaled.congr' heq.symm

noncomputable def quantumIsingReducedParameterAtScale
    (h k t : Real) : Real :=
  Real.cosh t * ((1 + (h * t) ^ 2) / (1 - (h * t) ^ 2)) +
    Real.sinh t * (2 * (h * t) / (1 - (h * t) ^ 2)) * Real.cos k

theorem quantumIsingReducedParameterAtScale_eq
    (beta h k : Real) (n : Nat) :
    quantumIsingTrotterReducedParameter beta h n k =
      quantumIsingReducedParameterAtScale h k (beta / (2 * n)) := by
  unfold quantumIsingTrotterReducedParameter quantumIsingReducedParameterAtScale
  ring

theorem quantumIsingReducedParameter_scaled_tendsto
    (h k : Real) :
    Tendsto
      (fun t : Real => (quantumIsingReducedParameterAtScale h k t - 1) / t ^ 2)
      (𝓝[>] 0)
      (nhds ((1 + 4 * h ^ 2 + 4 * h * Real.cos k) / 2)) := by
  let r : Real -> Real := fun t => (1 + (h * t) ^ 2) / (1 - (h * t) ^ 2)
  let s : Real -> Real := fun t => 2 * h / (1 - (h * t) ^ 2)
  have ht0 : Tendsto (fun t : Real => t) (𝓝[>] 0) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hdenT : Tendsto (fun t : Real => 1 - (h * t) ^ 2)
      (𝓝[>] 0) (nhds 1) := by
    convert (tendsto_const_nhds.sub
      ((tendsto_const_nhds.mul ht0).pow 2)) using 1 <;> norm_num
  have hnumT : Tendsto (fun t : Real => 1 + (h * t) ^ 2)
      (𝓝[>] 0) (nhds 1) := by
    convert (tendsto_const_nhds.add
      ((tendsto_const_nhds.mul ht0).pow 2)) using 1 <;> norm_num
  have hr : Tendsto r (𝓝[>] 0) (nhds 1) := by
    dsimp [r]
    convert hnumT.div hdenT one_ne_zero using 1 <;> norm_num
  have hs : Tendsto s (𝓝[>] 0) (nhds (2 * h)) := by
    dsimp [s]
    convert tendsto_const_nhds.div hdenT one_ne_zero using 1 <;> norm_num
  have hdenEv : ∀ᶠ t : Real in 𝓝[>] 0, 1 - (h * t) ^ 2 ≠ 0 :=
    hdenT (eventually_ne_nhds one_ne_zero)
  have hcorr : Tendsto (fun t : Real => (r t - 1) / t ^ 2)
      (𝓝[>] 0) (nhds (2 * h ^ 2)) := by
    have heq : ∀ᶠ t : Real in 𝓝[>] (0 : Real),
        (r t - 1) / t ^ 2 = 2 * h ^ 2 / (1 - (h * t) ^ 2) := by
      filter_upwards [self_mem_nhdsWithin, hdenEv] with t ht hden
      change 0 < t at ht
      have ht0 : t ≠ 0 := ht.ne'
      dsimp [r]
      have hden' : 1 - h ^ 2 * t ^ 2 ≠ 0 := by
        simpa [mul_pow] using hden
      field_simp [ht0, hden, hden']
      ring
    have htend : Tendsto (fun t : Real => 2 * h ^ 2 / (1 - (h * t) ^ 2))
        (𝓝[>] 0) (nhds (2 * h ^ 2)) := by
      convert tendsto_const_nhds.div hdenT (by norm_num) using 1 <;> norm_num
    exact htend.congr' (heq.mono fun _ ht => ht.symm)
  have hcosh := cosh_sub_one_div_sq_tendsto_half_right
  have hsinh := sinh_div_tendsto_one_right
  have hfirst := hcosh.mul hr
  have hsecond := hcorr
  have hthird := (hsinh.mul hs).const_mul (Real.cos k)
  have hsum := (hfirst.add hsecond).add hthird
  have heq : (fun t : Real =>
      (quantumIsingReducedParameterAtScale h k t - 1) / t ^ 2) =ᶠ[𝓝[>] 0]
      (fun t => (Real.cosh t - 1) / t ^ 2 * r t +
        (r t - 1) / t ^ 2 + Real.cos k * (Real.sinh t / t * s t)) := by
    filter_upwards [self_mem_nhdsWithin, hdenEv] with t ht hden
    change 0 < t at ht
    have htne : t ≠ 0 := ht.ne'
    dsimp [quantumIsingReducedParameterAtScale, r, s]
    field_simp [htne, hden]
    ring
  convert hsum.congr' heq.symm using 1 <;> ring

end StatMech.FrontierA

namespace StatMech.FrontierA

private theorem beta_div_nat_succ_tendsto_nhdsGT_zero
    {beta : Real} (hbeta : 0 < beta) :
    Tendsto (fun n : Nat => beta / (2 * (n + 1 : Real))) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hone := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)
    have hconst : Tendsto (fun _ : Nat => beta / 2) atTop (nhds (beta / 2)) :=
      tendsto_const_nhds
    convert hconst.mul hone using 1
    · funext n
      field_simp
    · simp
  · filter_upwards with n
    change 0 < beta / (2 * ((n : Real) + 1))
    positivity



theorem quantumIsingTrotterReducedParameter_scaled_tendsto
    (beta h k : Real) (hbeta : 0 < beta) :
    Tendsto
      (fun n : Nat => (n + 1 : Real) ^ 2 *
        (quantumIsingTrotterReducedParameter beta h (n + 1) k - 1))
      atTop
      (nhds (beta ^ 2 / 8 * quantumIsingDispersion h k ^ 2)) := by
  let t : Nat -> Real := fun n => beta / (2 * (n + 1 : Real))
  have ht : Tendsto t atTop (𝓝[>] 0) :=
    beta_div_nat_succ_tendsto_nhdsGT_zero hbeta
  have hbase := (quantumIsingReducedParameter_scaled_tendsto h k).comp ht
  have hscaled := (tendsto_const_nhds.mul hbase : Tendsto
    (fun n : Nat => (beta ^ 2 / 4) *
      ((quantumIsingReducedParameterAtScale h k (t n) - 1) / (t n) ^ 2))
    atTop
    (nhds ((beta ^ 2 / 4) *
      ((1 + 4 * h ^ 2 + 4 * h * Real.cos k) / 2))))
  have hdisp : quantumIsingDispersion h k ^ 2 =
      1 + 4 * h ^ 2 + 4 * h * Real.cos k := by
    unfold quantumIsingDispersion
    rw [Real.sq_sqrt (quantumIsing_radicand_nonneg h k)]
  convert hscaled using 1
  · funext n
    rw [quantumIsingReducedParameterAtScale_eq]
    norm_num only [Nat.cast_add, Nat.cast_one]
    dsimp [t]
    have hn : (n : Real) + 1 ≠ 0 := by positivity
    field_simp [hbeta.ne', hn]
    ring
  · rw [hdisp]
    ring

end StatMech.FrontierA
