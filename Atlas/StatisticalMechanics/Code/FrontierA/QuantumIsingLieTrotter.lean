/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingFiniteHamiltonian
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds









open Filter Matrix
open scoped Topology Norms.Operator

namespace StatMech.FrontierA

private theorem matrix_linfty_norm_le_entry_sum
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m Complex) :
  ‖A‖ ≤ ∑ i : m, ∑ j : m, ‖A i j‖ := by
  rw [Matrix.linfty_opNorm_def]
  have hnn :
      (Finset.univ.sup fun i : m => ∑ j : m, ‖A i j‖₊) ≤
        ∑ i : m, ∑ j : m, ‖A i j‖₊ := by
    apply Finset.sup_le
    intro i hi
    exact Finset.single_le_sum_of_canonicallyOrdered
      (f := fun k : m => (∑ j : m, ‖A k j‖₊ : NNReal))
      (s := Finset.univ) (Finset.mem_univ i)
  have hc :
      ((Finset.univ.sup fun i : m => ∑ j : m, ‖A i j‖₊ : NNReal) : Real) ≤
        ((∑ i : m, ∑ j : m, ‖A i j‖₊ : NNReal) : Real) := by
    exact_mod_cast hnn
  simpa using hc

private theorem one_div_nat_succ_tendsto_nhdsGT_zero :
    Tendsto (fun n : Nat => (1 / (n + 1 : Real))) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  · filter_upwards with n
    show 1 / (n + 1 : Real) ∈ Set.Ioi (0 : Real)
    change (0 : Real) < 1 / (n + 1 : Real)
    positivity



theorem quantumIsingTrotterStep_scaled_sub_entry_tendsto
    (beta h : Real) (L : Nat)
    (sigma tau : QuantumIsingChainConfig L) :
    Tendsto
      (fun n : Nat =>
        ((n + 1 : Real) : Complex) *
          (quantumIsingTrotterStep beta h L (1 / (n + 1 : Real)) sigma tau -
            (1 : Matrix (QuantumIsingChainConfig L)
              (QuantumIsingChainConfig L) Complex) sigma tau))
      atTop
      (nhds (quantumIsingBoltzmannGenerator beta h L sigma tau)) := by
  have hslope :=
    (quantumIsingTrotterStep_entry_hasDerivAt_zero beta h L sigma tau).tendsto_slope_zero_right
  have hcomp := hslope.comp one_div_nat_succ_tendsto_nhdsGT_zero
  convert hcomp using 1
  funext n
  simp only [zero_add]
  rw [quantumIsingTrotterStep_zero]
  change ((n + 1 : Real) : Complex) * _ =
    (((1 / (n + 1 : Real))⁻¹ : Real) : Complex) * _
  congr 1
  rw [inv_div]
  norm_num



theorem quantumIsingTrotterStep_scaled_error_norm_tendsto
    (beta h : Real) (L : Nat) :
    Tendsto
      (fun n : Nat =>
        ‖(n + 1 : Real) •
            (quantumIsingTrotterStep beta h L (1 / (n + 1 : Real)) - 1) -
          quantumIsingBoltzmannGenerator beta h L‖)
      atTop (nhds 0) := by
  let error : Nat -> Matrix (QuantumIsingChainConfig L)
      (QuantumIsingChainConfig L) Complex := fun n =>
    (n + 1 : Real) •
        (quantumIsingTrotterStep beta h L (1 / (n + 1 : Real)) - 1) -
      quantumIsingBoltzmannGenerator beta h L
  have hentry (sigma tau : QuantumIsingChainConfig L) :
      Tendsto (fun n => error n sigma tau) atTop (nhds 0) := by
    have h := (quantumIsingTrotterStep_scaled_sub_entry_tendsto
      beta h L sigma tau).sub
        (tendsto_const_nhds
          (x := quantumIsingBoltzmannGenerator beta h L sigma tau))
    simpa only [error, Matrix.sub_apply, Pi.smul_apply,
      Complex.real_smul, Complex.ofReal_natCast, sub_self] using h
  have hsum : Tendsto
      (fun n => ∑ sigma : QuantumIsingChainConfig L,
        ∑ tau : QuantumIsingChainConfig L, ‖error n sigma tau‖)
      atTop (nhds 0) := by
    convert tendsto_finsetSum Finset.univ (fun sigma _ =>
        tendsto_finsetSum Finset.univ (fun tau _ =>
          (continuous_norm.tendsto 0).comp (hentry sigma tau))) using 1
    all_goals simp
  apply squeeze_zero (fun n => norm_nonneg (error n))
    (fun n => matrix_linfty_norm_le_entry_sum (error n)) hsum


theorem quantumIsingExponentialStep_scaled_error_norm_tendsto
    (beta h : Real) (L : Nat) :
    Tendsto
      (fun n : Nat =>
        ‖(n + 1 : Real) •
            (NormedSpace.exp
                ((1 / (n + 1 : Real)) •
                  quantumIsingBoltzmannGenerator beta h L) - 1) -
          quantumIsingBoltzmannGenerator beta h L‖)
      atTop (nhds 0) := by
  let C := quantumIsingBoltzmannGenerator beta h L
  have hslope :=
    (hasDerivAt_exp_smul_const C (0 : Real)).tendsto_slope_zero_right
  have hcomp := hslope.comp one_div_nat_succ_tendsto_nhdsGT_zero
  simp only [zero_add, zero_smul,
    NormedSpace.exp_zero, one_mul] at hcomp
  have hvec : Tendsto
      (fun n : Nat =>
        (n + 1 : Real) •
            (NormedSpace.exp ((1 / (n + 1 : Real)) • C) - 1) - C)
      atTop (nhds 0) := by
    convert hcomp.sub tendsto_const_nhds using 1
    · funext n
      change (n + 1 : Real) • _ - C =
        (1 / (n + 1 : Real))⁻¹ • _ - C
      congr 2
      rw [inv_div]
      norm_num
    · rw [sub_self]
      rfl
  simpa [C] using (continuous_norm.tendsto 0).comp hvec

private theorem norm_pow_sub_pow_le
    {A : Type*} [NormedRing A] [NormOneClass A] (a b : A) (m : Nat) :
    ‖a ^ m - b ^ m‖ ≤
      (m : Real) * (max 1 (max ‖a‖ ‖b‖)) ^ m * ‖a - b‖ := by
  let q : Real := max 1 (max ‖a‖ ‖b‖)
  have hq_one : 1 ≤ q := le_max_left _ _
  have hq_nonneg : 0 ≤ q := zero_le_one.trans hq_one
  have ha : ‖a‖ ≤ q := le_max_left _ _ |>.trans (le_max_right _ _)
  have hb : ‖b‖ ≤ q := le_max_right _ _ |>.trans (le_max_right _ _)
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        ‖a ^ (m + 1) - b ^ (m + 1)‖ =
            ‖(a ^ m - b ^ m) * a + b ^ m * (a - b)‖ := by
              congr 1
              noncomm_ring
        _ ≤ ‖a ^ m - b ^ m‖ * ‖a‖ + ‖b ^ m‖ * ‖a - b‖ := by
              exact (norm_add_le _ _).trans <|
                add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ (m : Real) * q ^ m * ‖a - b‖ * q +
              q ^ m * ‖a - b‖ := by
              gcongr
              exact (norm_pow_le b m).trans
                (pow_le_pow_left₀ (norm_nonneg b) hb m)
        _ ≤ ((m + 1 : Nat) : Real) * q ^ (m + 1) * ‖a - b‖ := by
              rw [pow_succ]
              have hpow : 0 ≤ q ^ m := pow_nonneg hq_nonneg _
              have hnorm : 0 ≤ ‖a - b‖ := norm_nonneg _
              have hdiff : 0 ≤ q - 1 := sub_nonneg.mpr hq_one
              push_cast
              nlinarith only [mul_nonneg (mul_nonneg hpow hnorm) hdiff]



theorem quantumIsingTrotterStep_power_tendsto_exp
    (beta h : Real) (L : Nat) :
    Tendsto
      (fun n : Nat =>
        (quantumIsingTrotterStep beta h L
          (1 / (n + 1 : Real))) ^ (n + 1))
      atTop
      (nhds (NormedSpace.exp
        (quantumIsingBoltzmannGenerator beta h L))) := by
  let C : Matrix (QuantumIsingChainConfig L)
      (QuantumIsingChainConfig L) Complex :=
    quantumIsingBoltzmannGenerator beta h L
  let F : Nat -> Matrix (QuantumIsingChainConfig L)
      (QuantumIsingChainConfig L) Complex := fun n =>
    quantumIsingTrotterStep beta h L (1 / (n + 1 : Real))
  let E : Nat -> Matrix (QuantumIsingChainConfig L)
      (QuantumIsingChainConfig L) Complex := fun n =>
    NormedSpace.exp ((1 / (n + 1 : Real)) • C)
  have hF : Tendsto
      (fun n : Nat => ‖(n + 1 : Real) • (F n - 1) - C‖)
      atTop (nhds 0) := by
    simpa [F, C] using
      quantumIsingTrotterStep_scaled_error_norm_tendsto beta h L
  have hE : Tendsto
      (fun n : Nat => ‖(n + 1 : Real) • (E n - 1) - C‖)
      atTop (nhds 0) := by
    simpa [E, C] using
      quantumIsingExponentialStep_scaled_error_norm_tendsto beta h L
  have hFvec : Tendsto
      (fun n : Nat => (n + 1 : Real) • (F n - 1))
      atTop (nhds C) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hF
  have hEvec : Tendsto
      (fun n : Nat => (n + 1 : Real) • (E n - 1))
      atTop (nhds C) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hE
  have hFnorm : Tendsto
      (fun n : Nat => (n + 1 : Real) * ‖F n - 1‖)
      atTop (nhds ‖C‖) := by
    convert (continuous_norm.tendsto C).comp hFvec using 1
    funext n
    change (n + 1 : Real) * ‖F n - 1‖ =
      ‖(n + 1 : Real) • (F n - 1)‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hEnorm : Tendsto
      (fun n : Nat => (n + 1 : Real) * ‖E n - 1‖)
      atTop (nhds ‖C‖) := by
    convert (continuous_norm.tendsto C).comp hEvec using 1
    funext n
    change (n + 1 : Real) * ‖E n - 1‖ =
      ‖(n + 1 : Real) • (E n - 1)‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  let g : Nat -> Real := fun n => max ‖F n - 1‖ ‖E n - 1‖
  have hgscaled : Tendsto
      (fun n : Nat => (n + 1 : Real) * g n)
      atTop (nhds ‖C‖) := by
    convert hFnorm.max hEnorm using 1
    · funext n
      change (n + 1 : Real) * max ‖F n - 1‖ ‖E n - 1‖ =
        max ((n + 1 : Real) * ‖F n - 1‖)
          ((n + 1 : Real) * ‖E n - 1‖)
      exact mul_max_of_nonneg _ _ (by positivity)
    · simp
  have hginv : Tendsto (fun n : Nat => 1 / (n + 1 : Real))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)
  have hgzero : Tendsto g atTop (nhds 0) := by
    have hmul := hginv.mul hgscaled
    convert hmul using 1
    · funext n
      dsimp [g]
      field_simp
    · simp
  have hgnscaled : Tendsto (fun n : Nat => (n : Real) * g n)
      atTop (nhds ‖C‖) := by
    convert hgscaled.sub hgzero using 1
    · funext n
      ring
    · simp
  have hgpower : Tendsto
      (fun n : Nat => (1 + g n) ^ (n + 1))
      atTop (nhds (Real.exp ‖C‖)) := by
    have hn := Real.tendsto_one_add_pow_exp_of_tendsto hgnscaled
    have hbase : Tendsto (fun n : Nat => 1 + g n) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hgzero
    simpa [pow_succ] using hn.mul hbase
  have hscaledDiff : Tendsto
      (fun n : Nat => (n + 1 : Real) * ‖F n - E n‖)
      atTop (nhds 0) := by
    have hsum : Tendsto
        (fun n : Nat => ‖(n + 1 : Real) • (F n - 1) - C‖ +
          ‖(n + 1 : Real) • (E n - 1) - C‖)
        atTop (nhds 0) := by
      simpa using hF.add hE
    apply squeeze_zero
      (fun n => mul_nonneg (by positivity) (norm_nonneg _))
      (fun n => ?_)
      hsum
    let r : Real := n + 1
    have hid : r • (F n - E n) =
        (r • (F n - 1) - C) - (r • (E n - 1) - C) := by
      module
    have hr : 0 < r := by
      dsimp [r]
      positivity
    calc
      (n + 1 : Real) * ‖F n - E n‖ = ‖r • (F n - E n)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = ‖(r • (F n - 1) - C) - (r • (E n - 1) - C)‖ := by rw [hid]
      _ ≤ ‖r • (F n - 1) - C‖ + ‖r • (E n - 1) - C‖ :=
        norm_sub_le _ _
  have hpowError : Tendsto
      (fun n : Nat => ‖F n ^ (n + 1) - E n ^ (n + 1)‖)
      atTop (nhds 0) := by
    have hupper : Tendsto
        (fun n : Nat => ((n + 1 : Real) * ‖F n - E n‖) *
          (1 + g n) ^ (n + 1)) atTop (nhds 0) := by
      simpa using hscaledDiff.mul hgpower
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hupper
    let q : Real := max 1 (max ‖F n‖ ‖E n‖)
    have hFbase : ‖F n‖ ≤ 1 + ‖F n - 1‖ := by
      calc
        ‖F n‖ = ‖(F n - 1) + 1‖ := by
          congr 1
          noncomm_ring
        _ ≤ ‖F n - 1‖ + ‖(1 : Matrix (QuantumIsingChainConfig L)
            (QuantumIsingChainConfig L) Complex)‖ := norm_add_le _ _
        _ = 1 + ‖F n - 1‖ := by rw [norm_one]; ring
    have hEbase : ‖E n‖ ≤ 1 + ‖E n - 1‖ := by
      calc
        ‖E n‖ = ‖(E n - 1) + 1‖ := by
          congr 1
          noncomm_ring
        _ ≤ ‖E n - 1‖ + ‖(1 : Matrix (QuantumIsingChainConfig L)
            (QuantumIsingChainConfig L) Complex)‖ := norm_add_le _ _
        _ = 1 + ‖E n - 1‖ := by rw [norm_one]; ring
    have hq : q ≤ 1 + g n := by
      apply max_le
      · exact le_add_of_nonneg_right (by simp [g])
      · apply max_le
        · calc
            ‖F n‖ ≤ 1 + ‖F n - 1‖ := hFbase
            _ ≤ 1 + g n := by
              gcongr
              simp [g]
        · calc
            ‖E n‖ ≤ 1 + ‖E n - 1‖ := hEbase
            _ ≤ 1 + g n := by
              gcongr
              simp [g]
    have hq0 : 0 ≤ q := zero_le_one.trans (le_max_left _ _)
    calc
      ‖F n ^ (n + 1) - E n ^ (n + 1)‖ ≤
          (n + 1 : Real) * q ^ (n + 1) * ‖F n - E n‖ :=
        by simpa [q, Nat.cast_add, Nat.cast_one] using
          norm_pow_sub_pow_le (F n) (E n) (n + 1)
      _ = ((n + 1 : Real) * ‖F n - E n‖) * q ^ (n + 1) := by ring
      _ ≤ ((n + 1 : Real) * ‖F n - E n‖) *
          (1 + g n) ^ (n + 1) := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_left₀ hq0 hq _
        · positivity
  change Tendsto (fun n : Nat => F n ^ (n + 1)) atTop
    (nhds (NormedSpace.exp C))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hpowError using 1
  funext n
  change ‖F n ^ (n + 1) - NormedSpace.exp C‖ = _
  have hEpow : E n ^ (n + 1) = NormedSpace.exp C := by
    rw [← Matrix.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul Real, smul_smul]
    have hn : (n : Real) + 1 ≠ 0 := by positivity
    rw [Nat.cast_add, Nat.cast_one, one_div]
    rw [mul_inv_cancel₀ hn, one_smul]
  rw [hEpow]



theorem quantumIsingTrotterTransferMatrix_power_tendsto_exp
    (beta h : Real) (L : Nat) :
    Tendsto
      (fun n : Nat =>
        (quantumIsingTrotterTransferMatrix beta h (n + 1) L) ^ (n + 1))
      atTop
      (nhds (NormedSpace.exp
        (quantumIsingBoltzmannGenerator beta h L))) := by
  apply (quantumIsingTrotterStep_power_tendsto_exp beta h L).congr'
  filter_upwards with n
  rw [quantumIsingTrotterTransferMatrix_eq_step beta h (n + 1) L (by omega)]
  norm_num [Nat.cast_add, Nat.cast_one]



theorem quantumIsingTrotterTrace_tendsto_quantumPartition
    (beta h : Real) (L : Nat) :
    Tendsto
      (fun n : Nat =>
        ((quantumIsingTrotterTransferMatrix beta h (n + 1) L) ^
          (n + 1)).trace)
      atTop (nhds (quantumIsingQuantumPartition beta h L)) := by
  have hmatrix :=
    quantumIsingTrotterTransferMatrix_power_tendsto_exp beta h L
  simpa [quantumIsingQuantumPartition] using
    (continuous_id.matrix_trace.tendsto _).comp hmatrix




theorem quantumIsingNormalizedClassicalCylinder_tendsto_quantumPartition
    (beta h : Real) (L : Nat) (hbh : 0 < beta * h) :
    Tendsto
      (fun n : Nat =>
        ((Real.exp (-quantumIsingVerticalCoupling beta h (n + 1)) ^
            (L * (n + 1)) *
          quantumIsingClassicalCylinderPartition beta h (n + 1) L : Real) :
          Complex))
      atTop (nhds (quantumIsingQuantumPartition beta h L)) := by
  apply (quantumIsingTrotterTrace_tendsto_quantumPartition beta h L).congr'
  filter_upwards with n
  rw [quantumIsingTrotterTrace_eq_classical beta h (n + 1) L
    (by omega) (by positivity)]


end StatMech.FrontierA
