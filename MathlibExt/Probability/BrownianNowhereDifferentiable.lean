/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Nowhere differentiability of Brownian paths

We prove that almost surely a real Brownian path is differentiable at no positive time.
The proof bounds the probability of three consecutive small increments on a fine uniform grid.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal ProbabilityTheory Topology

namespace MathlibExt.Probability.BrownianSamplePathsWanted

private noncomputable def mesh (n : ℕ) : ℝ≥0 := 1 / ((n : ℝ≥0) + 1) ^ 2

private noncomputable def grid (n k : ℕ) : ℝ≥0 := k * mesh n

private lemma coe_grid (n k : ℕ) : (grid n k : ℝ) = (k : ℝ) * (mesh n : ℝ) := by
  simp [grid]

section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private noncomputable def increment (B : ℝ≥0 → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ) + 1) * (B (grid n (k + 1)) ω - B (grid n k) ω)

private lemma hasLaw_increment (hB : IsPreBrownianReal B P) (n k : ℕ) :
    HasLaw (increment B n k) (gaussianReal 0 1) P := by
  have hstep : nndist (grid n (k + 1) : ℝ) (grid n k : ℝ) = mesh n := by
    apply NNReal.eq
    rw [coe_nndist, Real.dist_eq, coe_grid, coe_grid, Nat.cast_add, Nat.cast_one]
    rw [show ((k : ℝ) + 1) * (mesh n : ℝ) - k * (mesh n : ℝ) = mesh n by ring]
    exact abs_of_nonneg (NNReal.coe_nonneg _)
  have hvar : ((n : ℝ≥0) + 1) ^ 2 * mesh n = 1 := by
    unfold mesh
    have hn : ((n : ℝ≥0) + 1) ^ 2 ≠ 0 := by positivity
    exact mul_div_cancel₀ 1 hn
  have h : HasLaw (B (grid n (k + 1)) - B (grid n k))
      (gaussianReal 0 (nndist (grid n (k + 1) : ℝ) (grid n k : ℝ))) P :=
    hB.hasLaw_sub (grid n (k + 1)) (grid n k)
  rw [hstep] at h
  have hscale : NNReal.mk (((n : ℝ) + 1) ^ 2) (sq_nonneg _) = ((n : ℝ≥0) + 1) ^ 2 := by
    apply NNReal.eq
    simp
  unfold increment
  simpa only [Pi.sub_apply, mul_zero, hscale, hvar] using
    gaussianReal_const_mul h ((n : ℝ) + 1)

private lemma gaussianReal_zero_one_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  refine le_trans (b := volume.withDensity fun _ : ℝ ↦ 1) ?_ (by simp)
  refine withDensity_mono (Filter.Eventually.of_forall fun x ↦ ?_)
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) ≤ 1
  apply ENNReal.ofReal_le_one.mpr
  have hs : 1 ≤ Real.sqrt (2 * Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.one_le_pi_div_two]
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have he : Real.exp (-x ^ 2 / (2 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
  calc
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 := mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ 1 := by simpa using (inv_le_one₀ (by positivity)).mpr hs

private noncomputable def smallIncrements (B : ℝ≥0 → Ω → ℝ) (K n k : ℕ) : Set Ω :=
  ⋂ i : Fin 3, increment B n (k + i) ⁻¹' Icc (-(K : ℝ) / (n + 1)) ((K : ℝ) / (n + 1))

private lemma measure_smallIncrements (hB : IsPreBrownianReal B P) (K n k : ℕ) :
    P (smallIncrements B K n k) ≤ ENNReal.ofReal (2 * K / ((n : ℝ) + 1)) ^ 3 := by
  let I := Icc (-(K : ℝ) / ((n : ℝ) + 1)) ((K : ℝ) / ((n : ℝ) + 1))
  have hgrid : Monotone (grid n) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (by positivity)
  have hIndep : iIndepFun (fun (i : Fin 3) ↦ increment B n (k + i)) P := by
    have h := (hB.hasIndepIncrements.nat hgrid).comp
      (fun _ (x : ℝ) ↦ ((n : ℝ) + 1) * x) (fun _ ↦ measurable_const.mul measurable_id)
    exact h.precomp (g := fun i : Fin 3 ↦ k + (i : ℕ))
      (fun _ _ heq ↦ Fin.ext (Nat.add_left_cancel heq))
  have hmul :
      P (⋂ i : Fin 3, increment B n (k + i) ⁻¹' I) =
        ∏ i : Fin 3, P (increment B n (k + i) ⁻¹' I) := by
    simpa using hIndep.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun _ ↦ I) (fun _ _ ↦ measurableSet_Icc)
  have hsingle (j : ℕ) : P (increment B n j ⁻¹' I) ≤
      ENNReal.ofReal (2 * K / ((n : ℝ) + 1)) := by
    have hlaw := hasLaw_increment hB n j
    rw [← Measure.map_apply_of_aemeasurable hlaw.aemeasurable
      (show MeasurableSet I from measurableSet_Icc), hlaw.map_eq]
    refine (gaussianReal_zero_one_le_volume I).trans ?_
    dsimp only [I]
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  calc
    P (smallIncrements B K n k) = ∏ i : Fin 3, P (increment B n (k + i) ⁻¹' I) := hmul
    _ ≤ ∏ _ : Fin 3, ENNReal.ofReal (2 * K / ((n : ℝ) + 1)) :=
      Finset.prod_le_prod fun i _ ↦ hsingle (k + i)
    _ = _ := by simp

private noncomputable def smallIncrementsOnGrid (B : ℝ≥0 → Ω → ℝ) (T K n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range (T * (n + 1) ^ 2), smallIncrements B K n k

private lemma measure_smallIncrementsOnGrid (hB : IsPreBrownianReal B P) (T K n : ℕ) :
    P (smallIncrementsOnGrid B T K n) ≤
      ENNReal.ofReal ((T : ℝ) * (2 * K) ^ 3 / ((n : ℝ) + 1)) := by
  calc
    P (smallIncrementsOnGrid B T K n) ≤
        ∑ k ∈ Finset.range (T * (n + 1) ^ 2), P (smallIncrements B K n k) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _ ∈ Finset.range (T * (n + 1) ^ 2),
          ENNReal.ofReal (2 * K / ((n : ℝ) + 1)) ^ 3 :=
      Finset.sum_le_sum fun k _ ↦ measure_smallIncrements hB K n k
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      push_cast
      congr 1
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp

private lemma tendsto_div_nat_add_one (c : ℝ) :
    Tendsto (fun n : ℕ ↦ c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 1)

-- This uses the outer measure bound, so no measurability of the differentiability event is needed.
private lemma ae_exists_goodGrid (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ T K N : ℕ, ∃ n ≥ N, ω ∉ smallIncrementsOnGrid B T K n := by
  simp only [ae_all_iff]
  intro T K N
  rw [ae_iff]
  apply nonpos_iff_eq_zero.mp
  have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((T : ℝ) * (2 * K) ^ 3 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_div_nat_add_one _)
  apply ge_of_tendsto ht
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (measure_mono ?_).trans (measure_smallIncrementsOnGrid hB T K n)
  intro ω hω
  by_contra h
  exact hω ⟨n, hn, h⟩

private lemma grid_near (t : ℝ) (ht : 0 ≤ t) {T : ℕ} (hT : t < T) (n : ℕ) :
    ∃ k < T * (n + 1) ^ 2, ∀ j : ℕ, j ≤ 3 →
      |(grid n (k + j) : ℝ) - t| ≤ 3 * (mesh n : ℝ) := by
  let q : ℝ := ((n : ℝ) + 1) ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hmesh : (mesh n : ℝ) = 1 / q := by simp [mesh, q]
  let k := ⌊t * q⌋₊
  have hlo : (k : ℝ) ≤ t * q := Nat.floor_le (mul_nonneg ht hq.le)
  have hhi : t * q < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk : k < T * (n + 1) ^ 2 := by
    have h : (k : ℝ) < (T : ℝ) * q := hlo.trans_lt (mul_lt_mul_of_pos_right hT hq)
    dsimp only [q] at h
    exact_mod_cast h
  refine ⟨k, hk, fun j hj ↦ ?_⟩
  rw [coe_grid, Nat.cast_add, hmesh, mul_one_div, mul_one_div]
  have hj' : (j : ℝ) ≤ 3 := by exact_mod_cast hj
  have hj₀ : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hd : |(k : ℝ) + j - t * q| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    |((k : ℝ) + j) / q - t| = |((k : ℝ) + j - t * q) / q| := by
      rw [sub_div, mul_div_cancel_right₀ _ hq.ne']
    _ = |(k : ℝ) + j - t * q| / q := by rw [abs_div, abs_of_pos hq]
    _ ≤ 3 / q := (div_le_div_iff_of_pos_right hq).2 hd

omit [MeasurableSpace Ω] in
private lemma differentiable_mem_smallIncrementsOnGrid {ω : Ω} {t : ℝ} (ht : 0 ≤ t)
    (hd : DifferentiableAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) t) :
    ∃ T K N : ℕ, ∀ n ≥ N, ω ∈ smallIncrementsOnGrid B T K n := by
  obtain ⟨T, hT⟩ := exists_nat_gt t
  obtain ⟨C, hC⟩ := hd.isBigO_sub.bound
  obtain ⟨K, hK⟩ := exists_nat_gt (6 * |C|)
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp hC
  have hmesh_tendsto : Tendsto (fun n : ℕ ↦ 3 * (mesh n : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_div_nat_add_one 1).pow 2 |>.const_mul (3 : ℝ)
    simpa [mesh, div_pow] using h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmesh_tendsto.eventually_lt_const hε)
  refine ⟨T, K, N, fun n hn ↦ ?_⟩
  obtain ⟨k, hk, hnear⟩ := grid_near t ht hT n
  refine mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hk, mem_iInter.mpr fun i ↦ ?_⟩
  have habs (j : ℕ) (hj : j ≤ 3) :
      |B (grid n (k + j)) ω - B t.toNNReal ω| ≤
        |C| * (3 * (mesh n : ℝ)) := by
    have hdist := hnear j hj
    have hball : dist (grid n (k + j) : ℝ) t < ε := by
      rw [Real.dist_eq]
      exact hdist.trans_lt (hN n hn)
    have h := hlocal hball
    simp only [Real.norm_eq_abs, Real.toNNReal_coe] at h
    exact h.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hdist (abs_nonneg _)))
  have hi := habs i (by omega)
  have hi' := habs ((i : ℕ) + 1) (by omega)
  have hinc : |B (grid n (k + i + 1)) ω - B (grid n (k + i)) ω| ≤
      (K : ℝ) * (mesh n : ℝ) := by
    rw [Nat.add_assoc]
    calc
      _ ≤ |B (grid n (k + (i + 1))) ω - B t.toNNReal ω| +
          |B (grid n (k + i)) ω - B t.toNNReal ω| := by
        simpa only [Real.dist_eq] using dist_triangle_right
          (B (grid n (k + (i + 1))) ω) (B (grid n (k + i)) ω) (B t.toNNReal ω)
      _ ≤ (6 * |C|) * (mesh n : ℝ) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hK.le (NNReal.coe_nonneg _)
  have hnorm : |increment B n (k + i) ω| ≤ (K : ℝ) / ((n : ℝ) + 1) := by
    have hn' : 0 < (n : ℝ) + 1 := by positivity
    rw [increment, abs_mul, abs_of_pos hn']
    refine (mul_le_mul_of_nonneg_left hinc hn'.le).trans_eq ?_
    simp only [mesh, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, NNReal.coe_add,
      NNReal.coe_natCast]
    field_simp
  have h := abs_le.mp hnorm
  exact ⟨by simpa only [neg_div] using h.1, h.2⟩

end

/-- **Brownian paths are nowhere differentiable** (Paley, Wiener and Zygmund). Almost surely, the
path `s ↦ B s ω` is differentiable at no time `t > 0` (Mörters and Peres, *Brownian Motion*,
Cambridge University Press, 2010, Theorem 1.30). The statement is restricted to `t > 0` because
the path is extended by `B 0` to negative times, so a two-sided derivative at `0` is not the
Brownian one. -/
public theorem IsBrownianReal.ae_not_differentiableAt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ¬ DifferentiableAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) t := by
  filter_upwards [ae_exists_goodGrid hB.toIsPreBrownianReal] with ω hω t ht hd
  obtain ⟨T, K, N, h⟩ := differentiable_mem_smallIncrementsOnGrid ht.le hd
  obtain ⟨n, hn, hnot⟩ := hω T K N
  exact hnot (h n hn)

end MathlibExt.Probability.BrownianSamplePathsWanted
