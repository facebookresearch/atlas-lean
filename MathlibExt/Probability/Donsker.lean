/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FunProp
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import MathlibExt.Probability.ContinuousPathConvergence
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.ContinuousPathConvergence
open scoped ENNReal NNReal ProbabilityTheory Real

namespace MathlibExt.Probability.DonskerWanted

/-!
# Donsker's invariance principle

This file proves the functional CLT: polygonal partial-sum processes converge in
`C([0,1],ℝ)` to Brownian motion.
-/

noncomputable section

/-- Clamps a real to `[0,1]`. -/
noncomputable def donskerClamp (x : ℝ) : ℝ :=
  min (max x 0) 1

/-- Weight `t ↦ clamp(n·t - i)` for the polygonal interpolation. -/
noncomputable def donskerWeight (n i : ℕ) (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  donskerClamp ((n : ℝ) * t.val - (i : ℝ))

/-- Bundled continuous version of `donskerWeight` in `C([0,1],ℝ)`. -/
noncomputable def donskerWeightCM (n i : ℕ) : C(Set.Icc (0 : ℝ) 1, ℝ) where
  toFun := donskerWeight n i
  continuous_toFun := by
    unfold donskerWeight donskerClamp
    have h_val : Continuous (fun t : Set.Icc (0 : ℝ) 1 => (t.val : ℝ)) :=
      continuous_subtype_val
    have h_lin : Continuous (fun t : Set.Icc (0 : ℝ) 1 => (n : ℝ) * t.val - (i : ℝ)) := by
      fun_prop
    have h_clamp : Continuous (fun x : ℝ => min (max x 0) 1) := by
      fun_prop
    exact h_clamp.comp h_lin

private lemma donskerWeight_eq_one_of_lt_floor (n i : ℕ) (t : Set.Icc (0 : ℝ) 1)
    (hi : i < Nat.floor ((n : ℝ) * t.1)) : donskerWeight n i t = 1 := by
  have ha0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg (Nat.cast_nonneg n) t.2.1
  have hi' : (i : ℝ) + 1 ≤ (n : ℝ) * t.1 := by
    calc
      (i : ℝ) + 1 = ((i + 1 : ℕ) : ℝ) := by norm_num
      _ ≤ (Nat.floor ((n : ℝ) * t.1) : ℝ) := by exact_mod_cast hi
      _ ≤ (n : ℝ) * t.1 := Nat.floor_le ha0
  have hweight : 1 ≤ (n : ℝ) * t.1 - (i : ℝ) := by linarith
  simp [donskerWeight, donskerClamp, max_eq_left (le_trans zero_le_one hweight),
    min_eq_right hweight]

private lemma donskerWeight_floor (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    donskerWeight n (Nat.floor ((n : ℝ) * t.1)) t =
      (n : ℝ) * t.1 - Nat.floor ((n : ℝ) * t.1) := by
  have ha0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg (Nat.cast_nonneg n) t.2.1
  have hfrac0 := Nat.zero_le_self_sub_floor ha0
  have hfrac1 := (Nat.self_sub_floor_lt_one ((n : ℝ) * t.1)).le
  simp [donskerWeight, donskerClamp, max_eq_left hfrac0, min_eq_left hfrac1]

private lemma donskerWeight_eq_zero_of_floor_lt (n i : ℕ) (t : Set.Icc (0 : ℝ) 1)
    (hi : Nat.floor ((n : ℝ) * t.1) < i) : donskerWeight n i t = 0 := by
  have ha0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg (Nat.cast_nonneg n) t.2.1
  have hi' : (n : ℝ) * t.1 < (i : ℝ) := (Nat.floor_lt ha0).mp hi
  have hweight : (n : ℝ) * t.1 - (i : ℝ) ≤ 0 := by linarith
  simp [donskerWeight, donskerClamp, max_eq_right hweight]

private lemma donsker_weighted_sum_eq {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω)
    (t : Set.Icc (0 : ℝ) 1) :
    (∑ i ∈ Finset.range n, X i ω * donskerWeight n i t) =
      (∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * t.1)), X i ω) +
        if Nat.floor ((n : ℝ) * t.1) < n then
          X (Nat.floor ((n : ℝ) * t.1)) ω *
            ((n : ℝ) * t.1 - Nat.floor ((n : ℝ) * t.1))
        else 0 := by
  let m := Nat.floor ((n : ℝ) * t.1)
  have ha_le : (n : ℝ) * t.1 ≤ (n : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left t.2.2 (Nat.cast_nonneg n)
  have hm_le : m ≤ n := Nat.floor_le_of_le ha_le
  have hprefix : (∑ i ∈ Finset.range m, X i ω * donskerWeight n i t) =
      ∑ i ∈ Finset.range m, X i ω := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [donskerWeight_eq_one_of_lt_floor n i t (Finset.mem_range.mp hi)]
    simp
  by_cases hm_lt : m < n
  · have htail : (∑ i ∈ Finset.Ico (m + 1) n, X i ω * donskerWeight n i t) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [donskerWeight_eq_zero_of_floor_lt n i t]
      · simp
      · exact (Nat.succ_le_iff.mp (Finset.mem_Ico.mp hi).1)
    rw [← Finset.sum_range_add_sum_Ico (fun i => X i ω * donskerWeight n i t) hm_le,
      Finset.sum_eq_sum_Ico_succ_bot hm_lt, hprefix, donskerWeight_floor, htail]
    simp [m, hm_lt]
  · have hm_eq : m = n := le_antisymm hm_le (not_lt.mp hm_lt)
    change (∑ i ∈ Finset.range n, X i ω * donskerWeight n i t) =
      (∑ i ∈ Finset.range m, X i ω) +
        if m < n then X m ω * ((n : ℝ) * t.1 - m) else 0
    simp only [hm_lt, ↓reduceIte, add_zero]
    simpa [hm_eq] using hprefix

/-- Polygonal normalized partial-sum process as a `C([0,1],ℝ)`-valued variable. -/
noncomputable def donskerProcess {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    C(Set.Icc (0 : ℝ) 1, ℝ) :=
  if n = 0 then 0
  else
    let sqrtInv : ℝ := (Real.sqrt (n : ℝ))⁻¹
    sqrtInv • (Finset.sum (Finset.range n) fun i => (X i ω) • donskerWeightCM n i)

/-- Explicit partial-sum interpolation formula for `donskerProcess`. -/
public theorem donskerProcess_apply_eq {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω)
    (t : Set.Icc (0 : ℝ) 1) (hn : n ≠ 0) :
    donskerProcess n X ω t =
      ((∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * t.1)), X i ω) +
        if Nat.floor ((n : ℝ) * t.1) < n then
          X (Nat.floor ((n : ℝ) * t.1)) ω *
            ((n : ℝ) * t.1 - Nat.floor ((n : ℝ) * t.1))
        else 0) / Real.sqrt (n : ℝ) := by
  simp only [donskerProcess, hn, ↓reduceIte]
  simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply]
  change (Real.sqrt (n : ℝ))⁻¹ *
      (∑ i ∈ Finset.range n, X i ω * donskerWeight n i t) = _
  rw [donsker_weighted_sum_eq]
  ring

private lemma donskerProcess_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (fun ω => donskerProcess n X ω) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  by_cases hn : n = 0
  · simp [donskerProcess, hn]
  · simp only [donskerProcess, hn, ↓reduceIte, ContinuousMap.smul_apply,
      ContinuousMap.sum_apply]
    fun_prop

/-- Inclusion of `Set.Icc 0 1` into `ℝ≥0`. -/
noncomputable def iccToNNReal (t : Set.Icc (0 : ℝ) 1) : ℝ≥0 :=
  ⟨t.val, t.2.1⟩

private lemma continuous_iccToNNReal : Continuous iccToNNReal := by
  exact continuous_subtype_val.subtype_mk _

private noncomputable def donskerBrownianPath {Ω' : Type*} (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    C(Set.Icc (0 : ℝ) 1, ℝ) := by
  classical
  exact if h : Continuous (fun t : Set.Icc (0 : ℝ) 1 => B (iccToNNReal t) ω) then
    ⟨fun t => B (iccToNNReal t) ω, h⟩ else 0

private lemma donskerBrownianPath_apply_of_continuous {Ω' : Type*}
    (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') (hω : Continuous (fun s => B s ω))
    (t : Set.Icc (0 : ℝ) 1) :
    donskerBrownianPath B ω t = B (iccToNNReal t) ω := by
  have h : Continuous (fun t : Set.Icc (0 : ℝ) 1 => B (iccToNNReal t) ω) :=
    hω.comp continuous_iccToNNReal
  simp [donskerBrownianPath, h]

private noncomputable def donskerBrownianApproximation {Ω' : Type*} (n : ℕ)
    (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ∑ k : Fin (n + 1), bernstein n k •
    ContinuousMap.const _ (B (iccToNNReal (bernstein.z k)) ω)

private lemma donskerBrownianApproximation_aemeasurable {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} (B : ℝ≥0 → Ω' → ℝ) (hB : IsPreBrownianReal B P') (n : ℕ) :
    AEMeasurable (donskerBrownianApproximation n B) P' := by
  let hcoeff (k : Fin (n + 1)) := hB.aemeasurable (iccToNNReal (bernstein.z k))
  let coeff (k : Fin (n + 1)) := (hcoeff k).mk (B (iccToNNReal (bernstein.z k)))
  let g (ω : Ω') : C(Set.Icc (0 : ℝ) 1, ℝ) :=
    ∑ k : Fin (n + 1), bernstein n k • ContinuousMap.const _ (coeff k ω)
  refine ⟨g, ?_, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.2
    intro t
    simp only [g, ContinuousMap.sum_apply]
    fun_prop
  · have hcoeff_ae : ∀ᵐ ω ∂P', ∀ k : Fin (n + 1),
        coeff k ω = B (iccToNNReal (bernstein.z k)) ω :=
      ae_all_iff.2 fun k => (hcoeff k).ae_eq_mk.symm
    filter_upwards [hcoeff_ae] with ω hω
    unfold donskerBrownianApproximation
    apply Finset.sum_congr rfl
    intro k _
    rw [hω k]

private lemma donskerBrownianApproximation_eq_bernstein {Ω' : Type*} (n : ℕ)
    (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') (hω : Continuous (fun s => B s ω)) :
    donskerBrownianApproximation n B ω =
      bernsteinApproximation n (donskerBrownianPath B ω) := by
  unfold donskerBrownianApproximation bernsteinApproximation
  apply Finset.sum_congr rfl
  intro k _
  rw [donskerBrownianPath_apply_of_continuous B ω hω]

private lemma donskerBrownianApproximation_tendsto {Ω' : Type*}
    (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') (hω : Continuous (fun s => B s ω)) :
    Filter.Tendsto (fun n => donskerBrownianApproximation n B ω) Filter.atTop
      (𝓝 (donskerBrownianPath B ω)) := by
  simpa only [donskerBrownianApproximation_eq_bernstein (B := B) (ω := ω) (hω := hω)] using
    bernsteinApproximation_uniform (donskerBrownianPath B ω)

private lemma donskerBrownianPath_aemeasurable {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    AEMeasurable (donskerBrownianPath B) P' := by
  apply aemeasurable_of_tendsto_metrizable_ae'
    (fun n => donskerBrownianApproximation_aemeasurable B hB.toIsPreBrownianReal n)
  filter_upwards [hB.cont] with ω hω
  exact donskerBrownianApproximation_tendsto B ω hω

private lemma donskerBrownianPath_ae_eq {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    ∀ᵐ ω ∂P', ∀ t : Set.Icc (0 : ℝ) 1,
      donskerBrownianPath B ω t = B (iccToNNReal t) ω := by
  filter_upwards [hB.cont] with ω hω
  exact fun t => donskerBrownianPath_apply_of_continuous B ω hω t

/-- Local Borel structures for `C(Icc 0 1, ℝ)`, scoped to avoid orphan leakage. -/
scoped instance instMeasurableSpaceContinuousMap : MeasurableSpace C(Set.Icc (0 : ℝ) 1, ℝ) :=
  borel _

scoped instance instBorelSpaceContinuousMap : BorelSpace C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨rfl⟩

/-- Probability measures on `C([0,1], ℝ)` are determined by their finite-dimensional
distributions. Compatibility wrapper around
`MathlibExt.Probability.ContinuousPathConvergence.continuousPath_measure_ext_of_finset_eval`
at `T = 1`; the projective-limit argument lives there, not here. -/
public theorem continuousMap_measure_ext_of_finset_eval
    (μ ν : Measure C(Set.Icc (0 : ℝ) 1, ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ I : Finset (Set.Icc (0 : ℝ) 1),
      μ.map (fun f => I.restrict (fun t => f t)) =
        ν.map (fun f => I.restrict (fun t => f t))) : μ = ν := by
  let μ' : ProbabilityMeasure C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨μ, inferInstance⟩
  let ν' : ProbabilityMeasure C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨ν, inferInstance⟩
  have h' : ∀ I : Finset (Set.Icc (0 : ℝ) 1),
      μ'.map (fun f => I.restrict (fun t => f t)) =
        ν'.map (fun f => I.restrict (fun t => f t)) := by
    intro I
    apply ProbabilityMeasure.toMeasure_injective
    exact h I
  exact congrArg ProbabilityMeasure.toMeasure
    (continuousPath_measure_ext_of_finset_eval 1 μ' ν' h')

private lemma second_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → ℝ) (hX : AEMeasurable X P) (hmean : P[X] = 0) (hvar : Var[X; P] = 1) :
    P[X ^ 2] = 1 := by
  rw [← hvar, variance_eq_integral hX]
  simp [hmean]

private def bsize (a b : ℝ) (n : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) * b) - Nat.floor ((n : ℝ) * a)

private def bsum {Ω : Type*} (a b : ℝ) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ *
    ∑ i ∈ Finset.range (bsize a b n), X (Nat.floor ((n : ℝ) * a) + i) ω

private lemma bsum_eq_sub {Ω : Type*} (a b : ℝ) (hab : a ≤ b)
    (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    bsum a b n X ω = (Real.sqrt (n : ℝ))⁻¹ *
      ((∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * b)), X i ω) -
        ∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * a)), X i ω) := by
  have hfloor : Nat.floor ((n : ℝ) * a) ≤ Nat.floor ((n : ℝ) * b) :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n))
  have hshift :
      (∑ i ∈ Finset.range
          (Nat.floor ((n : ℝ) * b) - Nat.floor ((n : ℝ) * a)),
          X (Nat.floor ((n : ℝ) * a) + i) ω) =
        ∑ i ∈ Finset.Ico (Nat.floor ((n : ℝ) * a)) (Nat.floor ((n : ℝ) * b)), X i ω :=
    (Finset.sum_Ico_eq_sum_range (fun i => X i ω)
      (Nat.floor ((n : ℝ) * a)) (Nat.floor ((n : ℝ) * b))).symm
  rw [bsum, bsize, hshift, Finset.sum_Ico_eq_sub (fun i => X i ω) hfloor]

private lemma floor_mul_div_tendsto (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (Nat.floor ((n : ℝ) * t) : ℝ) / (n : ℝ)) atTop (𝓝 t) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun n : ℕ => t - ((n : ℝ))⁻¹) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlt : (n : ℝ) * t < (Nat.floor ((n : ℝ) * t) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [inv_eq_one_div]
    apply (sub_le_iff_le_add).2
    rw [← add_div, le_div_iff₀ hnR]
    nlinarith
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hfl : (Nat.floor ((n : ℝ) * t) : ℝ) ≤ (n : ℝ) * t :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) ht)
    rw [div_le_iff₀ hnR]
    nlinarith

private lemma bsize_ratio_tendsto (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => (bsize a b n : ℝ) / (n : ℝ)) atTop (𝓝 (b - a)) := by
  have hfloor (n : ℕ) : Nat.floor ((n : ℝ) * a) ≤ Nat.floor ((n : ℝ) * b) :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n))
  have heq (n : ℕ) : (bsize a b n : ℝ) / (n : ℝ) =
      (Nat.floor ((n : ℝ) * b) : ℝ) / (n : ℝ) -
        (Nat.floor ((n : ℝ) * a) : ℝ) / (n : ℝ) := by
    rw [bsize, Nat.cast_sub (hfloor n)]
    ring
  simp_rw [heq]
  exact (floor_mul_div_tendsto b (ha.trans hab)).sub (floor_mul_div_tendsto a ha)

private lemma bsize_tendsto_atTop (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (bsize a b) atTop atTop := by
  have hratio := bsize_ratio_tendsto a b ha hab.le
  rw [tendsto_atTop]
  intro K
  have hd : 0 < b - a := sub_pos.mpr hab
  have hevent_ratio : ∀ᶠ n : ℕ in atTop,
      (b - a) / 2 < (bsize a b n : ℝ) / (n : ℝ) :=
    hratio.eventually (Ioi_mem_nhds (half_lt_self hd))
  have hevent_n : ∀ᶠ n : ℕ in atTop, (2 * K : ℝ) / (b - a) < n :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hevent_ratio, hevent_n, eventually_gt_atTop (0 : ℕ)] with n hr hn hn0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hK : (K : ℝ) < (bsize a b n : ℕ) := by
    have hmul : (K : ℝ) < ((b - a) / 2) * n := by
      rw [div_lt_iff₀ hd] at hn
      nlinarith
    have hprod := mul_lt_mul_of_pos_right hr hnR
    rw [div_mul_cancel₀ _ hnR.ne'] at hprod
    exact hmul.trans hprod
  exact_mod_cast hK.le

private lemma tid_reindex
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {W : ℕ → Ω → E} {Y : Ω' → E}
    (h : TendstoInDistribution W atTop Y (fun _ => P) P')
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    TendstoInDistribution (fun n => W (m n)) atTop Y (fun _ => P) P' where
  forall_aemeasurable n := h.forall_aemeasurable (m n)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hm

private lemma tid_of_identDistrib
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {W V : ℕ → Ω → E} {Y : Ω' → E}
    (h : TendstoInDistribution W atTop Y (fun _ => P) P')
    (hWV : ∀ n, IdentDistrib (W n) (V n) P P) :
    TendstoInDistribution V atTop Y (fun _ => P) P' where
  forall_aemeasurable n := (hWV n).aemeasurable_snd
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := by
    refine h.tendsto.congr' (.of_forall fun n => ?_)
    apply Subtype.ext
    exact (hWV n).map_eq

private lemma shifted_ident
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (start m : ℕ) :
    IdentDistrib
      (fun ω => ∑ i ∈ Finset.range m, X (start + i) ω)
      (fun ω => ∑ i ∈ Finset.range m, X i ω) P P := by
  let A : Fin m → Ω → ℝ := fun i => X (start + i)
  let C : Fin m → Ω → ℝ := fun i => X i
  have hcomp : ∀ i : Fin m, IdentDistrib (A i) (C i) P P := by
    intro i
    exact (hIdent (start + i)).trans (hIdent i).symm
  have hA : iIndepFun A P := by
    exact hIndep.precomp (fun _ _ h => Fin.ext (Nat.add_left_cancel h))
  have hC : iIndepFun C P := by
    exact hIndep.precomp Fin.val_injective
  have hpi := IdentDistrib.pi hcomp hA hC
  have hsum := hpi.comp (u := fun z : Fin m → ℝ => ∑ i, z i) (by fun_prop)
  convert hsum using 1 <;> ext ω
  · exact (Fin.sum_univ_eq_sum_range (fun i => X (start + i) ω) m).symm
  · exact (Fin.sum_univ_eq_sum_range (fun i => X i ω) m).symm

private lemma normalized_brownian_increment_hasLaw
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsPreBrownianReal B P')
    (a b : ℝ≥0) (hab : a < b) :
    HasLaw (fun ω => (B b ω - B a ω) / Real.sqrt ((b : ℝ) - (a : ℝ)))
      (gaussianReal 0 1) P' := by
  have hd : 0 < (b : ℝ) - (a : ℝ) := sub_pos.mpr (by exact_mod_cast hab)
  have hinc := hB.hasLaw_sub b a
  convert gaussianReal_div_const hinc (Real.sqrt ((b : ℝ) - (a : ℝ))) using 1
  congr 2
  · simp
  · ext
    simp [Real.dist_eq, abs_of_nonneg hd.le, Real.sq_sqrt hd.le, hd.ne']

private lemma bsum_tendstoInDistribution_of_lt
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsPreBrownianReal B P')
    (a b : ℝ≥0) (hab : a < b) :
    TendstoInDistribution (fun n => bsum a b n X) atTop (B b - B a)
      (fun _ => P) P' := by
  let d : ℝ := (b : ℝ) - (a : ℝ)
  let G : Ω' → ℝ := fun ω => (B b ω - B a ω) / Real.sqrt d
  let W : ℕ → Ω → ℝ := fun m ω =>
    (Real.sqrt (m : ℝ))⁻¹ * ∑ i ∈ Finset.range m, X i ω
  let m : ℕ → ℕ := bsize a b
  let r : ℕ → ℝ := fun n => Real.sqrt (m n : ℝ) / Real.sqrt (n : ℝ)
  have ha : 0 ≤ (a : ℝ) := a.2
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hd : 0 < d := sub_pos.mpr habR
  have hsecond : P[(X 0) ^ 2] = 1 :=
    second_moment (X 0) (hIdent 0).aemeasurable_fst hMean hVar
  have hG : HasLaw G (gaussianReal 0 1) P' := by
    exact normalized_brownian_increment_hasLaw B hB a b hab
  have hclt : TendstoInDistribution W atTop G (fun _ => P) P' := by
    exact tendstoInDistribution_inv_sqrt_mul_sum hG hMean hsecond hIndep hIdent
  have hm : Tendsto m atTop atTop := bsize_tendsto_atTop a b ha habR
  have hsub : TendstoInDistribution (fun n => W (m n)) atTop G (fun _ => P) P' :=
    tid_reindex hclt m hm
  have hratio : Tendsto (fun n => (m n : ℝ) / (n : ℝ)) atTop (𝓝 d) :=
    bsize_ratio_tendsto a b ha habR.le
  have hr : Tendsto r atTop (𝓝 (Real.sqrt d)) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
    have heq : r = fun n => Real.sqrt ((m n : ℝ) / (n : ℝ)) := by
      funext n
      exact (Real.sqrt_div (Nat.cast_nonneg (m n)) (n : ℝ)).symm
    rw [heq]
    exact hsqrt
  have hrMeasure : TendstoInMeasure P (fun n _ω => r n) atTop (fun _ω => Real.sqrt d) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      fun_prop
    · exact .of_forall fun _ω => hr
  have hmul : TendstoInDistribution (fun n ω => r n * W (m n) ω) atTop
      (fun ω => Real.sqrt d * G ω) (fun _ => P) P' := by
    exact hsub.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) hrMeasure (fun _ => by fun_prop)
  have hprefix : TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range (m n), X i ω)
      atTop (B b - B a) (fun _ => P) P' := by
    refine hmul.congr (fun n => .of_forall fun ω => ?_) (.of_forall fun ω => ?_)
    · dsimp [r, W]
      by_cases hn : n = 0
      · simp [hn]
      by_cases hmm : m n = 0
      · simp [hmm]
      have hnR : Real.sqrt (n : ℝ) ≠ 0 := by positivity
      have hmR : Real.sqrt (m n : ℝ) ≠ 0 := by positivity
      field_simp
    · dsimp [G]
      field_simp [Real.sqrt_ne_zero'.mpr hd]
  apply tid_of_identDistrib hprefix
  intro n
  exact ((shifted_ident X hIndep hIdent (Nat.floor ((n : ℝ) * (a : ℝ))) (m n)).symm.comp
    (u := fun z : ℝ => (Real.sqrt (n : ℝ))⁻¹ * z) (by fun_prop))

private lemma bsum_tendstoInDistribution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsPreBrownianReal B P')
    (a b : ℝ≥0) (hab : a ≤ b) :
    TendstoInDistribution (fun n => bsum a b n X) atTop (B b - B a)
      (fun _ => P) P' := by
  obtain rfl | hab := hab.eq_or_lt
  · have hconst : TendstoInDistribution (fun _n : ℕ => fun _ω : Ω => (0 : ℝ)) atTop
        (fun _ω : Ω' => (0 : ℝ)) (fun _ => P) P' := by
      apply tendstoInDistribution_of_identDistrib 0
      · intro n
        exact ⟨by fun_prop, by fun_prop, by simp⟩
      · exact ⟨by fun_prop, by fun_prop, by simp⟩
    refine hconst.congr (fun n => .of_forall fun ω => ?_) (.of_forall fun ω => ?_)
    · simp [bsum, bsize]
    · simp
  · exact bsum_tendstoInDistribution_of_lt X hIndep hIdent hMean hVar B hB a b hab

private noncomputable def blockVec {d : ℕ} {Ω : Type*}
    (u : Fin (d + 1) → ℝ≥0) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => bsum (u j.castSucc) (u j.succ) n X ω)

private noncomputable def brownianBlockVec {d : ℕ} {Ω' : Type*}
    (u : Fin (d + 1) → ℝ≥0) (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => B (u j.succ) ω - B (u j.castSucc) ω)

private lemma indepFun_blockVec_bsum
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (u : Fin (d + 2) → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    IndepFun
      (blockVec (fun i : Fin (d + 1) => u i.castSucc) n X)
      (bsum (u (Fin.last d).castSucc) (u (Fin.last d).succ) n X) P := by
  let q : Fin (d + 2) := (Fin.last d).castSucc
  let start : ℕ := Nat.floor ((n : ℝ) * (u q : ℝ))
  let finish : ℕ := Nat.floor ((n : ℝ) * (u (Fin.last d).succ : ℝ))
  let S : Finset ℕ := Finset.range start
  let T : Finset ℕ := Finset.Ico start finish
  have hq : q ≤ (Fin.last d).succ := by
    exact Fin.le_last q
  have hstartfinish : start ≤ finish := by
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left
      (mod_cast hu hq) (Nat.cast_nonneg n))
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    have hiS' : i < start := Finset.mem_range.mp hiS
    have hiT' : start ≤ i := (Finset.mem_Ico.mp hiT).1
    omega
  have hraw : IndepFun
      (fun ω (i : S) => X i ω) (fun ω (i : T) => X i ω) P :=
    hIndep.indepFun_finset S T hST hMeas
  let φ : (S → ℝ) → EuclideanSpace ℝ (Fin d) := fun z =>
    WithLp.toLp 2 (fun j =>
      (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i : Fin (bsize (u j.castSucc.castSucc) (u j.succ.castSucc) n),
          z ⟨Nat.floor ((n : ℝ) * (u j.castSucc.castSucc : ℝ)) + i, by
            have hj : j.succ.castSucc ≤ q := by
              simp [q]
            have hend : Nat.floor ((n : ℝ) * (u j.succ.castSucc : ℝ)) ≤ start := by
              exact Nat.floor_mono (mul_le_mul_of_nonneg_left
                (mod_cast hu hj) (Nat.cast_nonneg n))
            have habj : Nat.floor ((n : ℝ) * (u j.castSucc.castSucc : ℝ)) ≤
                Nat.floor ((n : ℝ) * (u j.succ.castSucc : ℝ)) := by
              exact Nat.floor_mono (mul_le_mul_of_nonneg_left
                (mod_cast hu (by
                  apply Fin.mk_le_mk.mpr
                  simp)) (Nat.cast_nonneg n))
            have hi : (i : ℕ) <
                Nat.floor ((n : ℝ) * (u j.succ.castSucc : ℝ)) -
                  Nat.floor ((n : ℝ) * (u j.castSucc.castSucc : ℝ)) := by
              simpa [bsize] using i.isLt
            exact Finset.mem_range.mpr (by omega)⟩)
  let ψ : (T → ℝ) → ℝ := fun z =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ∑ i : Fin (finish - start),
        z ⟨start + i, by
          rw [Finset.mem_Ico]
          have hi := i.isLt
          omega⟩
  have hcomp : IndepFun
      (φ ∘ fun ω (i : S) => X i ω)
      (ψ ∘ fun ω (i : T) => X i ω) P := by
    apply hraw.comp
    · dsimp [φ]
      fun_prop
    · dsimp [ψ]
      fun_prop
  refine hcomp.congr (.of_forall fun ω => ?_) (.of_forall fun ω => ?_)
  · simp only [Function.comp_apply, blockVec, φ, bsum]
    congr 1
    funext j
    rw [Fin.sum_univ_eq_sum_range
      (fun i => X (Nat.floor ((n : ℝ) * (u j.castSucc.castSucc : ℝ)) + i) ω)
      (bsize (u j.castSucc.castSucc) (u j.succ.castSucc) n)]
  · simp only [Function.comp_apply, bsum, ψ]
    have hsize : bsize (u q) (u (Fin.last d).succ) n = finish - start := by
      rfl
    rw [hsize]
    rw [Fin.sum_univ_eq_sum_range (fun i => X (start + i) ω) (finish - start)]

private lemma indepFun_brownian_blockVec_sub
    {d : ℕ} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsPreBrownianReal B P')
    (u : Fin (d + 2) → ℝ≥0) (hu : Monotone u) :
    IndepFun
      (brownianBlockVec (fun i : Fin (d + 1) => u i.castSucc) B)
      (B (u (Fin.last d).succ) - B (u (Fin.last d).castSucc)) P' := by
  let V : Fin (d + 1) → Ω' → ℝ := fun j => B (u j.succ) - B (u j.castSucc)
  let S : Finset (Fin (d + 1)) := Finset.univ.image Fin.castSucc
  let T : Finset (Fin (d + 1)) := {(Fin.last d)}
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    rw [Finset.mem_singleton] at hiT
    subst i
    simp only [S, Finset.mem_image] at hiS
    obtain ⟨j, _, hj⟩ := hiS
    exact Fin.castSucc_ne_last j hj
  have hV : ∀ j, AEMeasurable (V j) P' := fun j =>
    (hB.aemeasurable _).sub (hB.aemeasurable _)
  have hInc : iIndepFun V P' := hB.hasIndepIncrements (d + 1) u hu
  have hraw : IndepFun
      (fun ω (i : S) => V i ω) (fun ω (i : T) => V i ω) P' :=
    hInc.indepFun_finset₀ S T hST hV
  let φ : (S → ℝ) → EuclideanSpace ℝ (Fin d) := fun z =>
    WithLp.toLp 2 (fun j => z ⟨j.castSucc, by
      simp only [S, Finset.mem_image]
      exact ⟨j, Finset.mem_univ _, rfl⟩⟩)
  let ψ : (T → ℝ) → ℝ := fun z => z ⟨Fin.last d, Finset.mem_singleton_self _⟩
  have hcomp : IndepFun
      (φ ∘ fun ω (i : S) => V i ω)
      (ψ ∘ fun ω (i : T) => V i ω) P' := by
    apply hraw.comp
    · dsimp [φ]
      fun_prop
    · dsimp [ψ]
      fun_prop
  refine hcomp.congr (.of_forall fun ω => ?_) (.of_forall fun ω => ?_)
  · simp only [Function.comp_apply, brownianBlockVec, φ, V]
    congr 1
  · rfl

private lemma tid_pair_of_indep
    {Ω Ω' E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (X : ℕ → Ω → E) (Y : ℕ → Ω → F) (X' : Ω' → E) (Y' : Ω' → F)
    (hX : TendstoInDistribution X atTop X' (fun _ => P) P')
    (hY : TendstoInDistribution Y atTop Y' (fun _ => P) P')
    (hInd : ∀ n, IndepFun (X n) (Y n) P) (hInd' : IndepFun X' Y' P') :
    TendstoInDistribution (fun n ω => WithLp.toLp 2 (X n ω, Y n ω)) atTop
      (fun ω => WithLp.toLp 2 (X' ω, Y' ω)) (fun _ => P) P' := by
  have hXY : ∀ n, AEMeasurable (fun ω => WithLp.toLp 2 (X n ω, Y n ω)) P :=
    fun n => (WithLp.measurable_toLp 2 _).comp_aemeasurable
      ((hX.forall_aemeasurable n).prodMk (hY.forall_aemeasurable n))
  have hXY' : AEMeasurable (fun ω => WithLp.toLp 2 (X' ω, Y' ω)) P' :=
    (WithLp.measurable_toLp 2 _).comp_aemeasurable
      (hX.aemeasurable_limit.prodMk hY.aemeasurable_limit)
  refine TendstoInDistribution.of_tendsto_charFun hXY hXY' fun t => ?_
  have hfac (n : ℕ) := (indepFun_iff_charFun_prod
    (hX.forall_aemeasurable n) (hY.forall_aemeasurable n)).mp (hInd n) t
  have hfac' := (indepFun_iff_charFun_prod hX.aemeasurable_limit
    hY.aemeasurable_limit).mp hInd' t
  rw [hfac']
  simp_rw [hfac]
  exact (hX.tendsto_charFun t.ofLp.1).mul (hY.tendsto_charFun t.ofLp.2)

private noncomputable def appendVec {d : ℕ} :
    WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → EuclideanSpace ℝ (Fin (d + 1)) :=
  fun p => WithLp.toLp 2 (Fin.lastCases p.ofLp.2 (fun i => p.ofLp.1 i))

private lemma continuous_appendVec {d : ℕ} : Continuous (@appendVec d) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [Function.comp_def] using continuous_snd.comp
      (WithLp.prod_continuous_ofLp 2 (EuclideanSpace ℝ (Fin d)) ℝ)
  · simpa [Function.comp_def] using
      (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).comp
        (continuous_fst.comp
          (WithLp.prod_continuous_ofLp 2 (EuclideanSpace ℝ (Fin d)) ℝ))

private lemma blockVec_tendstoInDistribution
    {d : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X P) (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsPreBrownianReal B P')
    (u : Fin (d + 1) → ℝ≥0) (hu : Monotone u) :
    TendstoInDistribution (fun n => blockVec u n X) atTop (brownianBlockVec u B)
      (fun _ => P) P' := by
  induction d with
  | zero =>
      have hconst : TendstoInDistribution
          (fun _n : ℕ => fun _ω : Ω => (0 : EuclideanSpace ℝ (Fin 0))) atTop
          (fun _ω : Ω' => (0 : EuclideanSpace ℝ (Fin 0))) (fun _ => P) P' := by
        apply tendstoInDistribution_of_identDistrib 0
        · intro n
          exact ⟨by fun_prop, by fun_prop, by simp⟩
        · exact ⟨by fun_prop, by fun_prop, by simp⟩
      refine hconst.congr (fun n => .of_forall fun ω => Subsingleton.elim _ _)
        (.of_forall fun ω => Subsingleton.elim _ _)
  | succ d ih =>
      let u0 : Fin (d + 1) → ℝ≥0 := fun i => u i.castSucc
      have hu0 : Monotone u0 := by
        intro i j hij
        exact hu (by simpa using hij)
      have hprev : TendstoInDistribution (fun n => blockVec u0 n X) atTop
          (brownianBlockVec u0 B) (fun _ => P) P' := ih u0 hu0
      let a : ℝ≥0 := u (Fin.last d).castSucc
      let b : ℝ≥0 := u (Fin.last d).succ
      have hab : a ≤ b := hu (Fin.castSucc_le_succ (Fin.last d))
      have hlast : TendstoInDistribution (fun n => bsum a b n X) atTop (B b - B a)
          (fun _ => P) P' :=
        bsum_tendstoInDistribution X hIndep hIdent hMean hVar B hB a b hab
      have hpair := tid_pair_of_indep
        (fun n => blockVec u0 n X) (fun n => bsum a b n X)
        (brownianBlockVec u0 B) (B b - B a) hprev hlast
        (fun n => indepFun_blockVec_bsum X hMeas hIndep u hu n)
        (indepFun_brownian_blockVec_sub B hB u hu)
      have happ := hpair.continuous_comp (continuous_appendVec (d := d))
      refine happ.congr (fun n => .of_forall fun ω => ?_) (.of_forall fun ω => ?_)
      · simp only [Function.comp_apply, appendVec, blockVec, u0, a, b]
        congr 1
        funext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp
        · simp
      · simp only [Function.comp_apply, appendVec, brownianBlockVec, u0, a, b]
        congr 1
        funext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp
        · simp

private noncomputable def cumVec {d : ℕ} :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun v =>
  WithLp.toLp 2 (fun j =>
    ∑ k : Fin (j + 1), v ⟨k, lt_of_lt_of_le k.isLt (Nat.succ_le_iff.mpr j.isLt)⟩)

private lemma continuous_cumVec {d : ℕ} : Continuous (@cumVec d) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
  apply continuous_pi
  intro j
  dsimp [cumVec]
  fun_prop

private lemma fin_sum_sub_eq (n : ℕ) (A : Fin (n + 1) → ℝ) :
    (∑ k : Fin n, (A k.succ - A k.castSucc)) = A (Fin.last n) - A 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      have hprev := ih (fun i : Fin (n + 1) => A i.castSucc)
      rw [show (∑ x : Fin n,
          (A x.castSucc.succ - A x.castSucc.castSucc)) =
          A (Fin.last n).castSucc - A 0 by
        convert hprev using 1 <;> congr]
      rw [show (Fin.last n).succ = Fin.last (n + 1) by ext; simp]
      ring

private lemma cumVec_blockVec_eq
    {d : ℕ} {Ω : Type*} (u : Fin (d + 1) → ℝ≥0) (hu : Monotone u)
    (hu0 : u 0 = 0) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    cumVec (blockVec u n X ω) =
      WithLp.toLp 2 (fun j : Fin d =>
        (Real.sqrt (n : ℝ))⁻¹ *
          ∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * (u j.succ : ℝ))), X i ω) := by
  apply congrArg (WithLp.toLp 2)
  funext j
  simp only [blockVec]
  let e : Fin (j + 2) → Fin (d + 1) := fun k =>
    ⟨k, lt_of_lt_of_le k.isLt (by omega)⟩
  let A : Fin (j + 2) → ℝ := fun k =>
    ∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * (u (e k) : ℝ))), X i ω
  calc
    ∑ k : Fin (j + 1),
        bsum (u (⟨k, by omega⟩ : Fin d).castSucc)
          (u (⟨k, by omega⟩ : Fin d).succ) n X ω =
      ∑ k : Fin (j + 1),
        (Real.sqrt (n : ℝ))⁻¹ * (A k.succ - A k.castSucc) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [bsum_eq_sub]
          · congr 2
          · exact_mod_cast hu (Fin.castSucc_le_succ (⟨k, by omega⟩ : Fin d))
    _ = (Real.sqrt (n : ℝ))⁻¹ *
        ∑ k : Fin (j + 1), (A k.succ - A k.castSucc) := by
      rw [Finset.mul_sum]
    _ = (Real.sqrt (n : ℝ))⁻¹ * (A (Fin.last (j + 1)) - A 0) := by
      rw [fin_sum_sub_eq]
    _ = (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * (u j.succ : ℝ))), X i ω := by
      have helast : e (Fin.last (j + 1)) = j.succ := by
        apply Fin.ext
        simp [e]
      have hA0 : A 0 = 0 := by
        simp [A, e, hu0]
      rw [hA0, sub_zero]
      change (Real.sqrt (n : ℝ))⁻¹ *
          (∑ i ∈ Finset.range
            (Nat.floor ((n : ℝ) * (u (e (Fin.last (j + 1))) : ℝ))), X i ω) = _
      rw [helast]

private lemma cumVec_brownianBlockVec_eq
    {d : ℕ} {Ω' : Type*} (u : Fin (d + 1) → ℝ≥0)
    (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    cumVec (brownianBlockVec u B ω) =
      WithLp.toLp 2 (fun j : Fin d => B (u j.succ) ω - B (u 0) ω) := by
  apply congrArg (WithLp.toLp 2)
  funext j
  simp only [brownianBlockVec]
  let e : Fin (j + 2) → Fin (d + 1) := fun k =>
    ⟨k, lt_of_lt_of_le k.isLt (by omega)⟩
  let A : Fin (j + 2) → ℝ := fun k => B (u (e k)) ω
  have htel := fin_sum_sub_eq (j + 1) A
  convert htel using 1 <;> congr

private noncomputable def prefixVec {d : ℕ} {Ω : Type*}
    (u : Fin (d + 1) → ℝ≥0) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * (u j.succ : ℝ))), X i ω)

private noncomputable def brownianValueVec {d : ℕ} {Ω' : Type*}
    (u : Fin (d + 1) → ℝ≥0) (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => B (u j.succ) ω)

private lemma prefixVec_tendstoInDistribution
    {d : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X P) (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsPreBrownianReal B P')
    (u : Fin (d + 1) → ℝ≥0) (hu : Monotone u) (hu0 : u 0 = 0) :
    TendstoInDistribution (fun n => prefixVec u n X) atTop (brownianValueVec u B)
      (fun _ => P) P' := by
  have hblock := blockVec_tendstoInDistribution X hMeas hIndep hIdent hMean hVar B hB u hu
  have hcum := hblock.continuous_comp (continuous_cumVec (d := d))
  refine hcum.congr (fun n => .of_forall fun ω => ?_) ?_
  · exact cumVec_blockVec_eq u hu hu0 n X ω
  · filter_upwards [hB.eval_zero_ae_eq_zero] with ω hzero
    rw [Function.comp_apply, cumVec_brownianBlockVec_eq]
    unfold brownianValueVec
    apply congrArg (WithLp.toLp 2)
    funext j
    simp [hu0, hzero]

private noncomputable def interpolationCoeff (n : ℕ) (t : ℝ≥0) : ℝ :=
  if Nat.floor ((n : ℝ) * (t : ℝ)) < n then
    (Real.sqrt (n : ℝ))⁻¹ *
      ((n : ℝ) * (t : ℝ) - Nat.floor ((n : ℝ) * (t : ℝ)))
  else 0

private lemma interpolationCoeff_nonneg (n : ℕ) (t : ℝ≥0) :
    0 ≤ interpolationCoeff n t := by
  rw [interpolationCoeff]
  split_ifs
  · exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (Nat.zero_le_self_sub_floor (mul_nonneg (Nat.cast_nonneg n) t.2))
  · exact le_rfl

private lemma interpolationCoeff_le (n : ℕ) (t : ℝ≥0) :
    interpolationCoeff n t ≤ (Real.sqrt (n : ℝ))⁻¹ := by
  rw [interpolationCoeff]
  split_ifs
  · exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (Nat.self_sub_floor_lt_one ((n : ℝ) * (t : ℝ))).le
  · exact inv_nonneg.mpr (Real.sqrt_nonneg _)

private lemma interpolationCoeff_tendsto_zero (t : ℝ≥0) :
    Tendsto (fun n => interpolationCoeff n t) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  · exact .of_forall fun n => interpolationCoeff_nonneg n t
  · exact .of_forall fun n => interpolationCoeff_le n t

private noncomputable def interpolationErrorVec {d : ℕ} {Ω : Type*}
    (u : Fin d → ℝ≥0) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j =>
    interpolationCoeff n (u j) * X (Nat.floor ((n : ℝ) * (u j : ℝ))) ω)

private lemma interpolationErrorVec_eq_sum {d : ℕ} {Ω : Type*}
    (u : Fin d → ℝ≥0) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    interpolationErrorVec u n X ω =
      ∑ j : Fin d, PiLp.single 2 j
        (interpolationCoeff n (u j) * X (Nat.floor ((n : ℝ) * (u j : ℝ))) ω) := by
  apply PiLp.ext
  intro j
  simp [interpolationErrorVec]

private lemma interpolationErrorVec_eLpNorm_tendsto_zero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i))
    (hMemLp : MemLp (X 0) 2 P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (u : Fin d → ℝ≥0) :
    Tendsto (fun n => eLpNorm (interpolationErrorVec u n X) 2 P) atTop (nhds 0) := by
  let C : ℝ≥0∞ := eLpNorm (X 0) 2 P
  have hterm (j : Fin d) :
      Tendsto (fun n => ‖interpolationCoeff n (u j)‖ₑ * C) atTop (nhds 0) := by
    have hc : Tendsto (fun n => ‖interpolationCoeff n (u j)‖ₑ) atTop (nhds 0) := by
      change Tendsto ((fun a : ℝ => ‖a‖ₑ) ∘ fun n => interpolationCoeff n (u j))
        atTop (nhds 0)
      simpa only [enorm_zero] using
        (continuous_enorm.tendsto 0).comp (interpolationCoeff_tendsto_zero (u j))
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const hc (Or.inr hMemLp.eLpNorm_lt_top.ne)
  have hsum : Tendsto (fun n => ∑ j : Fin d, ‖interpolationCoeff n (u j)‖ₑ * C)
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ => hterm j)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (.of_forall fun n => bot_le) ?_
  apply Filter.Eventually.of_forall
  intro n
  rw [show interpolationErrorVec u n X =
      ∑ j : Fin d, fun ω => PiLp.single (p := 2) (i := j)
        (β := fun _ : Fin d => ℝ)
        (interpolationCoeff n (u j) *
          X (Nat.floor ((n : ℝ) * (u j : ℝ))) ω) by
    funext ω
    simpa only [Finset.sum_apply] using interpolationErrorVec_eq_sum u n X ω]
  refine (eLpNorm_sum_le (p := (2 : ℝ≥0∞)) (by norm_num)).trans ?_
  apply Finset.sum_le_sum
  intro j _
  have hsingle : Continuous (fun x : ℝ =>
      PiLp.single (p := 2) (i := j) (β := fun _ : Fin d => ℝ) x) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    apply continuous_pi
    intro k
    by_cases hjk : j = k
    · subst k
      simpa only [Pi.single_eq_same] using (continuous_id' : Continuous (fun x : ℝ => x))
    · simpa only [Pi.single_eq_of_ne (Ne.symm hjk)] using
        (continuous_const : Continuous (fun _x : ℝ => (0 : ℝ)))
  have hcoord : AEStronglyMeasurable
      (fun ω => interpolationCoeff n (u j) *
        X (Nat.floor ((n : ℝ) * (u j : ℝ))) ω) P :=
    ((hMeas (Nat.floor ((n : ℝ) * (u j : ℝ)))).const_mul _).aestronglyMeasurable
  have hscalar :
      eLpNorm
          (fun ω => PiLp.single (p := 2) (i := j) (β := fun _ : Fin d => ℝ)
            (interpolationCoeff n (u j) *
              X (Nat.floor ((n : ℝ) * (u j : ℝ))) ω)) 2 P =
        eLpNorm
          (fun ω => interpolationCoeff n (u j) *
            X (Nat.floor ((n : ℝ) * (u j : ℝ))) ω) 2 P := by
    apply eLpNorm_congr_norm_ae
    · exact hsingle.comp_aestronglyMeasurable hcoord
    · exact hcoord
    · exact .of_forall fun ω => PiLp.norm_single 2 (fun _ : Fin d => ℝ) j _
  rw [hscalar]
  rw [show (fun ω => interpolationCoeff n (u j) *
      X (Nat.floor ((n : ℝ) * (u j : ℝ))) ω) =
      interpolationCoeff n (u j) •
        X (Nat.floor ((n : ℝ) * (u j : ℝ))) by rfl]
  rw [eLpNorm_const_smul]
  exact le_of_eq (congrArg (‖interpolationCoeff n (u j)‖ₑ * ·)
    ((hIdent (Nat.floor ((n : ℝ) * (u j : ℝ)))).eLpNorm_eq 2))

private lemma interpolationErrorVec_tendstoInMeasure
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i))
    (hMemLp : MemLp (X 0) 2 P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (u : Fin d → ℝ≥0) :
    TendstoInMeasure P (fun n => interpolationErrorVec u n X) atTop 0 := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ℝ≥0∞)) (by norm_num)
  simpa using interpolationErrorVec_eLpNorm_tendsto_zero X hMeas hMemLp hIdent u

private lemma interpolationErrorVec_measurable
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i))
    (u : Fin d → ℝ≥0) (n : ℕ) :
    Measurable (interpolationErrorVec u n X) := by
  unfold interpolationErrorVec
  apply (WithLp.measurable_toLp 2 _).comp
  fun_prop

private noncomputable def processValueVec {d : ℕ} {Ω : Type*}
    (t : Fin d → Set.Icc (0 : ℝ) 1) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => donskerProcess n X ω (t j))

private lemma processValueVec_eq_prefix_add_error
    {d : ℕ} {Ω : Type*}
    (t : Fin d → Set.Icc (0 : ℝ) 1)
    (u : Fin (d + 1) → ℝ≥0)
    (htu : ∀ j, u j.succ = iccToNNReal (t j))
    (n : ℕ) (hn : n ≠ 0) (X : ℕ → Ω → ℝ) (ω : Ω) :
    processValueVec t n X ω =
      prefixVec u n X ω + interpolationErrorVec (fun j => u j.succ) n X ω := by
  apply PiLp.ext
  intro j
  change donskerProcess n X ω (t j) =
    (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * (u j.succ : ℝ))), X i ω +
      interpolationCoeff n (u j.succ) *
        X (Nat.floor ((n : ℝ) * (u j.succ : ℝ))) ω
  rw [donskerProcess_apply_eq n X ω (t j) hn]
  have htuR : (u j.succ : ℝ) = (t j : ℝ) := by
    have h := congrArg ((↑) : ℝ≥0 → ℝ) (htu j)
    change (u j.succ : ℝ) = (t j).1 at h
    exact h
  unfold interpolationCoeff
  rw [htuR]
  split_ifs with hfloor
  · field_simp
  · field_simp
    simp

private lemma processValueVec_measurable
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i))
    (t : Fin d → Set.Icc (0 : ℝ) 1) (n : ℕ) :
    Measurable (processValueVec t n X) := by
  unfold processValueVec
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro j
  by_cases hn : n = 0
  · simp [donskerProcess, hn]
  · simp only [donskerProcess, hn, ↓reduceIte, ContinuousMap.smul_apply,
      ContinuousMap.sum_apply]
    fun_prop

private lemma processValueVec_tendstoInDistribution
    {d : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X P) (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsPreBrownianReal B P')
    (t : Fin d → Set.Icc (0 : ℝ) 1)
    (u : Fin (d + 1) → ℝ≥0) (hu : Monotone u) (hu0 : u 0 = 0)
    (htu : ∀ j, u j.succ = iccToNNReal (t j)) :
    TendstoInDistribution (fun n => processValueVec t n X) atTop (brownianValueVec u B)
      (fun _ => P) P' := by
  have hprefix := prefixVec_tendstoInDistribution X hMeas hIndep hIdent hMean hVar
    B hB u hu hu0
  have herr := interpolationErrorVec_tendstoInMeasure X hMeas hMemLp hIdent
    (fun j => u j.succ)
  have hadd := hprefix.add_of_tendstoInMeasure_const herr
    (fun n => (interpolationErrorVec_measurable X hMeas (fun j => u j.succ) n).aemeasurable)
  have hsource : ∀ n,
      prefixVec u n X + interpolationErrorVec (fun j => u j.succ) n X =ᵐ[P]
        processValueVec t n X := by
    intro n
    by_cases hn : n = 0
    · subst n
      exact .of_forall fun ω => by
        apply PiLp.ext
        intro j
        simp [processValueVec, prefixVec, interpolationErrorVec, interpolationCoeff,
          donskerProcess]
    · exact .of_forall fun ω =>
        (processValueVec_eq_prefix_add_error t u htu n hn X ω).symm
  have hlimit : (fun ω => brownianValueVec u B ω + WithLp.toLp 2 0) =ᵐ[P']
      brownianValueVec u B := by
    apply Filter.Eventually.of_forall
    intro ω
    have hz : WithLp.toLp 2 (0 : Fin d → ℝ) =
        (0 : EuclideanSpace ℝ (Fin d)) := by
      apply PiLp.ext
      intro j
      rfl
    rw [hz]
    change brownianValueVec u B ω + 0 = brownianValueVec u B ω
    exact add_zero _
  exact hadd.congr hsource hlimit

private noncomputable def finsetTimes
    (I : Finset (Set.Icc (0 : ℝ) 1)) : Fin I.card → Set.Icc (0 : ℝ) 1 :=
  fun j => (I.orderIsoOfFin rfl j).1

private noncomputable def finsetTimesWithZero
    (I : Finset (Set.Icc (0 : ℝ) 1)) : Fin (I.card + 1) → ℝ≥0 :=
  Fin.cases 0 (fun j => iccToNNReal (finsetTimes I j))

private lemma finsetTimesWithZero_zero (I : Finset (Set.Icc (0 : ℝ) 1)) :
    finsetTimesWithZero I 0 = 0 := by
  rfl

private lemma finsetTimesWithZero_succ (I : Finset (Set.Icc (0 : ℝ) 1))
    (j : Fin I.card) :
    finsetTimesWithZero I j.succ = iccToNNReal (finsetTimes I j) := by
  rfl

private lemma finsetTimesWithZero_monotone (I : Finset (Set.Icc (0 : ℝ) 1)) :
    Monotone (finsetTimesWithZero I) := by
  rw [Fin.monotone_iff_le_succ]
  intro j
  by_cases hzero : j.castSucc = 0
  · calc
      finsetTimesWithZero I j.castSucc = 0 := by rw [hzero]; rfl
      _ ≤ finsetTimesWithZero I j.succ := bot_le
  · obtain ⟨k, hk⟩ := Fin.eq_succ_of_ne_zero hzero
    have hkj : k ≤ j := by
      apply Fin.mk_le_mk.mpr
      have hkval := congrArg Fin.val hk
      simp only [Fin.val_castSucc, Fin.val_succ] at hkval
      omega
    calc
      finsetTimesWithZero I j.castSucc = iccToNNReal (finsetTimes I k) := by
        rw [hk]
        rfl
      _ ≤ iccToNNReal (finsetTimes I j) := by
        apply NNReal.coe_le_coe.mp
        change ((I.orderIsoOfFin rfl k).1 : Set.Icc (0 : ℝ) 1).1 ≤
          ((I.orderIsoOfFin rfl j).1 : Set.Icc (0 : ℝ) 1).1
        exact_mod_cast (I.orderIsoOfFin rfl).monotone hkj
      _ = finsetTimesWithZero I j.succ := rfl

private noncomputable def orderedToFinset
    (I : Finset (Set.Icc (0 : ℝ) 1)) :
    EuclideanSpace ℝ (Fin I.card) → (I → ℝ) :=
  fun z i => z ((I.orderIsoOfFin rfl).symm i)

private lemma continuous_orderedToFinset (I : Finset (Set.Icc (0 : ℝ) 1)) :
    Continuous (orderedToFinset I) := by
  apply continuous_pi
  intro i
  exact PiLp.continuous_apply 2 (fun _ : Fin I.card => ℝ) ((I.orderIsoOfFin rfl).symm i)

private lemma orderedToFinset_processValueVec
    {Ω : Type*} (I : Finset (Set.Icc (0 : ℝ) 1))
    (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    orderedToFinset I
        (processValueVec (fun j : Fin I.card => finsetTimes I j) n X ω) =
      I.restrict (fun t => donskerProcess n X ω t) := by
  ext i
  change donskerProcess n X ω
      ((I.orderIsoOfFin rfl ((I.orderIsoOfFin rfl).symm i)).1) =
    donskerProcess n X ω i.1
  rw [(I.orderIsoOfFin rfl).apply_symm_apply i]

private lemma orderedToFinset_brownianValueVec
    {Ω' : Type*} (I : Finset (Set.Icc (0 : ℝ) 1))
    (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    orderedToFinset I (brownianValueVec (finsetTimesWithZero I) B ω) =
      I.restrict (fun t => B (iccToNNReal t) ω) := by
  ext i
  change B (iccToNNReal
      ((I.orderIsoOfFin rfl ((I.orderIsoOfFin rfl).symm i)).1)) ω =
    B (iccToNNReal i.1) ω
  rw [(I.orderIsoOfFin rfl).apply_symm_apply i]

private lemma finsetEval_tendstoInDistribution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X P) (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsPreBrownianReal B P')
    (I : Finset (Set.Icc (0 : ℝ) 1)) :
    TendstoInDistribution
      (fun n ω => I.restrict (fun t => donskerProcess n X ω t)) atTop
      (fun ω => I.restrict (fun t => B (iccToNNReal t) ω)) (fun _ => P) P' := by
  have hvalues := processValueVec_tendstoInDistribution X hMeas hIndep hIdent hMemLp
    hMean hVar B hB (finsetTimes I) (finsetTimesWithZero I)
    (finsetTimesWithZero_monotone I) (finsetTimesWithZero_zero I)
    (finsetTimesWithZero_succ I)
  have hmap := hvalues.continuous_comp (continuous_orderedToFinset I)
  refine hmap.congr (fun n => .of_forall fun ω => ?_) (.of_forall fun ω => ?_)
  · exact orderedToFinset_processValueVec I n X ω
  · exact orderedToFinset_brownianValueVec I B ω

private def psum {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, X i ω

private def level {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) : Set Ω :=
  {ω | a ≤ |psum X k ω|}

private lemma measurable_psum {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (k : ℕ) :
    Measurable (psum X k) := by
  unfold psum
  fun_prop

private lemma measurableSet_level {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (a : ℝ) (k : ℕ) :
    MeasurableSet (level X a k) := by
  exact measurableSet_le measurable_const (measurable_psum X hX k).norm

private def firstHit {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) : Set Ω :=
  disjointed (level X a) k

private lemma measurableSet_firstHit {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (a : ℝ) (k : ℕ) :
    MeasurableSet (firstHit X a k) := by
  exact MeasurableSet.disjointed (measurableSet_level X hX a) k

private def prefixTuple {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) :
    Ω → (Finset.range k → ℝ) :=
  fun ω i => X i ω

private def tailTuple {Ω : Type*} (X : ℕ → Ω → ℝ) (k n : ℕ) :
    Ω → (Finset.Ico k n → ℝ) :=
  fun ω i => X i ω

private def tuplePsum (k : ℕ) (z : Finset.range k → ℝ) (j : Fin (k + 1)) : ℝ :=
  ∑ i : Fin j, z ⟨i, Finset.mem_range.mpr
    (lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt))⟩

private def tupleFirstHit (k : ℕ) (a : ℝ) : Set (Finset.range k → ℝ) :=
  {z | a ≤ |tuplePsum k z (Fin.last k)| ∧
    ∀ j : Fin k, |tuplePsum k z j.castSucc| < a}

private def tupleTailLarge (k n : ℕ) (a : ℝ) : Set (Finset.Ico k n → ℝ) :=
  {z | a < |∑ i, z i|}

private lemma tuplePsum_prefixTuple
    {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) (j : Fin (k + 1)) :
    tuplePsum k (prefixTuple X k ω) j = psum X j ω := by
  rw [tuplePsum, psum]
  simpa [prefixTuple] using
    (Fin.sum_univ_eq_sum_range (fun i => X i ω) j)

private lemma measurableSet_tupleFirstHit (k : ℕ) (a : ℝ) :
    MeasurableSet (tupleFirstHit k a) := by
  have hsum (j : Fin (k + 1)) :
      Measurable (fun z : Finset.range k → ℝ => tuplePsum k z j) := by
    unfold tuplePsum
    fun_prop
  rw [show tupleFirstHit k a =
      {z | a ≤ |tuplePsum k z (Fin.last k)|} ∩
        ⋂ j : Fin k, {z | |tuplePsum k z j.castSucc| < a} by
    ext z
    simp [tupleFirstHit]]
  exact (measurableSet_le measurable_const (hsum (Fin.last k)).norm).inter
    (MeasurableSet.iInter fun j => measurableSet_lt (hsum j.castSucc).norm measurable_const)

private lemma measurableSet_tupleTailLarge (k n : ℕ) (a : ℝ) :
    MeasurableSet (tupleTailLarge k n a) := by
  exact measurableSet_lt measurable_const (by fun_prop)

private lemma firstHit_eq_preimage_prefixTuple
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) :
    firstHit X a k = prefixTuple X k ⁻¹' tupleFirstHit k a := by
  ext ω
  simp only [firstHit, disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, Set.mem_preimage, level, Set.mem_ofPred_eq, tupleFirstHit]
  constructor
  · rintro ⟨hk, hprev⟩
    refine ⟨?_, fun j => ?_⟩
    · rw [tuplePsum_prefixTuple]
      simpa using hk
    · have := hprev j j.isLt
      simp only [not_le] at this
      rw [tuplePsum_prefixTuple]
      simpa using this
  · rintro ⟨hk, hprev⟩
    refine ⟨?_, fun j hj => ?_⟩
    · rw [tuplePsum_prefixTuple] at hk
      simpa using hk
    · simp only [not_le]
      have hp := hprev ⟨j, hj⟩
      rw [tuplePsum_prefixTuple] at hp
      simpa using hp

private lemma tailLarge_eq_preimage_tailTuple
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (k n : ℕ) (hkn : k ≤ n) :
    {ω | a < |psum X n ω - psum X k ω|} =
      tailTuple X k n ⁻¹' tupleTailLarge k n a := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, tupleTailLarge, tailTuple]
  rw [psum, psum, ← Finset.sum_Ico_eq_sub (fun i => X i ω) hkn]
  rw [Finset.sum_subtype]
  simp

private lemma firstHit_inter_tailLarge_measure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X P) (a b : ℝ) (k n : ℕ) (hkn : k ≤ n) :
    P (firstHit X a k ∩ {ω | b < |psum X n ω - psum X k ω|}) =
      P (firstHit X a k) * P {ω | b < |psum X n ω - psum X k ω|} := by
  have hdisj : Disjoint (Finset.range k) (Finset.Ico k n) := by
    rw [Finset.disjoint_left]
    intro i hi h'i
    exact (not_lt_of_ge (Finset.mem_Ico.mp h'i).1) (Finset.mem_range.mp hi)
  have hraw : IndepFun (prefixTuple X k) (tailTuple X k n) P := by
    exact hIndep.indepFun_finset (Finset.range k) (Finset.Ico k n) hdisj hX
  have hmeasure := hraw.measure_inter_preimage_eq_mul
    (tupleFirstHit k a) (tupleTailLarge k n b)
    (measurableSet_tupleFirstHit k a) (measurableSet_tupleTailLarge k n b)
  rw [← firstHit_eq_preimage_prefixTuple X a k,
    ← tailLarge_eq_preimage_tailTuple X b k n hkn] at hmeasure
  exact hmeasure

private lemma tailLarge_subset_level_union
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (k n : ℕ) :
    {ω | 2 * a < |psum X n ω - psum X k ω|} ⊆
      level X a n ∪ level X a k := by
  intro ω hω
  by_contra hmem
  simp only [Set.mem_union, level, Set.mem_ofPred_eq, not_or, not_le] at hmem
  change 2 * a < |psum X n ω - psum X k ω| at hω
  have htri := abs_sub (psum X n ω) (psum X k ω)
  linarith

private lemma firstHit_subset_level_union_inter_tail
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (k n : ℕ) :
    firstHit X (3 * a) k ⊆
      level X a n ∪
        (firstHit X (3 * a) k ∩ {ω | 2 * a < |psum X n ω - psum X k ω|}) := by
  intro ω hω
  by_cases htail : 2 * a < |psum X n ω - psum X k ω|
  · exact Or.inr ⟨hω, htail⟩
  · left
    have hk : 3 * a ≤ |psum X k ω| :=
      (disjointed_subset (level X (3 * a)) k hω)
    have htri : |psum X k ω| ≤
        |psum X n ω| + |psum X n ω - psum X k ω| := by
      calc
        |psum X k ω| = |psum X n ω - (psum X n ω - psum X k ω)| := by ring_nf
        _ ≤ |psum X n ω| + |psum X n ω - psum X k ω| := abs_sub _ _
    change a ≤ |psum X n ω|
    linarith

private lemma biUnion_firstHit_eq_biUnion_level
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) :
    ⋃ k ∈ Finset.range (n + 1), firstHit X a k =
      ⋃ k ∈ Finset.range (n + 1), level X a k := by
  rw [show (⋃ k ∈ Finset.range (n + 1), firstHit X a k) =
      partialSups (level X a) n by
    exact biUnion_range_succ_disjointed (level X a) n]
  rw [partialSups_apply, Finset.sup'_eq_sup, Finset.sup_set_eq_biUnion]
  ext ω
  simp

/-- Etemadi's maximal inequality for partial sums of independent real random variables. -/
public theorem etemadi_maximal_inequality
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X P) (n : ℕ) (a : ℝ) :
    P {ω | ∃ k ∈ Finset.range (n + 1),
        3 * a ≤ |∑ i ∈ Finset.range k, X i ω|} ≤
      3 * (⨆ k ∈ Finset.range (n + 1),
        P {ω | a ≤ |∑ i ∈ Finset.range k, X i ω|}) := by
  rw [show {ω | ∃ k ∈ Finset.range (n + 1),
      3 * a ≤ |∑ i ∈ Finset.range k, X i ω|} =
      ⋃ k ∈ Finset.range (n + 1), level X (3 * a) k by
    ext ω
    simp [level, psum]]
  change P (⋃ k ∈ Finset.range (n + 1), level X (3 * a) k) ≤
    3 * (⨆ k ∈ Finset.range (n + 1), P (level X a k))
  let M : ℝ≥0∞ := ⨆ k ∈ Finset.range (n + 1), P (level X a k)
  have hM (k : ℕ) (hk : k ∈ Finset.range (n + 1)) : P (level X a k) ≤ M := by
    exact le_iSup_of_le k (le_iSup_of_le hk le_rfl)
  have htail (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      P {ω | 2 * a < |psum X n ω - psum X k ω|} ≤ 2 * M := by
    have hkn : k ≤ n := by
      have hlt := Finset.mem_range.mp hk
      omega
    calc
      P {ω | 2 * a < |psum X n ω - psum X k ω|}
          ≤ P (level X a n ∪ level X a k) :=
        measure_mono (tailLarge_subset_level_union X a k n)
      _ ≤ P (level X a n) + P (level X a k) := measure_union_le _ _
      _ ≤ M + M := add_le_add (hM n (by simp)) (hM k hk)
      _ = 2 * M := by ring
  have hinter (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      P (firstHit X (3 * a) k ∩
          {ω | 2 * a < |psum X n ω - psum X k ω|}) ≤
        P (firstHit X (3 * a) k) * (2 * M) := by
    have hkn : k ≤ n := by
      have hlt := Finset.mem_range.mp hk
      omega
    rw [firstHit_inter_tailLarge_measure X hX hIndep (3 * a) (2 * a) k n hkn]
    exact mul_le_mul_right (htail k hk) _
  have hsumHit :
      (∑ k ∈ Finset.range (n + 1), P (firstHit X (3 * a) k)) ≤ 1 := by
    change (∑ k ∈ Finset.range (n + 1),
      P (disjointed (level X (3 * a)) k)) ≤ 1
    rw [← measure_biUnion_finset
      ((disjoint_disjointed (level X (3 * a))).set_pairwise _)
      (fun k _ => measurableSet_firstHit X hX (3 * a) k)]
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hsubset :
      (⋃ k ∈ Finset.range (n + 1), firstHit X (3 * a) k) ⊆
        level X a n ∪
          ⋃ k ∈ Finset.range (n + 1),
            (firstHit X (3 * a) k ∩
              {ω | 2 * a < |psum X n ω - psum X k ω|}) := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_union] at hω ⊢
    obtain ⟨k, hk, hωk⟩ := hω
    rcases firstHit_subset_level_union_inter_tail X a k n hωk with hn | ht
    · exact Or.inl hn
    · exact Or.inr ⟨k, hk, ht⟩
  change P (⋃ k ∈ Finset.range (n + 1), level X (3 * a) k) ≤ 3 * M
  rw [← biUnion_firstHit_eq_biUnion_level X (3 * a) n]
  calc
    P (⋃ k ∈ Finset.range (n + 1), firstHit X (3 * a) k)
        ≤ P (level X a n ∪
          ⋃ k ∈ Finset.range (n + 1),
            (firstHit X (3 * a) k ∩
              {ω | 2 * a < |psum X n ω - psum X k ω|})) := measure_mono hsubset
    _ ≤ P (level X a n) +
          P (⋃ k ∈ Finset.range (n + 1),
            (firstHit X (3 * a) k ∩
              {ω | 2 * a < |psum X n ω - psum X k ω|})) := measure_union_le _ _
    _ ≤ M + ∑ k ∈ Finset.range (n + 1),
          P (firstHit X (3 * a) k ∩
            {ω | 2 * a < |psum X n ω - psum X k ω|}) := by
      gcongr
      · exact hM n (by simp)
      · exact measure_biUnion_finset_le _ _
    _ ≤ M + ∑ k ∈ Finset.range (n + 1),
          P (firstHit X (3 * a) k) * (2 * M) := by
      gcongr with k hk
      exact hinter k hk
    _ = M + (∑ k ∈ Finset.range (n + 1), P (firstHit X (3 * a) k)) *
          (2 * M) := by rw [Finset.sum_mul]
    _ ≤ M + 1 * (2 * M) := by gcongr
    _ = 3 * M := by ring

private lemma donsker_memLp_ident
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (i : ℕ) :
    MemLp (X i) 2 P :=
  (hIdent i).memLp_iff.mpr hMemLp

private lemma donsker_psum_memLp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (k : ℕ) :
    MemLp (psum X k) 2 P := by
  change MemLp (fun a => ∑ i ∈ Finset.range k, X i a) 2 P
  exact memLp_finsetSum (Finset.range k)
    (fun i _ => donsker_memLp_ident X hIdent hMemLp i)

private lemma donsker_psum_mean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0) (k : ℕ) :
    P[psum X k] = 0 := by
  change ∫ ω, ∑ i ∈ Finset.range k, X i ω ∂P = 0
  rw [integral_finsetSum]
  · simp only [(hIdent _).integral_eq, hMean, Finset.sum_const_zero]
  · exact fun i _ => (donsker_memLp_ident X hIdent hMemLp i).integrable (by norm_num)

private lemma donsker_psum_variance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hVar : Var[X 0; P] = 1) (k : ℕ) :
    Var[psum X k; P] = k := by
  change Var[fun ω => ∑ i ∈ Finset.range k, X i ω; P] = k
  rw [show (fun ω => ∑ i ∈ Finset.range k, X i ω) =
      ∑ i ∈ Finset.range k, X i by
    funext ω
    simp only [Finset.sum_apply]]
  rw [IndepFun.variance_sum]
  · simp only [(hIdent _).variance_eq, hVar, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  · exact fun i _ => donsker_memLp_ident X hIdent hMemLp i
  · intro i hi j hj hij
    exact hIndep.indepFun hij

private lemma donsker_psum_tail_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1) (k : ℕ) {a : ℝ} (ha : 0 < a) :
    P {ω | a ≤ |psum X k ω|} ≤ ENNReal.ofReal ((k : ℝ) / a ^ 2) := by
  have h := meas_ge_le_variance_div_sq
    (donsker_psum_memLp X hIdent hMemLp k) ha
  rw [donsker_psum_mean X hIdent hMemLp hMean k,
    donsker_psum_variance X hIndep hIdent hMemLp hVar k] at h
  simpa using h

private lemma donsker_psum_tail_real_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1) (k : ℕ) {a : ℝ} (ha : 0 < a) :
    P.real {ω | a ≤ |psum X k ω|} ≤ (k : ℝ) / a ^ 2 := by
  have h := donsker_psum_tail_le X hIndep hIdent hMemLp hMean hVar k ha
  have ht := (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).2 h
  simpa only [measureReal_def, ENNReal.toReal_ofReal
    (div_nonneg (Nat.cast_nonneg k) (sq_nonneg a))] using ht

private lemma donsker_normalized_psum_tendstoInDistribution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, X i ω)
      atTop id (fun _ => P) (gaussianReal 0 1) := by
  exact tendstoInDistribution_inv_sqrt_mul_sum HasLaw.id hMean
    (second_moment (X 0) (hIdent 0).aemeasurable_fst hMean hVar) hIndep hIdent

private noncomputable def donskerGaussianFourthBound : ℝ :=
  (eLpNorm id 4 (gaussianReal 0 1)).toReal ^ 4

private lemma donsker_gaussian_tail_fourth {a : ℝ} (ha : 0 < a) :
    a ^ 4 * (gaussianReal 0 1).real {x | a ≤ |x|} ≤ donskerGaussianFourthBound := by
  have h := mul_meas_ge_le_pow_eLpNorm' (gaussianReal 0 1)
    (p := (4 : ℝ≥0∞)) (f := (id : ℝ → ℝ))
    (by norm_num) (by norm_num) (ENNReal.ofReal a)
  have hset : {x : ℝ | ENNReal.ofReal a ≤ ‖id x‖ₑ} = {x | a ≤ |x|} := by
    ext x
    simp only [id_eq, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg x)
  rw [hset] at h
  have hleft : (ENNReal.ofReal a ^ (4 : ℝ≥0∞).toReal *
      gaussianReal 0 1 {x | a ≤ |x|}) ≠ ∞ := by
    finiteness
  have hright : (eLpNorm id (4 : ℝ≥0∞) (gaussianReal 0 1) ^
      (4 : ℝ≥0∞).toReal) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · norm_num
    · exact (memLp_id_gaussianReal (4 : ℝ≥0)).eLpNorm_lt_top.ne
  have ht := (ENNReal.toReal_le_toReal hleft hright).2 h
  simpa [donskerGaussianFourthBound, measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_rpow, ENNReal.toReal_ofReal ha.le] using ht

private lemma donsker_gaussian_tail_frontier_null {a : ℝ} (ha : 0 ≤ a) :
    gaussianReal 0 1 (frontier {x : ℝ | a ≤ |x|}) = 0 := by
  let _ := nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hset : {x : ℝ | a ≤ |x|} = (Metric.ball 0 a)ᶜ := by
    ext x
    simp [Metric.mem_ball]
  rw [hset, frontier_compl]
  refine measure_mono_null Metric.frontier_ball_subset_sphere ?_
  rw [Real.sphere_eq_pair 0 ha]
  simpa only [zero_sub, zero_add] using
    ((Set.countable_singleton a).insert (-a)).measure_zero (gaussianReal 0 1)

private lemma donsker_normalized_psum_tail_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto
      (fun (k : ℕ) => P.real {ω | a ≤
        |(Real.sqrt (k : ℝ))⁻¹ * ∑ i ∈ Finset.range k, X i ω|})
      atTop (𝓝 ((gaussianReal 0 1).real {x | a ≤ |x|})) := by
  let W : ℕ → Ω → ℝ := fun k ω =>
    (Real.sqrt (k : ℝ))⁻¹ * ∑ i ∈ Finset.range k, X i ω
  let F : Set ℝ := {x | a ≤ |x|}
  have hF : IsClosed F := by
    exact isClosed_le (by fun_prop) (by fun_prop)
  have htid : TendstoInDistribution W atTop id (fun _ => P) (gaussianReal 0 1) := by
    exact donsker_normalized_psum_tendstoInDistribution X hIndep hIdent hMean hVar
  have hmeasure := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    htid.tendsto (E := F) (by
      simpa [F] using donsker_gaussian_tail_frontier_null ha)
  have hsource (k : ℕ) : P.map (W k) F = P {ω | a ≤ |W k ω|} := by
    rw [Measure.map_apply_of_aemeasurable (htid.forall_aemeasurable k) hF.measurableSet]
    rfl
  have htarget : (gaussianReal 0 1).map id F = gaussianReal 0 1 F := by
    rw [Measure.map_id]
  have hfinite :
      (↑(⟨(gaussianReal 0 1).map id, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ) F ≠
        ∞ := by
    simp only [htarget]
    exact measure_ne_top _ _
  have hreal := (ENNReal.continuousAt_toReal hfinite).tendsto.comp hmeasure
  simpa only [ProbabilityMeasure.coe_mk, hsource, htarget, measureReal_def, W, F,
    Function.comp_def] using hreal

private lemma donsker_normalized_psum_tail_eventually
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop,
      P.real {ω | a ≤
          |(Real.sqrt (k : ℝ))⁻¹ * ∑ i ∈ Finset.range k, X i ω|} ≤
        (gaussianReal 0 1).real {x | a ≤ |x|} + δ := by
  have ht := donsker_normalized_psum_tail_tendsto X hIndep hIdent hMean hVar ha.le
  have hev := ht.eventually
    (Iio_mem_nhds (lt_add_of_pos_right ((gaussianReal 0 1).real {x | a ≤ |x|}) hδ))
  filter_upwards [hev] with k hk
  exact hk.le

private lemma donsker_normalized_psum_tail_scaled_eventually
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    {a η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop,
      a ^ 2 * P.real {ω | a ≤
          |(Real.sqrt (k : ℝ))⁻¹ * ∑ i ∈ Finset.range k, X i ω|} ≤
        donskerGaussianFourthBound / a ^ 2 + η := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hev := donsker_normalized_psum_tail_eventually X hIndep hIdent hMean hVar
    ha (div_pos hη ha2)
  have hg := donsker_gaussian_tail_fourth ha
  have hg' : a ^ 2 * (gaussianReal 0 1).real {x | a ≤ |x|} ≤
      donskerGaussianFourthBound / a ^ 2 := by
    rw [le_div_iff₀ ha2]
    nlinarith [hg]
  filter_upwards [hev] with k hk
  calc
    a ^ 2 * P.real {ω | a ≤
        |(Real.sqrt (k : ℝ))⁻¹ * ∑ i ∈ Finset.range k, X i ω|}
        ≤ a ^ 2 * ((gaussianReal 0 1).real {x | a ≤ |x|} + η / a ^ 2) :=
      mul_le_mul_of_nonneg_left hk ha2.le
    _ = a ^ 2 * (gaussianReal 0 1).real {x | a ≤ |x|} + η := by
      field_simp
    _ ≤ donskerGaussianFourthBound / a ^ 2 + η := by
      simpa only [add_comm] using add_le_add_right hg' η

private lemma donsker_psum_tail_subset_normalized
    {Ω : Type*} (X : ℕ → Ω → ℝ) {c : ℝ} (hc : 0 ≤ c)
    {k m : ℕ} (hk0 : 0 < k) (hkm : k ≤ m) :
    {ω | c * Real.sqrt (m : ℝ) ≤ |psum X k ω|} ⊆
      {ω | c ≤ |(Real.sqrt (k : ℝ))⁻¹ * psum X k ω|} := by
  intro ω hω
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hsqrtk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkR
  have hsqrt_le : Real.sqrt (k : ℝ) ≤ Real.sqrt (m : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hkm)
  change c * Real.sqrt (m : ℝ) ≤ |psum X k ω| at hω
  change c ≤ |(Real.sqrt (k : ℝ))⁻¹ * psum X k ω|
  rw [abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), inv_mul_eq_div,
    le_div_iff₀ hsqrtk]
  exact (mul_le_mul_of_nonneg_left hsqrt_le hc).trans hω

private lemma donsker_psum_tail_small_index
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1) {c ρ : ℝ} (hc : 0 < c)
    {k m : ℕ} (hm0 : 0 < m) (hkρ : (k : ℝ) ≤ ρ * m) :
    c ^ 2 * P.real {ω | c * Real.sqrt (m : ℝ) ≤ |psum X k ω|} ≤ ρ := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have htail := donsker_psum_tail_real_le X hIndep hIdent hMemLp hMean hVar k
    (mul_pos hc hsqrtm)
  calc
    c ^ 2 * P.real {ω | c * Real.sqrt (m : ℝ) ≤ |psum X k ω|}
        ≤ c ^ 2 * ((k : ℝ) / (c * Real.sqrt (m : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left htail (sq_nonneg c)
    _ = (k : ℝ) / m := by
      rw [mul_pow, Real.sq_sqrt hmR.le]
      field_simp
    _ ≤ ρ := by
      rw [div_le_iff₀ hmR]
      simpa only [Nat.cast_ofNat, mul_comm] using hkρ

private lemma donsker_psum_tail_large_index_eventually
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ m, k ≤ m →
      c ^ 2 * P.real {ω | c * Real.sqrt (m : ℝ) ≤ |psum X k ω|} ≤
        donskerGaussianFourthBound / c ^ 2 + η := by
  have hev := donsker_normalized_psum_tail_scaled_eventually X hIndep hIdent hMean hVar hc hη
  filter_upwards [hev, eventually_gt_atTop (0 : ℕ)] with k hk hk0
  intro m hkm
  have hmono :
      P.real {ω | c * Real.sqrt (m : ℝ) ≤ |psum X k ω|} ≤
        P.real {ω | c ≤ |(Real.sqrt (k : ℝ))⁻¹ * psum X k ω|} :=
    measureReal_mono (donsker_psum_tail_subset_normalized X hc.le hk0 hkm)
  exact (mul_le_mul_of_nonneg_left hmono (sq_nonneg c)).trans hk

private lemma donsker_fourth_bound_div_eventually {ε : ℝ} (hε : 0 < ε) :
    ∃ L > 0, ∀ c, L ≤ c → donskerGaussianFourthBound / c ^ 2 ≤ ε := by
  have hC : 0 ≤ donskerGaussianFourthBound := by
    unfold donskerGaussianFourthBound
    positivity
  let L := 1 + donskerGaussianFourthBound / ε
  have hL : 0 < L := by
    dsimp [L]
    positivity
  refine ⟨L, hL, fun c hLc => ?_⟩
  have hc : 0 < c := hL.trans_le hLc
  have hc1 : 1 ≤ c := by
    calc
      1 ≤ L := by
        dsimp [L]
        exact le_add_of_nonneg_right (div_nonneg hC hε.le)
      _ ≤ c := hLc
  have hCε : donskerGaussianFourthBound ≤ ε * c := by
    have hdiv : donskerGaussianFourthBound / ε ≤ c := by
      dsimp [L] at hLc
      linarith
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hdiv
  apply (div_le_iff₀ (sq_pos_of_pos hc)).2
  nlinarith

private lemma donsker_partial_sum_tail_uniform
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1) {η : ℝ} (hη : 0 < η) :
    ∃ L > 0, ∀ c, L ≤ c → ∀ᶠ m : ℕ in atTop, ∀ k ≤ m,
      c ^ 2 * P.real {ω | c * Real.sqrt (m : ℝ) ≤ |psum X k ω|} ≤ η := by
  obtain ⟨L, hL, hfourth⟩ := donsker_fourth_bound_div_eventually (half_pos hη)
  refine ⟨L, hL, fun c hLc => ?_⟩
  have hc : 0 < c := hL.trans_le hLc
  have hlarge := donsker_psum_tail_large_index_eventually X hIndep hIdent hMean hVar
    hc (half_pos hη)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hlarge
  have hmdiv : ∀ᶠ m : ℕ in atTop, (K : ℝ) / η ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((K : ℝ) / η))
  filter_upwards [hmdiv, eventually_gt_atTop (0 : ℕ)] with m hmdiv hm0
  have hmK : (K : ℝ) ≤ η * m := by
    rw [div_le_iff₀ hη] at hmdiv
    simpa only [Nat.cast_ofNat, mul_comm] using hmdiv
  intro k hkm
  by_cases hsmall : (k : ℝ) ≤ η * m
  · exact donsker_psum_tail_small_index X hIndep hIdent hMemLp hMean hVar hc hm0 hsmall
  · have hkgt : η * (m : ℝ) < k := lt_of_not_ge hsmall
    have hKk : K ≤ k := by
      exact_mod_cast (hmK.trans_lt hkgt).le
    exact (hK k hKk m hkm).trans (by linarith [hfourth c hLc])

private lemma donsker_etemadi_scaled_of_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (Y i)) (hIndep : iIndepFun Y P)
    {c η : ℝ} (hc : 0 < c) (hη : 0 < η) {m : ℕ}
    (htail : ∀ k ≤ m,
      c ^ 2 * P.real {ω | c * Real.sqrt (m : ℝ) ≤ |psum Y k ω|} ≤ η / 3) :
    c ^ 2 * P.real {ω | ∃ k ∈ Finset.range (m + 1),
      3 * (c * Real.sqrt (m : ℝ)) ≤ |psum Y k ω|} ≤ η := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  let M : ℝ≥0∞ := ⨆ k ∈ Finset.range (m + 1),
    P {ω | c * Real.sqrt (m : ℝ) ≤ |psum Y k ω|}
  have hq : 0 ≤ (η / 3) / c ^ 2 := div_nonneg (div_nonneg hη.le (by norm_num)) hc2.le
  have hpoint (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :
      P {ω | c * Real.sqrt (m : ℝ) ≤ |psum Y k ω|} ≤
        ENNReal.ofReal ((η / 3) / c ^ 2) := by
    have hkm : k ≤ m := by
      have := Finset.mem_range.mp hk
      omega
    have hreal : P.real {ω | c * Real.sqrt (m : ℝ) ≤ |psum Y k ω|} ≤
        (η / 3) / c ^ 2 := by
      rw [le_div_iff₀ hc2]
      simpa only [mul_comm] using htail k hkm
    apply (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).1
    simpa only [measureReal_def, ENNReal.toReal_ofReal hq] using hreal
  have hMbound : M ≤ ENNReal.ofReal ((η / 3) / c ^ 2) := by
    dsimp only [M]
    exact iSup_le fun k => iSup_le fun hk => hpoint k hk
  have hMtop : M ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMbound
  have hMreal : M.toReal ≤ (η / 3) / c ^ 2 := by
    have := (ENNReal.toReal_le_toReal hMtop ENNReal.ofReal_ne_top).2 hMbound
    simpa only [ENNReal.toReal_ofReal hq] using this
  have het := etemadi_maximal_inequality Y hMeas hIndep m
    (c * Real.sqrt (m : ℝ))
  change P {ω | ∃ k ∈ Finset.range (m + 1),
      3 * (c * Real.sqrt (m : ℝ)) ≤ |psum Y k ω|} ≤ 3 * M at het
  have hthreeMtop : (3 * M : ℝ≥0∞) ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hMtop
  have hetReal := (ENNReal.toReal_le_toReal (measure_ne_top P _) hthreeMtop).2 het
  have hmax : P.real {ω | ∃ k ∈ Finset.range (m + 1),
      3 * (c * Real.sqrt (m : ℝ)) ≤ |psum Y k ω|} ≤ 3 * M.toReal := by
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hetReal
  calc
    c ^ 2 * P.real {ω | ∃ k ∈ Finset.range (m + 1),
        3 * (c * Real.sqrt (m : ℝ)) ≤ |psum Y k ω|}
        ≤ c ^ 2 * (3 * M.toReal) := mul_le_mul_of_nonneg_left hmax hc2.le
    _ ≤ c ^ 2 * (3 * ((η / 3) / c ^ 2)) := by gcongr
    _ = η := by field_simp

private lemma donsker_maximal_partial_sum_tail_uniform
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1) {η : ℝ} (hη : 0 < η) :
    ∃ L > 0, ∀ c, L ≤ c → ∀ᶠ m : ℕ in atTop,
      c ^ 2 * P.real {ω | ∃ k ∈ Finset.range (m + 1),
        3 * (c * Real.sqrt (m : ℝ)) ≤ |psum X k ω|} ≤ η := by
  obtain ⟨L, hL, htail⟩ :=
    donsker_partial_sum_tail_uniform X hIndep hIdent hMemLp hMean hVar
      (div_pos hη (by norm_num : (0 : ℝ) < 3))
  refine ⟨L, hL, fun c hLc => ?_⟩
  have hc : 0 < c := hL.trans_le hLc
  filter_upwards [htail c hLc] with m hm
  exact donsker_etemadi_scaled_of_tail_bound X hMeas hIndep hc hη hm

private lemma donsker_shifted_psum_tail_real_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) (start k : ℕ) (a : ℝ) :
    P.real {ω | a ≤ |psum (fun i => X (start + i)) k ω|} =
      P.real {ω | a ≤ |psum X k ω|} := by
  have hset : MeasurableSet {x : ℝ | a ≤ |x|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have h := (shifted_ident X hIndep hIdent start k).measure_preimage_eq hset
  change P {ω | a ≤ |∑ i ∈ Finset.range k, X (start + i) ω|} =
    P {ω | a ≤ |∑ i ∈ Finset.range k, X i ω|} at h
  have h' := congrArg ENNReal.toReal h
  simpa only [measureReal_def, psum] using h'

private lemma donsker_block_maximal_partial_sum_tail_uniform
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1) {η : ℝ} (hη : 0 < η) :
    ∃ L > 0, ∀ c, L ≤ c → ∀ᶠ m : ℕ in atTop, ∀ start,
      c ^ 2 * P.real {ω | ∃ k ∈ Finset.range (m + 1),
        3 * (c * Real.sqrt (m : ℝ)) ≤
          |psum (fun i => X (start + i)) k ω|} ≤ η := by
  obtain ⟨L, hL, htail⟩ :=
    donsker_partial_sum_tail_uniform X hIndep hIdent hMemLp hMean hVar
      (div_pos hη (by norm_num : (0 : ℝ) < 3))
  refine ⟨L, hL, fun c hLc => ?_⟩
  have hc : 0 < c := hL.trans_le hLc
  filter_upwards [htail c hLc] with m hm
  intro start
  apply donsker_etemadi_scaled_of_tail_bound (fun i => X (start + i))
    (fun i => hMeas (start + i))
    (hIndep.precomp (fun _ _ h => Nat.add_left_cancel h)) hc hη
  intro k hkm
  rw [donsker_shifted_psum_tail_real_eq X hIndep hIdent start k]
  exact hm k hkm

private lemma donsker_psum_add {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω)
    (start k : ℕ) :
    psum X (start + k) ω =
      psum X start ω + psum (fun i => X (start + i)) k ω := by
  simp only [psum, Finset.sum_range_add]

private lemma donskerProcess_apply_eq_convex {Ω : Type*} (n : ℕ)
    (X : ℕ → Ω → ℝ) (ω : Ω) (t : Set.Icc (0 : ℝ) 1) (hn : n ≠ 0) :
    let j := Nat.floor ((n : ℝ) * t.1)
    let r := (n : ℝ) * t.1 - j
    donskerProcess n X ω t =
      if j < n then
        ((1 - r) * psum X j ω + r * psum X (j + 1) ω) / Real.sqrt (n : ℝ)
      else psum X j ω / Real.sqrt (n : ℝ) := by
  rw [donskerProcess_apply_eq n X ω t hn]
  dsimp only
  split_ifs with hj
  · rw [show psum X (Nat.floor ((n : ℝ) * t.1) + 1) ω =
        psum X (Nat.floor ((n : ℝ) * t.1)) ω +
          X (Nat.floor ((n : ℝ) * t.1)) ω by
      simp only [psum, Finset.sum_range_succ]]
    simp only [psum]
    ring
  · simp only [psum, add_zero]

private lemma donsker_abs_convex_le {a b r A : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : |a| ≤ A) (hb : |b| ≤ A) :
    |(1 - r) * a + r * b| ≤ A := by
  calc
    |(1 - r) * a + r * b| ≤ |(1 - r) * a| + |r * b| := abs_add_le _ _
    _ = (1 - r) * |a| + r * |b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hr1), abs_of_nonneg hr0]
    _ ≤ (1 - r) * A + r * A := by gcongr
    _ = A := by ring

private lemma donskerProcess_sub_psum_le {Ω : Type*} (n : ℕ)
    (X : ℕ → Ω → ℝ) (ω : Ω) (t : Set.Icc (0 : ℝ) 1) (hn : n ≠ 0)
    (start M : ℕ) (A : ℝ)
    (hstart : start ≤ Nat.floor ((n : ℝ) * t.1))
    (hjM : Nat.floor ((n : ℝ) * t.1) ≤ start + M)
    (hsucc : Nat.floor ((n : ℝ) * t.1) < n →
      Nat.floor ((n : ℝ) * t.1) + 1 ≤ start + M)
    (hblock : ∀ k ≤ M, |psum (fun i => X (start + i)) k ω| ≤ A) :
    |donskerProcess n X ω t - psum X start ω / Real.sqrt (n : ℝ)| ≤
      A / Real.sqrt (n : ℝ) := by
  let j := Nat.floor ((n : ℝ) * t.1)
  let r := (n : ℝ) * t.1 - j
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hr0 : 0 ≤ r := Nat.zero_le_self_sub_floor
    (mul_nonneg (Nat.cast_nonneg n) t.2.1)
  have hr1 : r ≤ 1 := (Nat.self_sub_floor_lt_one ((n : ℝ) * t.1)).le
  have hdiff (k : ℕ) (hk : start ≤ k) (hkM : k ≤ start + M) :
      |psum X k ω - psum X start ω| ≤ A := by
    have hsub : k - start ≤ M := by omega
    have hadd := donsker_psum_add X ω start (k - start)
    rw [Nat.add_sub_of_le hk] at hadd
    rw [hadd, add_sub_cancel_left]
    exact hblock (k - start) hsub
  rw [donskerProcess_apply_eq_convex n X ω t hn]
  split_ifs with hjn
  · have hconv :
        |(1 - r) * (psum X j ω - psum X start ω) +
            r * (psum X (j + 1) ω - psum X start ω)| ≤ A :=
      donsker_abs_convex_le hr0 hr1
        (hdiff j hstart hjM) (hdiff (j + 1) (by omega) (hsucc hjn))
    have heq :
        (1 - r) * psum X j ω + r * psum X (j + 1) ω - psum X start ω =
          (1 - r) * (psum X j ω - psum X start ω) +
            r * (psum X (j + 1) ω - psum X start ω) := by
      ring
    rw [← sub_div, abs_div, abs_of_pos hsqrt]
    apply div_le_div_of_nonneg_right _ hsqrt.le
    rw [heq]
    exact hconv
  · rw [← sub_div, abs_div, abs_of_pos hsqrt]
    exact div_le_div_of_nonneg_right (hdiff j hstart hjM) hsqrt.le

private lemma donsker_bad_oscillation_subset_block_max
    {Ω : Type*} (X : ℕ → Ω → ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    {ω | ∃ s t : Set.Icc (0 : ℝ) 1,
        dist s t ≤ (m : ℝ) / n ∧
          ε ≤ dist (donskerProcess n X ω s) (donskerProcess n X ω t)} ⊆
      {ω | ∃ q ∈ Finset.range (n / m + 1),
        ∃ k ∈ Finset.range ((2 * m + 1) + 1),
          ε * Real.sqrt (n : ℝ) / 3 ≤
            |psum (fun i => X (q * m + i)) k ω|} := by
  intro ω hω
  obtain ⟨s, t, hdist, hbad⟩ := hω
  have hord (s t : Set.Icc (0 : ℝ) 1) (hst : (s : ℝ) ≤ t)
      (hdist : dist s t ≤ (m : ℝ) / n)
      (hbad : ε ≤ dist (donskerProcess n X ω s) (donskerProcess n X ω t)) :
      ∃ q ∈ Finset.range (n / m + 1),
        ∃ k ∈ Finset.range ((2 * m + 1) + 1),
          ε * Real.sqrt (n : ℝ) / 3 ≤
            |psum (fun i => X (q * m + i)) k ω| := by
    let js := Nat.floor ((n : ℝ) * s.1)
    let jt := Nat.floor ((n : ℝ) * t.1)
    let q := js / m
    let start := q * m
    let M := 2 * m + 1
    let A := ε * Real.sqrt (n : ℝ) / 3
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
    have hjsn : js ≤ n := by
      exact Nat.floor_le_of_le (by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left s.2.2 (Nat.cast_nonneg n))
    have hqmem : q ∈ Finset.range (n / m + 1) := by
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hjsn)
    refine ⟨q, hqmem, ?_⟩
    have hstartjs : start ≤ js := by
      dsimp only [start, q]
      simpa only [mul_comm] using Nat.div_mul_le_self js m
    have hjslt : js < start + m := by
      have hmod := Nat.mod_lt js hm
      have hdecomp := Nat.mod_add_div js m
      dsimp only [start, q]
      simp only [mul_comm] at hdecomp ⊢
      omega
    have hjsjt : js ≤ jt := by
      exact Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg n))
    have hts : (t : ℝ) - s ≤ (m : ℝ) / n := by
      change |(s : ℝ) - t| ≤ (m : ℝ) / n at hdist
      rw [abs_of_nonpos (sub_nonpos.mpr hst)] at hdist
      simpa only [neg_sub] using hdist
    have hscaled : (n : ℝ) * ((t : ℝ) - s) ≤ m := by
      have := (le_div_iff₀ hnR).mp hts
      nlinarith
    have hnslt : (n : ℝ) * s < (js : ℝ) + 1 := by
      exact Nat.lt_floor_add_one _
    have hntlt : (n : ℝ) * t < (js + m + 1 : ℕ) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hjtle : jt ≤ js + m := by
      have hjtcast : (jt : ℝ) ≤ (n : ℝ) * t :=
        Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) t.2.1)
      have : jt < js + m + 1 := by exact_mod_cast hjtcast.trans_lt hntlt
      omega
    have hstartjt : start ≤ jt := hstartjs.trans hjsjt
    have hjsM : js ≤ start + M := by dsimp only [M]; omega
    have hjsSucc : js < n → js + 1 ≤ start + M := by
      intro
      dsimp only [M]
      omega
    have hjtM : jt ≤ start + M := by dsimp only [M]; omega
    have hjtSucc : jt < n → jt + 1 ≤ start + M := by
      intro
      dsimp only [M]
      omega
    by_contra hlarge
    have hblock (k : ℕ) (hk : k ≤ M) :
        |psum (fun i => X (start + i)) k ω| ≤ A := by
      have hkmem : k ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
      have hnot : ¬A ≤ |psum (fun i => X (start + i)) k ω| := by
        intro hkA
        apply hlarge
        simpa only [M, A, start, q] using ⟨k, hkmem, hkA⟩
      exact (lt_of_not_ge hnot).le
    have hsbound := donskerProcess_sub_psum_le n X ω s hn.ne'
      start M A hstartjs hjsM hjsSucc hblock
    have htbound := donskerProcess_sub_psum_le n X ω t hn.ne'
      start M A hstartjt hjtM hjtSucc hblock
    have hAdiv : A / Real.sqrt (n : ℝ) = ε / 3 := by
      dsimp only [A]
      field_simp
    rw [hAdiv] at hsbound htbound
    have hclose : dist (donskerProcess n X ω s) (donskerProcess n X ω t) < ε := by
      calc
        dist (donskerProcess n X ω s) (donskerProcess n X ω t)
            ≤ dist (donskerProcess n X ω s)
                (psum X start ω / Real.sqrt (n : ℝ)) +
              dist (psum X start ω / Real.sqrt (n : ℝ))
                (donskerProcess n X ω t) := dist_triangle _ _ _
        _ ≤ ε / 3 + ε / 3 := by
          rw [Real.dist_eq, Real.dist_eq, abs_sub_comm
            (psum X start ω / Real.sqrt (n : ℝ))]
          exact add_le_add hsbound htbound
        _ < ε := by linarith
    exact (not_lt_of_ge hbad) hclose
  rcases le_total (s : ℝ) t with hst | hts
  · exact hord s t hst hdist hbad
  · exact hord t s hts (by simpa only [dist_comm] using hdist)
      (by simpa only [dist_comm] using hbad)

private lemma donsker_oscillation_eventually
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∀ᶠ n : ℕ in atTop,
      P.real {ω | ∃ s t : Set.Icc (0 : ℝ) 1,
        dist s t ≤ δ ∧
          ε ≤ dist (donskerProcess n X ω s) (donskerProcess n X ω t)} ≤ η := by
  let θ := η * ε ^ 2 / 3600
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  obtain ⟨L, hL, hmax⟩ :=
    donsker_block_maximal_partial_sum_tail_uniform
      X hMeas hIndep hIdent hMemLp hMean hVar hθ
  let R := 30 * L / ε
  let q := Nat.ceil (R ^ 2) + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hq : 0 < q := by dsimp only [q]; omega
  let c := ε * Real.sqrt (q : ℝ) / 30
  have hc : 0 < c := by dsimp only [c]; positivity
  have hR2q : R ^ 2 ≤ (q : ℝ) := by
    have hceil := Nat.le_ceil (R ^ 2)
    dsimp only [q]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hRsqrt : R ≤ Real.sqrt (q : ℝ) :=
    (Real.le_sqrt hR.le (Nat.cast_nonneg q)).2 hR2q
  have hLc : L ≤ c := by
    dsimp only [R] at hRsqrt
    dsimp only [c]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 30)]
    have hs := (div_le_iff₀ hε).mp hRsqrt
    simpa only [mul_comm] using hs
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hmax c hLc)
  refine ⟨1 / (q : ℝ), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max (3 * q) (q * K))] with n hn
  have hn3q : 3 * q ≤ n := (le_max_left _ _).trans hn
  have hnqK : q * K ≤ n := (le_max_right _ _).trans hn
  have hn : 0 < n := lt_of_lt_of_le (by positivity : 0 < 3 * q) hn3q
  let m := Nat.ceil ((n : ℝ) / q)
  let M := 2 * m + 1
  let A := ε * Real.sqrt (n : ℝ) / 3
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hm : 0 < m := by
    rw [Nat.ceil_pos]
    exact div_pos hnR hqR
  have hmLower : (n : ℝ) / q ≤ m := Nat.le_ceil _
  have hmUpper : (m : ℝ) < (n : ℝ) / q + 1 := by
    exact Nat.ceil_lt_add_one (div_nonneg hnR.le hqR.le)
  have hnqm : n ≤ q * m := by
    have : n ≤ m * q := by exact_mod_cast ((div_le_iff₀ hqR).mp hmLower)
    simpa only [mul_comm] using this
  have hblocks : n / m + 1 ≤ q + 1 := by
    exact Nat.add_le_add_right (Nat.div_le_of_le_mul (by simpa [mul_comm] using hnqm)) 1
  have hKM : K ≤ M := by
    have hKm : K ≤ m := by
      have hcast : (K : ℝ) ≤ (n : ℝ) / q := by
        rw [le_div_iff₀ hqR]
        exact_mod_cast (by simpa only [mul_comm] using hnqK)
      exact_mod_cast hcast.trans hmLower
    dsimp only [M]
    omega
  have hMbound : (q : ℝ) * M ≤ 3 * n := by
    have hratio : (3 : ℝ) ≤ (n : ℝ) / q := by
      rw [le_div_iff₀ hqR]
      exact_mod_cast hn3q
    dsimp only [M]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have : (2 : ℝ) * m + 1 ≤ 3 * ((n : ℝ) / q) := by linarith
    calc
      (q : ℝ) * ((2 : ℝ) * m + 1)
          ≤ q * (3 * ((n : ℝ) / q)) := mul_le_mul_of_nonneg_left this hqR.le
      _ = 3 * n := by field_simp
  have hsqrtProd : Real.sqrt (q : ℝ) * Real.sqrt (M : ℝ) ≤
      2 * Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).1
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg q), Real.sq_sqrt (Nat.cast_nonneg M),
      mul_pow, Real.sq_sqrt hnR.le]
    nlinarith
  have hthreshold : 3 * (c * Real.sqrt (M : ℝ)) ≤ A := by
    calc
      3 * (c * Real.sqrt (M : ℝ)) =
          ε / 10 * (Real.sqrt (q : ℝ) * Real.sqrt (M : ℝ)) := by
        dsimp only [c]
        ring
      _ ≤ ε / 10 * (2 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtProd (by positivity)
      _ ≤ A := by
        dsimp only [A]
        nlinarith [mul_nonneg hε.le (Real.sqrt_nonneg (n : ℝ))]
  have hδm : 1 / (q : ℝ) ≤ (m : ℝ) / n := by
    rw [div_le_div_iff₀ hqR hnR]
    have hcast : (n : ℝ) ≤ (q : ℝ) * m := by exact_mod_cast hnqm
    calc
      (1 : ℝ) * n = n := one_mul _
      _ ≤ (q : ℝ) * m := hcast
      _ = (m : ℝ) * q := mul_comm _ _
  let block : ℕ → Set Ω := fun start =>
    {ω | ∃ k ∈ Finset.range (M + 1),
      A ≤ |psum (fun i => X (start + i)) k ω|}
  have hblockProb (start : ℕ) : P.real (block start) ≤ θ / c ^ 2 := by
    have hsubset : block start ⊆
        {ω | ∃ k ∈ Finset.range (M + 1),
          3 * (c * Real.sqrt (M : ℝ)) ≤
            |psum (fun i => X (start + i)) k ω|} := by
      rintro ω ⟨k, hk, hkA⟩
      exact ⟨k, hk, hthreshold.trans hkA⟩
    have hmono := measureReal_mono (μ := P) hsubset (measure_ne_top P _)
    have htail := hK M hKM start
    rw [le_div_iff₀ (sq_pos_of_pos hc)]
    calc
      P.real (block start) * c ^ 2 = c ^ 2 * P.real (block start) := mul_comm _ _
      _ ≤ θ := (mul_le_mul_of_nonneg_left hmono (sq_nonneg c)).trans htail
  have hcover :
      {ω | ∃ s t : Set.Icc (0 : ℝ) 1,
        dist s t ≤ 1 / (q : ℝ) ∧
          ε ≤ dist (donskerProcess n X ω s) (donskerProcess n X ω t)} ⊆
        ⋃ start ∈ Finset.range (n / m + 1), block (start * m) := by
    intro ω hω
    have hdet := donsker_bad_oscillation_subset_block_max X hn hm hε
    obtain ⟨s, t, hst, hbad⟩ := hω
    have hdet' := hdet ⟨s, t, hst.trans hδm, hbad⟩
    obtain ⟨start, hstart, k, hk, hklarge⟩ := hdet'
    refine Set.mem_iUnion.2 ⟨start, Set.mem_iUnion.2 ⟨hstart, ?_⟩⟩
    exact ⟨k, by simpa only [M] using hk, by simpa only [block, M, A] using hklarge⟩
  have hunion := measureReal_biUnion_finset_le
    (μ := P) (Finset.range (n / m + 1)) (fun start => block (start * m))
  calc
    P.real {ω | ∃ s t : Set.Icc (0 : ℝ) 1,
        dist s t ≤ 1 / (q : ℝ) ∧
          ε ≤ dist (donskerProcess n X ω s) (donskerProcess n X ω t)}
        ≤ P.real (⋃ start ∈ Finset.range (n / m + 1), block (start * m)) :=
      measureReal_mono (μ := P) hcover (measure_ne_top P _)
    _ ≤ ∑ start ∈ Finset.range (n / m + 1), P.real (block (start * m)) := hunion
    _ ≤ ∑ _start ∈ Finset.range (n / m + 1), θ / c ^ 2 := by
      exact Finset.sum_le_sum fun start _ => hblockProb (start * m)
    _ = ((n / m + 1 : ℕ) : ℝ) * (θ / c ^ 2) := by simp
    _ ≤ (2 * q : ℕ) * (θ / c ^ 2) := by
      gcongr
      omega
    _ = η / 2 := by
      dsimp only [θ, c]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
      field_simp [hε.ne', hqR.ne']
      all_goals ring
    _ ≤ η := by linarith

private lemma donsker_norm_tail_subset_max
    {Ω : Type*} (X : ℕ → Ω → ℝ) {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 < c) :
    {ω | 3 * c < ‖donskerProcess n X ω‖} ⊆
      {ω | ∃ k ∈ Finset.range (n + 1),
        3 * (c * Real.sqrt (n : ℝ)) ≤ |psum X k ω|} := by
  intro ω hω
  by_contra hlarge
  have hblock (k : ℕ) (hk : k ≤ n) :
      |psum (fun i => X (0 + i)) k ω| ≤ 3 * (c * Real.sqrt (n : ℝ)) := by
    have hkmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hnot : ¬3 * (c * Real.sqrt (n : ℝ)) ≤ |psum X k ω| := by
      intro hklarge
      exact hlarge ⟨k, hkmem, hklarge⟩
    simpa only [zero_add] using (lt_of_not_ge hnot).le
  have hfloor (t : Set.Icc (0 : ℝ) 1) :
      Nat.floor ((n : ℝ) * t.1) ≤ n :=
    Nat.floor_le_of_le (by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left t.2.2 (Nat.cast_nonneg n))
  have hpoint (t : Set.Icc (0 : ℝ) 1) :
      |donskerProcess n X ω t| ≤ 3 * c := by
    have h := donskerProcess_sub_psum_le n X ω t hn.ne' 0 n
      (3 * (c * Real.sqrt (n : ℝ))) (Nat.zero_le _)
      (by simpa only [zero_add] using hfloor t) (by intro; omega) hblock
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
    simpa only [psum, Finset.sum_range_zero, zero_div, sub_zero, mul_div_assoc,
      div_self hsqrt.ne', mul_one] using h
  have hnorm : ‖donskerProcess n X ω‖ ≤ 3 * c := by
    apply (ContinuousMap.norm_le (donskerProcess n X ω)
      (mul_nonneg (by norm_num) hc.le)).2
    intro t
    simpa only [Real.norm_eq_abs] using hpoint t
  exact (not_lt_of_ge hnorm) hω

private lemma donsker_norm_tail_eventually
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1) {η : ℝ} (hη : 0 < η) :
    ∃ R > 0, ∀ᶠ n : ℕ in atTop,
      P.real {ω | R < ‖donskerProcess n X ω‖} ≤ η := by
  obtain ⟨L, hL, hmax⟩ :=
    donsker_maximal_partial_sum_tail_uniform
      X hMeas hIndep hIdent hMemLp hMean hVar hη
  let c := max L 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hLc : L ≤ c := le_max_left _ _
  refine ⟨3 * c, mul_pos (by norm_num) hc, ?_⟩
  filter_upwards [hmax c hLc, eventually_gt_atTop (0 : ℕ)] with n hnmax hn
  have hmono := measureReal_mono (μ := P)
    (donsker_norm_tail_subset_max X hn hc) (measure_ne_top P _)
  have hc1 : 1 ≤ c ^ 2 := by nlinarith [le_max_right L 1]
  calc
    P.real {ω | 3 * c < ‖donskerProcess n X ω‖}
        ≤ P.real {ω | ∃ k ∈ Finset.range (n + 1),
          3 * (c * Real.sqrt (n : ℝ)) ≤ |psum X k ω|} := hmono
    _ ≤ c ^ 2 * P.real {ω | ∃ k ∈ Finset.range (n + 1),
          3 * (c * Real.sqrt (n : ℝ)) ≤ |psum X k ω|} := by
      exact le_mul_of_one_le_left measureReal_nonneg hc1
    _ ≤ η := hnmax

private lemma donsker_isCompact_equicontinuous
    {C : Set C(Set.Icc (0 : ℝ) 1, ℝ)} (hC : IsCompact C) :
    Equicontinuous ((↑) : C → Set.Icc (0 : ℝ) 1 → ℝ) := by
  have hcompact : IsCompact (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1))) :=
    hC.prod isCompact_univ
  have heval : Continuous (fun p : C(Set.Icc (0 : ℝ) 1, ℝ) × Set.Icc (0 : ℝ) 1 =>
      p.1 p.2) := continuous_eval
  have huc := hcompact.uniformContinuousOn_of_continuous heval.continuousOn
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := (Metric.uniformContinuousOn_iff.mp huc) ε hε
  refine ⟨δ, hδ, fun y hy f => ?_⟩
  have hp : ((f.1, x) : C(Set.Icc (0 : ℝ) 1, ℝ) × Set.Icc (0 : ℝ) 1) ∈
      C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) := ⟨f.2, Set.mem_univ _⟩
  have hq : ((f.1, y) : C(Set.Icc (0 : ℝ) 1, ℝ) × Set.Icc (0 : ℝ) 1) ∈
      C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) := ⟨f.2, Set.mem_univ _⟩
  apply hcontrol (f.1, x) hp (f.1, y) hq
  rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
  simpa only [dist_comm] using hy

private lemma donsker_isCompact_closure_of_bounded_equicontinuous
    {A : Set C(Set.Icc (0 : ℝ) 1, ℝ)} {R : ℝ}
    (hbound : ∀ f ∈ A, ‖f‖ ≤ R)
    (hequi : Equicontinuous ((↑) : A → Set.Icc (0 : ℝ) 1 → ℝ)) :
    IsCompact (closure A) := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact (Set.Icc (0 : ℝ) 1) ℝ
  let D : Set (BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) := e '' A
  have hin (g : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ)
      (x : Set.Icc (0 : ℝ) 1) (hg : g ∈ D) : g x ∈ Metric.closedBall 0 R := by
    obtain ⟨f, hf, rfl⟩ := hg
    have hfx := (ContinuousMap.norm_coe_le_norm f x).trans (hbound f hf)
    change f x ∈ Metric.closedBall 0 R
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, Real.norm_eq_abs] using hfx
  let u : D → A := fun g => ⟨e.symm g.1, by
    obtain ⟨f, hf, hfg⟩ := g.2
    have : e.symm g.1 = f := by
      calc
        e.symm g.1 = e.symm (e f) := congrArg e.symm hfg.symm
        _ = f := e.symm_apply_apply f
    rwa [this]⟩
  have hequiD : Equicontinuous ((↑) : D → Set.Icc (0 : ℝ) 1 → ℝ) := by
    have h := hequi.comp u
    have hfun :
        (fun g : D => fun x => (u g).1 x) = (fun g : D => fun x => g.1 x) := by
      funext g x
      rfl
    rw [← hfun]
    exact h
  have hD : IsCompact (closure D) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) R)
      (isCompact_closedBall (0 : ℝ) R) D hin hequiD
  have himage : e '' closure A = closure D := by
    have h := e.toHomeomorph.image_closure A
    change e '' closure A = closure (e '' A) at h
    simpa only [D] using h
  have heq : e.symm '' closure D = closure A := by
    rw [← himage]
    apply Set.Subset.antisymm
    · rintro f ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      simpa only [e.symm_apply_apply] using hg
    · intro f hf
      exact ⟨e f, ⟨f, hf, rfl⟩, e.symm_apply_apply f⟩
  rw [← heq]
  exact hD.image e.symm.continuous

private lemma donsker_compact_capture
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → C(Set.Icc (0 : ℝ) 1, ℝ)} (hW : Measurable W)
    {b : ℝ} (hb : 0 < b) :
    ∃ C : Set C(Set.Icc (0 : ℝ) 1, ℝ), IsCompact C ∧
      P.real {ω | W ω ∉ C} ≤ b := by
  let _ : IsFiniteMeasure (P.map W) := P.isFiniteMeasure_map W
  have htight : IsTightMeasureSet {P.map W} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨C, hC, hbound⟩ := htight (ENNReal.ofReal b) (ENNReal.ofReal_pos.2 hb)
  refine ⟨C, hC, ?_⟩
  have hmap := hbound (P.map W) (Set.mem_singleton _)
  rw [Measure.map_apply_of_aemeasurable hW.aemeasurable hC.isClosed.measurableSet.compl] at hmap
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).2 hmap
  change (P (W ⁻¹' Cᶜ)).toReal ≤ b
  simpa only [ENNReal.toReal_ofReal hb.le] using hreal

private lemma donsker_oscillation_schedule
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1) {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℕ → ℝ, ∃ N : ℕ → ℕ,
      (∀ j, 0 < δ j) ∧ (∀ j, j ≤ N j) ∧
        ∀ j n, N j ≤ n →
          P.real {ω | ∃ s t : Set.Icc (0 : ℝ) 1,
            dist s t ≤ δ j ∧
              1 / ((j : ℝ) + 1) ≤
                dist (donskerProcess n X ω s) (donskerProcess n X ω t)} ≤
            b / 8 * (1 / 2 : ℝ) ^ j := by
  have hdata (j : ℕ) :
      ∃ δ > 0, ∃ N : ℕ, j ≤ N ∧ ∀ n, N ≤ n →
        P.real {ω | ∃ s t : Set.Icc (0 : ℝ) 1,
          dist s t ≤ δ ∧
            1 / ((j : ℝ) + 1) ≤
              dist (donskerProcess n X ω s) (donskerProcess n X ω t)} ≤
          b / 8 * (1 / 2 : ℝ) ^ j := by
    have hjε : 0 < 1 / ((j : ℝ) + 1) := by positivity
    have hjb : 0 < b / 8 * (1 / 2 : ℝ) ^ j := by positivity
    obtain ⟨δ, hδ, hev⟩ := donsker_oscillation_eventually
      X hMeas hIndep hIdent hMemLp hMean hVar hjε hjb
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨δ, hδ, max N j, le_max_right _ _, fun n hn => ?_⟩
    exact hN n ((le_max_left _ _).trans hn)
  choose δ hδ N hjN hprob using hdata
  exact ⟨δ, N, hδ, hjN, hprob⟩

private def donskerGoodFamily
    (C : ℕ → Set C(Set.Icc (0 : ℝ) 1, ℝ)) (R : ℝ) (NR : ℕ)
    (δ : ℕ → ℝ) (N : ℕ → ℕ) : Set C(Set.Icc (0 : ℝ) 1, ℝ) :=
  {f | ∃ n, f ∈ C n ∧ (NR ≤ n → ‖f‖ ≤ R) ∧
    ∀ j, N j ≤ n → ∀ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ j →
      dist (f s) (f t) < 1 / ((j : ℝ) + 1)}

private lemma donsker_good_family_compact
    (C : ℕ → Set C(Set.Icc (0 : ℝ) 1, ℝ)) (hC : ∀ n, IsCompact (C n))
    (R : ℝ) (NR : ℕ) (δ : ℕ → ℝ) (N : ℕ → ℕ)
    (hδ : ∀ j, 0 < δ j) :
    IsCompact (closure (donskerGoodFamily C R NR δ N)) := by
  let CEarly : Set C(Set.Icc (0 : ℝ) 1, ℝ) := ⋃ n ∈ Finset.range NR, C n
  have hCEarly : IsCompact CEarly := by
    exact (Finset.range NR).isCompact_biUnion fun n _ => hC n
  obtain ⟨S, hS⟩ :=
    (Metric.isBounded_iff_subset_closedBall
      (0 : C(Set.Icc (0 : ℝ) 1, ℝ))).mp hCEarly.isBounded
  have hbound (f : C(Set.Icc (0 : ℝ) 1, ℝ))
      (hf : f ∈ donskerGoodFamily C R NR δ N) : ‖f‖ ≤ max R S := by
    obtain ⟨n, hfn, hnorm, _⟩ := hf
    by_cases hn : NR ≤ n
    · exact (hnorm hn).trans (le_max_left _ _)
    · have hnlt : n < NR := lt_of_not_ge hn
      have hfearly : f ∈ CEarly := by
        refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hnlt, hfn⟩⟩
      have hfball := hS hfearly
      rw [Metric.mem_closedBall, dist_zero_right] at hfball
      exact hfball.trans (le_max_right _ _)
  have hequi : Equicontinuous
      ((↑) : donskerGoodFamily C R NR δ N → Set.Icc (0 : ℝ) 1 → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    let CSmall : Set C(Set.Icc (0 : ℝ) 1, ℝ) := ⋃ n ∈ Finset.range (N j), C n
    have hCSmall : IsCompact CSmall := by
      exact (Finset.range (N j)).isCompact_biUnion fun n _ => hC n
    have hearly := donsker_isCompact_equicontinuous hCSmall
    have hearlyAt := hearly x
    rw [Metric.equicontinuousAt_iff] at hearlyAt
    obtain ⟨d, hd, hcontrol⟩ := hearlyAt ε hε
    refine ⟨min d (δ j), lt_min hd (hδ j), fun y hy f => ?_⟩
    obtain ⟨n, hfn, _, hosc⟩ := f.2
    by_cases hjn : N j ≤ n
    · have hxy : dist x y ≤ δ j := by
        rw [dist_comm]
        exact (hy.trans_le (min_le_right _ _)).le
      exact (hosc j hjn x y hxy).trans hj
    · have hnlt : n < N j := lt_of_not_ge hjn
      have hfsmall : f.1 ∈ CSmall := by
        refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hnlt, hfn⟩⟩
      exact hcontrol y (hy.trans_le (min_le_left _ _)) ⟨f.1, hfsmall⟩
  exact donsker_isCompact_closure_of_bounded_equicontinuous hbound hequi

private lemma donsker_laws_isTightMeasureSet
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1) :
    IsTightMeasureSet (Set.range fun n =>
      P.map (fun ω => donskerProcess n X ω)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ζ hζ
  by_cases hζtop : ζ = ∞
  · exact ⟨∅, isCompact_empty, by simp only [hζtop, le_top, implies_true]⟩
  let b := ζ.toReal
  have hb : 0 < b := ENNReal.toReal_pos hζ.ne' hζtop
  have hcapture (n : ℕ) :
      ∃ C : Set C(Set.Icc (0 : ℝ) 1, ℝ), IsCompact C ∧
        P.real {ω | donskerProcess n X ω ∉ C} ≤ b / 4 :=
    donsker_compact_capture (donskerProcess_measurable X hMeas n) (div_pos hb (by norm_num))
  choose C hC hCprob using hcapture
  obtain ⟨R, hR, hnormEv⟩ := donsker_norm_tail_eventually
    X hMeas hIndep hIdent hMemLp hMean hVar (div_pos hb (by norm_num : (0 : ℝ) < 4))
  obtain ⟨NR, hnorm⟩ := eventually_atTop.1 hnormEv
  obtain ⟨δ, N, hδ, hjN, hosc⟩ := donsker_oscillation_schedule
    X hMeas hIndep hIdent hMemLp hMean hVar hb
  let A := donskerGoodFamily C R NR δ N
  let K := closure A
  have hK : IsCompact K := by
    exact donsker_good_family_compact C hC R NR δ N hδ
  refine ⟨K, hK, ?_⟩
  rintro μ ⟨n, rfl⟩
  let W : Ω → C(Set.Icc (0 : ℝ) 1, ℝ) := fun ω => donskerProcess n X ω
  let baseFail : Set Ω := {ω | W ω ∉ C n}
  let normFail : Set Ω := {ω | R < ‖W ω‖}
  let oscFail : ℕ → Set Ω := fun j =>
    {ω | ∃ s t : Set.Icc (0 : ℝ) 1,
      dist s t ≤ δ j ∧ 1 / ((j : ℝ) + 1) ≤ dist (W ω s) (W ω t)}
  let J := (Finset.range (n + 1)).filter fun j => N j ≤ n
  let allFail := baseFail ∪ (if NR ≤ n then normFail else ∅) ∪ ⋃ j ∈ J, oscFail j
  have hpre : W ⁻¹' Kᶜ ⊆ allFail := by
    intro ω hω
    by_cases hCω : W ω ∈ C n
    · by_cases hnR : NR ≤ n
      · by_cases hnormω : R < ‖W ω‖
        · exact Or.inl (Or.inr (by simp only [hnR, ite_true, normFail]; exact hnormω))
        · by_cases hoscω : ∀ j, N j ≤ n → ∀ s t : Set.Icc (0 : ℝ) 1,
              dist s t ≤ δ j → dist (W ω s) (W ω t) < 1 / ((j : ℝ) + 1)
          · exfalso
            apply hω
            apply subset_closure
            exact ⟨n, hCω, fun _ => le_of_not_gt hnormω, hoscω⟩
          · push Not at hoscω
            obtain ⟨j, hjn, s, t, hst, hbad⟩ := hoscω
            have hjJ : j ∈ J := by
              rw [Finset.mem_filter, Finset.mem_range]
              exact ⟨Nat.lt_succ_of_le ((hjN j).trans hjn), hjn⟩
            refine Or.inr (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjJ, ?_⟩⟩)
            exact ⟨s, t, hst, hbad⟩
      · by_cases hoscω : ∀ j, N j ≤ n → ∀ s t : Set.Icc (0 : ℝ) 1,
            dist s t ≤ δ j → dist (W ω s) (W ω t) < 1 / ((j : ℝ) + 1)
        · exfalso
          apply hω
          apply subset_closure
          exact ⟨n, hCω, fun h => False.elim (hnR h), hoscω⟩
        · push Not at hoscω
          obtain ⟨j, hjn, s, t, hst, hbad⟩ := hoscω
          have hjJ : j ∈ J := by
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨Nat.lt_succ_of_le ((hjN j).trans hjn), hjn⟩
          refine Or.inr (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjJ, ?_⟩⟩)
          exact ⟨s, t, hst, hbad⟩
    · exact Or.inl (Or.inl hCω)
  have hnormFail : P.real (if NR ≤ n then normFail else ∅) ≤ b / 4 := by
    by_cases hnR : NR ≤ n
    · simp only [hnR, ite_true, normFail, W]
      exact hnorm n hnR
    · simp only [hnR, ite_false, measureReal_empty]
      exact div_nonneg hb.le (by norm_num)
  have hoscUnion : P.real (⋃ j ∈ J, oscFail j) ≤ b / 4 := by
    calc
      P.real (⋃ j ∈ J, oscFail j)
          ≤ ∑ j ∈ J, P.real (oscFail j) :=
        measureReal_biUnion_finset_le J oscFail
      _ ≤ ∑ j ∈ J, b / 8 * (1 / 2 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn := (Finset.mem_filter.mp hj).2
        simpa only [oscFail, W] using hosc j n hjn
      _ ≤ ∑ j ∈ Finset.range (n + 1), b / 8 * (1 / 2 : ℝ) ^ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro j _ _
        positivity
      _ = b / 8 * ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
      _ ≤ b / 8 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
      _ = b / 4 := by ring
  have hallFail : P.real allFail ≤ b := by
    calc
      P.real allFail
          ≤ P.real baseFail + P.real (if NR ≤ n then normFail else ∅) +
              P.real (⋃ j ∈ J, oscFail j) := by
        dsimp only [allFail]
        calc
          P.real ((baseFail ∪ if NR ≤ n then normFail else ∅) ∪
              ⋃ j ∈ J, oscFail j)
              ≤ P.real (baseFail ∪ if NR ≤ n then normFail else ∅) +
                P.real (⋃ j ∈ J, oscFail j) := measureReal_union_le _ _
          _ ≤ (P.real baseFail + P.real (if NR ≤ n then normFail else ∅)) +
                P.real (⋃ j ∈ J, oscFail j) := by
            gcongr
            exact measureReal_union_le _ _
      _ ≤ b / 4 + b / 4 + b / 4 :=
        add_le_add (add_le_add (hCprob n) hnormFail) hoscUnion
      _ ≤ b := by linarith
  have hreal : P.real (W ⁻¹' Kᶜ) ≤ b :=
    (measureReal_mono (μ := P) hpre (measure_ne_top P _)).trans hallFail
  rw [Measure.map_apply_of_aemeasurable
    (donskerProcess_measurable X hMeas n).aemeasurable hK.isClosed.measurableSet.compl]
  apply (ENNReal.toReal_le_toReal (measure_ne_top P _) hζtop).1
  simpa only [measureReal_def, b, W] using hreal

private lemma donsker_continuous_finsetEval
    (I : Finset (Set.Icc (0 : ℝ) 1)) :
    Continuous (fun f : C(Set.Icc (0 : ℝ) 1, ℝ) =>
      I.restrict (fun t => f t)) := by
  apply continuous_pi
  intro t
  change Continuous (fun f : C(Set.Icc (0 : ℝ) 1, ℝ) => f (t : Set.Icc (0 : ℝ) 1))
  exact continuous_eval_const (t : Set.Icc (0 : ℝ) 1)

private lemma donskerBrownianPath_finsetEval_map
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P')
    (I : Finset (Set.Icc (0 : ℝ) 1)) :
    (P'.map (donskerBrownianPath B)).map
        (fun f : C(Set.Icc (0 : ℝ) 1, ℝ) => I.restrict (fun t => f t)) =
      P'.map (fun ω => I.restrict (fun t => B (iccToNNReal t) ω)) := by
  rw [AEMeasurable.map_map_of_aemeasurable
    (donsker_continuous_finsetEval I).measurable.aemeasurable
    (donskerBrownianPath_aemeasurable B hB)]
  apply Measure.map_congr
  filter_upwards [donskerBrownianPath_ae_eq B hB] with ω hω
  ext t
  exact hω t

private lemma donsker_process_tendstoInDistribution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X P) (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    TendstoInDistribution (fun n ω => donskerProcess n X ω) atTop
      (donskerBrownianPath B) (fun _ => P) P' where
  forall_aemeasurable n := (donskerProcess_measurable X hMeas n).aemeasurable
  aemeasurable_limit := donskerBrownianPath_aemeasurable B hB
  tendsto := by
    let laws : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ) 1, ℝ) := fun n =>
      ⟨P.map (fun ω => donskerProcess n X ω), inferInstance⟩
    let limitLaw : ProbabilityMeasure C(Set.Icc (0 : ℝ) 1, ℝ) :=
      ⟨P'.map (donskerBrownianPath B), inferInstance⟩
    change Tendsto laws atTop (𝓝 limitLaw)
    have htight : IsTightMeasureSet
        {((μ : ProbabilityMeasure C(Set.Icc (0 : ℝ) 1, ℝ)) :
          Measure C(Set.Icc (0 : ℝ) 1, ℝ)) | μ ∈ Set.range laws} := by
      have hset :
          {((μ : ProbabilityMeasure C(Set.Icc (0 : ℝ) 1, ℝ)) :
            Measure C(Set.Icc (0 : ℝ) 1, ℝ)) | μ ∈ Set.range laws} =
            Set.range (fun n => P.map (fun ω => donskerProcess n X ω)) := by
        ext ν
        constructor
        · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
          exact ⟨n, rfl⟩
        · rintro ⟨n, rfl⟩
          exact ⟨laws n, ⟨n, rfl⟩, rfl⟩
      rw [hset]
      exact donsker_laws_isTightMeasureSet X hMeas hIndep hIdent hMemLp hMean hVar
    apply tendsto_continuousPath_of_tight_of_finset_eval 1 (by norm_num)
      laws limitLaw htight
    intro I
    let e := fun f : C(Set.Icc (0 : ℝ) 1, ℝ) =>
      I.restrict (fun t => f t)
    change Tendsto (fun n => (laws n).map e) atTop (𝓝 (limitLaw.map e))
    have hfd := finsetEval_tendstoInDistribution X hMeas hIndep hIdent hMemLp
      hMean hVar B hB.toIsPreBrownianReal I
    have hmap : ∀ n, (laws n).map e =
        (⟨P.map (fun ω => I.restrict (fun t => donskerProcess n X ω t)),
          inferInstance⟩ :
          ProbabilityMeasure (I → ℝ)) := by
      intro n
      apply ProbabilityMeasure.toMeasure_injective
      change (P.map (fun ω => donskerProcess n X ω)).map e =
        P.map (fun ω => I.restrict (fun t => donskerProcess n X ω t))
      rw [Measure.map_map (donsker_continuous_finsetEval I).measurable
        (donskerProcess_measurable X hMeas n)]
      rfl
    have hlim : limitLaw.map e =
        (⟨P'.map (fun ω => I.restrict (fun t => B (iccToNNReal t) ω)),
          inferInstance⟩ :
          ProbabilityMeasure (I → ℝ)) := by
      apply ProbabilityMeasure.toMeasure_injective
      change (P'.map (donskerBrownianPath B)).map e =
        P'.map (fun ω => I.restrict (fun t => B (iccToNNReal t) ω))
      exact donskerBrownianPath_finsetEval_map B hB I
    simpa only [hmap, hlim] using hfd.tendsto

/--
If `X : ℕ → Ω → ℝ` is i.i.d. with mean `0`, variance `1` and `MemLp` `2`, then for any Brownian
motion `B` with `IsBrownianReal B P'` there exists `Y : Ω' → C([0, 1], ℝ)` restricting to `B` a.e.
on `[0, 1]` such that `donskerProcess n X` converges in distribution to `Y`. Source: M. D.
Donsker, An invariance principle for certain probability limit theorems, Mem. Amer. Math. Soc. 6
(1951); extension Prohorov 1956 to Polish; textbook in Billingsley, Convergence of Probability
Measures, 2nd ed., Kallenberg, Foundations of Modern Probability; Lean is `C(Icc 0 1, ℝ)`
polygonal process with `MemLp 2`, mean-zero variance-one standardization.

Proves `Wanted` entry `donsker_invariance_principle`.

Proof: The route combines finite-dimensional convergence from the central limit theorem,
tightness from a maximal inequality and a modulus-of-continuity criterion, Prokhorov's theorem,
and uniqueness of laws on `C([0,1])` from finite-dimensional distributions.
-/
public theorem donsker_invariance_principle
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (X n))
    (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hInt : Integrable (X 0) P)
    (hMemLp : MemLp (X 0) 2 P)
    (hMean : P[X 0] = 0)
    (hVar : Var[X 0; P] = 1)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    ∃ (Y : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ)),
      (∀ᵐ ω' ∂P', ∀ t : Set.Icc (0 : ℝ) 1, (Y ω' t) = B (iccToNNReal t) ω') ∧
      TendstoInDistribution (fun n (ω : Ω) => donskerProcess n X ω) Filter.atTop Y
        (fun _ => P) P' := by
  refine ⟨donskerBrownianPath B, donskerBrownianPath_ae_eq B hB, ?_⟩
  exact donsker_process_tendstoInDistribution X hMeas hIndep hIdent hMemLp hMean hVar B hB

end

end MathlibExt.Probability.DonskerWanted
