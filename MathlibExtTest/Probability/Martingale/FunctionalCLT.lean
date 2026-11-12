/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.FunctionalCLT

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Martingale MathlibExt.Probability.DonskerWanted

namespace MathlibExtTest.Probability.Martingale.FunctionalCLT

noncomputable section

/-! ### The D-space and the J1 distance -/

-- On continuous paths the J1 distance is bounded by the uniform distance.
example (f g : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    edist (SkorokhodSpace.ofContinuous f) (SkorokhodSpace.ofContinuous g) ≤ edist f g := by
  simpa using SkorokhodSpace.lipschitzWith_ofContinuous f g

-- Boundary: the unit step at `1/2` is a càdlàg path that is not continuous, so `D` is
-- strictly larger than `C`.
example : IsCadlag (stepInd 1 (1 / 2)) ∧ ¬ Continuous (stepInd 1 (1 / 2)) := by
  refine ⟨isCadlag_stepInd 1 (1 / 2), fun hc => ?_⟩
  let a : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hval : stepInd 1 (1 / 2) a = 1 := by simp [stepInd, a]
  have hleft : Tendsto (stepInd 1 (1 / 2)) (𝓝[<] a) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : (y : ℝ) < 1 / 2 := Subtype.coe_lt_coe.2 hy
    unfold stepInd
    exact (ite_eq_right_iff.2 fun h => absurd h (not_le.2 hy')).symm
  have hne : (𝓝[<] a).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    refine ⟨⟨1 / 2 - min ε (1 / 2) / 2, ?_, ?_⟩, ?_, ?_⟩
    · have := min_le_right ε (1 / 2); linarith
    · have := min_le_right ε (1 / 2); have := lt_min hε (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
    · show (_ : ℝ) < 1 / 2
      have := lt_min hε (by norm_num : (0 : ℝ) < 1 / 2); simp only; linarith
    · rw [Subtype.dist_eq]
      simp only [a, Real.dist_eq]
      have h1 := lt_min hε (by norm_num : (0 : ℝ) < 1 / 2)
      have h2 := min_le_left ε (1 / 2)
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hcont : Tendsto (stepInd 1 (1 / 2)) (𝓝[<] a) (𝓝 1) := by
    have h : Tendsto (stepInd 1 (1 / 2)) (𝓝[<] a) (𝓝 (stepInd 1 (1 / 2) a)) :=
      (hc.continuousAt (x := a)).tendsto.mono_left nhdsWithin_le_nhds
    rwa [hval] at h
  exact zero_ne_one (tendsto_nhds_unique hleft hcont)

/-! ### J1 is not the uniform topology -/

/-- Piecewise-linear time change of `[0,1]` sending `3/4` to `1/2`. -/
def shiftTime (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨if (t : ℝ) ≤ 3 / 4 then 2 / 3 * t else 2 * t - 1, by
    obtain ⟨t, h0, h1⟩ := t
    split_ifs with h <;> constructor <;> simp only <;> linarith⟩

lemma shiftTime_strictMono : StrictMono shiftTime := by
  rintro ⟨s, hs0, hs1⟩ ⟨t, ht0, ht1⟩ hst
  change s < t at hst
  change (if s ≤ 3 / 4 then 2 / 3 * s else 2 * s - 1) <
    (if t ≤ 3 / 4 then 2 / 3 * t else 2 * t - 1)
  split_ifs <;> linarith

lemma shiftTime_surjective : Function.Surjective shiftTime := by
  rintro ⟨u, hu0, hu1⟩
  by_cases hu : u ≤ 1 / 2
  · refine ⟨⟨3 / 2 * u, by linarith, by linarith⟩, Subtype.ext ?_⟩
    change (if 3 / 2 * u ≤ 3 / 4 then 2 / 3 * (3 / 2 * u) else 2 * (3 / 2 * u) - 1) = u
    split_ifs with h
    · ring
    · exfalso; linarith
  · push Not at hu
    refine ⟨⟨(u + 1) / 2, by linarith, by linarith⟩, Subtype.ext ?_⟩
    change (if (u + 1) / 2 ≤ 3 / 4 then 2 / 3 * ((u + 1) / 2) else 2 * ((u + 1) / 2) - 1) = u
    split_ifs with h
    · have : u = 1 / 2 := by linarith
      subst this; norm_num
    · ring

-- A unit jump at `3/4` and one at `1/2` are within J1 distance `1/4` ...
example : skorokhodEDist (stepInd 1 (3 / 4)) (stepInd 1 (1 / 2)) ≤ ENNReal.ofReal (1 / 4) := by
  let φ := StrictMono.orderIsoOfSurjective shiftTime shiftTime_strictMono shiftTime_surjective
  refine iInf_le_of_le φ (max_le (iSup_le fun t => ?_) (iSup_le fun t => ?_))
  · obtain ⟨t, h0, h1⟩ := t
    rw [edist_dist, Subtype.dist_eq, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    change |(if t ≤ 3 / 4 then 2 / 3 * t else 2 * t - 1) - t| ≤ 1 / 4
    split_ifs with h <;> rw [abs_le] <;> constructor <;> linarith
  · obtain ⟨t, h0, h1⟩ := t
    have heq : stepInd 1 (3 / 4) ⟨t, h0, h1⟩ = stepInd 1 (1 / 2) (φ ⟨t, h0, h1⟩) := by
      change stepInd 1 (3 / 4) ⟨t, h0, h1⟩ = stepInd 1 (1 / 2) (shiftTime ⟨t, h0, h1⟩)
      unfold stepInd shiftTime
      simp only
      split_ifs <;> first | rfl | (exfalso; linarith)
    rw [heq, edist_self]
    exact bot_le

-- ... while their uniform distance is `1` (compare at `t = 1/2`).
example : edist (stepInd 1 (3 / 4) ⟨1 / 2, by norm_num, by norm_num⟩)
    (stepInd 1 (1 / 2) ⟨1 / 2, by norm_num, by norm_num⟩) = 1 := by
  simp [stepInd, edist_dist]
  norm_num

/-! ### Step processes and the counting-process example -/

-- At the right endpoint the step process is the normalized full partial sum.
example {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    skorokhodStepProcess n X ω ⟨1, zero_le_one, le_rfl⟩ =
      (∑ i ∈ Finset.range n, X i ω) / Real.sqrt n := by
  simp [skorokhodStepProcess_apply]

-- At time `0` the compensated counting process vanishes.
example {Ω : Type*} (n : ℕ) (p : ℝ) (ξ : ℕ → Ω → ℝ) (ω : Ω) :
    compensatedBernoulliStep n p ξ ω ⟨0, le_rfl, zero_le_one⟩ = 0 := by
  simp [compensatedBernoulliStep_apply]

-- The step process differs from Donsker's polygonal process (here at `t = 1/2`, `n = 1`):
-- the step path has not jumped yet while the polygon has risen halfway.
example {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) :
    skorokhodStepProcess 1 X ω ⟨1 / 2, by norm_num, by norm_num⟩ = 0 ∧
      donskerProcess 1 X ω ⟨1 / 2, by norm_num, by norm_num⟩ = X 0 ω / 2 := by
  have h0 : Nat.floor ((1 : ℝ) / 2) = 0 := Nat.floor_eq_zero.2 (by norm_num)
  constructor
  · rw [skorokhodStepProcess_apply]
    norm_num [h0]
  · rw [donskerProcess_apply_eq 1 X ω _ one_ne_zero]
    norm_num [h0]
    ring

-- Jump control for fair-coin counting increments.
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ℕ → Ω → ℝ)
    (hBern : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1) :
    LindebergConditionTriangular (fun n k ω => (ξ k ω - 1 / 2) / Real.sqrt n) P :=
  lindebergConditionTriangular_compensatedBernoulli P ξ hBern (1 / 2) (by norm_num)
    (by norm_num)

-- Predictable quadratic variations at `t = 1` converge to `p (1 - p)`.
example (p : ℝ) :
    Tendsto (fun n : ℕ => p * (1 - p) * (Nat.floor ((n : ℝ) * 1) / n)) atTop
      (𝓝 (p * (1 - p))) := by
  simpa using tendsto_compensatedBernoulli_predictableQV p 1 zero_le_one

/-! ### Smoke tests of the main theorems -/

-- Converging together with empty bad sets: identical sequences.
example {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Y : ℕ → Ω → SkorokhodSpace 1) (Z : Ω' → SkorokhodSpace 1)
    (hY : TendstoInDistribution Y atTop Z (fun _ => P) P') :
    TendstoInDistribution Y atTop Z (fun _ => P) P' :=
  tendstoInDistribution_of_eventually_edist_le Y Y Z hY hY.forall_aemeasurable
    fun ε _ => ⟨fun _ => ∅, fun _ => MeasurableSet.empty, by simp, fun n ω _ => by simp⟩

-- The counting-process FCLT, with the martingale property of the same process.
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (ξ : ℕ → Ω → ℝ) (hMeas : ∀ n, Measurable (ξ n)) (hIndep : iIndepFun ξ P)
    (hIdent : ∀ i, IdentDistrib (ξ i) (ξ 0) P P) (hBern : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1)
    (hMean : P[ξ 0] = 1 / 2) (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    Martingale (fun k ω => ∑ i ∈ Finset.range (k + 1), (ξ i ω - 1 / 2))
        (Filtration.natural ξ fun n => (hMeas n).stronglyMeasurable) P ∧
      ∃ Y : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ),
        (∀ᵐ ω' ∂P', ∀ t : Set.Icc (0 : ℝ) 1, Y ω' t = B (iccToNNReal t) ω') ∧
        TendstoInDistribution (fun n => compensatedBernoulliStep n (1 / 2) ξ) atTop
          (fun ω' => SkorokhodSpace.ofContinuous
            (Real.sqrt (1 / 2 * (1 - 1 / 2)) • Y ω')) (fun _ => P) P' :=
  ⟨martingale_compensatedBernoulli ξ _ hIndep hIdent hBern _ hMean,
    tendstoInDistribution_compensatedBernoulliStep ξ hMeas hIndep hIdent hBern (1 / 2)
      (by norm_num) (by norm_num) hMean B hB⟩

end

end MathlibExtTest.Probability.Martingale.FunctionalCLT
