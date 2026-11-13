/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Renewal.CramerIdentity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Tests for the ladder Cramér identity

* Non-vacuity: the coordinate walk on `ℤ^ℕ` with steps `+1` (probability `1/3`) and `-1`
  (probability `2/3`) has `𝔼 e^{θ X} = e^θ / 3 + 2 e^{-θ} / 3`, which equals `1` at
  `θ = log 2`; `hasSum_ladderLaw_mul_exp` applies.
* Computed consequence: the `±1` walk is skip-free upwards, so the identity pins the ladder law
  `g 1 = 1/2` and `P(M > 0) = 1/2` (the gambler's-ruin value `p / q`).
* Boundary (`θ = 0`): `𝔼 e^{0 · X} = 1` for every law, but for the walk above the identity
  fails at `θ = 0` (it would make the ladder law proper), so `0 < θ` cannot be dropped.
* Boundary (degenerate scores): for `X = 0` almost surely, `𝔼 e^{θ X} = 1` for every `θ`, yet
  the ladder law vanishes and `∑ g j e^{θ j} = 0`, so nondegeneracy cannot be dropped.
-/

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Renewal

namespace MathlibExtTest.Probability.Renewal.CramerIdentity

/-! ### Coordinate walks under a product law -/

lemma coord_hyps (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (∀ i, Measurable fun ω : ℕ → ℤ => ω i) ∧
      iIndepFun (fun i (ω : ℕ → ℤ) => ω i) (Measure.infinitePi fun _ : ℕ => ν) ∧
      ∀ i, IdentDistrib (fun ω : ℕ → ℤ => ω i) (fun ω => ω 0)
        (Measure.infinitePi fun _ : ℕ => ν) (Measure.infinitePi fun _ : ℕ => ν) := by
  refine ⟨fun i => measurable_pi_apply i,
    iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id, fun i => ?_⟩
  refine ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
  rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]

lemma mgf_coord (ν : Measure ℤ) [IsProbabilityMeasure ν] (θ : ℝ) :
    mgf (fun ω : ℕ → ℤ => (ω 0 : ℝ)) (Measure.infinitePi fun _ : ℕ => ν) θ =
      ∫ x : ℤ, Real.exp (θ * x) ∂ν := by
  have h := integral_map (μ := Measure.infinitePi fun _ : ℕ => ν)
    (measurable_pi_apply 0).aemeasurable
    (measurable_from_top (f := fun x : ℤ => Real.exp (θ * x))).aestronglyMeasurable
  rw [Measure.infinitePi_map_eval] at h
  exact h.symm

/-! ### Non-vacuity: the `±1` walk with `P(+1) = 1/3` -/

/-- Step law: `+1` with probability `1/3`, `-1` with probability `2/3`. -/
noncomputable def stepLaw : Measure ℤ :=
  (1 / 3 : ENNReal) • Measure.dirac 1 + (2 / 3 : ENNReal) • Measure.dirac (-1)

instance : IsProbabilityMeasure stepLaw := by
  constructor
  simp only [stepLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same, show (1 : ENNReal) + 2 = 3 by norm_num,
    ENNReal.div_self (by norm_num) (by norm_num)]

/-- The product law of the `±1` walk. -/
noncomputable abbrev walkP : Measure (ℕ → ℤ) := Measure.infinitePi fun _ : ℕ => stepLaw

lemma mgf_stepLaw (θ : ℝ) :
    mgf (fun ω : ℕ → ℤ => (ω 0 : ℝ)) walkP θ =
      1 / 3 * Real.exp θ + 2 / 3 * Real.exp (-θ) := by
  rw [mgf_coord, stepLaw, integral_add_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  · simp [ENNReal.toReal_div]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp [ENNReal.div_eq_top])

lemma mgf_stepLaw_log_two : mgf (fun ω : ℕ → ℤ => (ω 0 : ℝ)) walkP (Real.log 2) = 1 := by
  rw [mgf_stepLaw, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

lemma stepLaw_nondegenerate : ¬ ∀ᵐ ω ∂walkP, ω 0 = 0 := by
  intro h
  rw [ae_iff] at h
  have hpre : {ω : ℕ → ℤ | ¬ ω 0 = 0} = (fun ω : ℕ → ℤ => ω 0) ⁻¹' {x | x ≠ 0} := rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) (MeasurableSet.of_discrete),
    Measure.infinitePi_map_eval] at h
  simp [stepLaw] at h

/-- Non-vacuity of `hasSum_ladderLaw_mul_exp`: for the `±1` walk, `θ = log 2` solves
`𝔼 e^{θ X} = 1` and the ladder Cramér identity holds there. -/
theorem stepLaw_cramer :
    HasSum (fun k : ℕ => ladderLaw walkP (fun i ω => ω i) k * Real.exp (Real.log 2 * k)) 1 :=
  hasSum_ladderLaw_mul_exp (coord_hyps stepLaw).1 (coord_hyps stepLaw).2.1
    (coord_hyps stepLaw).2.2 (Real.log_pos (by norm_num)) mgf_stepLaw_log_two
    stepLaw_nondegenerate

/-- Consequence: the `±1` walk with negative drift reaches a positive level with probability
strictly less than `1`. -/
example : maxTail walkP (fun i ω => ω i) 0 < 1 := by
  obtain ⟨h1, h2, h3⟩ := coord_hyps stepLaw
  rw [← tsum_ladderLaw h1 h2 h3]
  exact tsum_lt_one_of_hasSum_exp_mul (Real.log_pos (by norm_num)) (ladderLaw_zero _ _)
    (ladderLaw_nonneg _ _) stepLaw_cramer

/-- The `±1` walk is skip-free upwards: almost surely its first ladder height is `1`. -/
lemma stepLaw_ladderLaw_eq_zero {j : ℕ} (hj : 2 ≤ j) : ladderLaw walkP (fun i ω => ω i) j = 0 := by
  have hstep : ∀ i, walkP ((fun ω : ℕ → ℤ => ω i) ⁻¹' {x | x ≠ 1 ∧ x ≠ -1}) = 0 := fun i => by
    rw [← Measure.map_apply (measurable_pi_apply i) (MeasurableSet.of_discrete),
      Measure.infinitePi_map_eval]
    simp [stepLaw]
  have hnull : ∀ n, walkP (ladderEvent (fun i ω => ω i) n j) = 0 := by
    intro n
    refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hstep)
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq]
    by_contra hall
    push Not at hall
    obtain ⟨hpos, hval, hmin⟩ := hω
    cases n with
    | zero => simp [scoreWalk] at hpos
    | succ n =>
      have hsucc : scoreWalk (fun i ω => ω i) (n + 1) ω =
          scoreWalk (fun i ω => ω i) n ω + ω n := Finset.sum_range_succ _ n
      have hle := hmin n (Nat.lt_succ_self n)
      have hω1 : ω n ≤ 1 := by
        by_cases h1 : ω n = 1
        · omega
        · have := hall n h1
          omega
      omega
  rw [ladderLaw, measure_iUnion_null hnull, ENNReal.toReal_zero]

/-- The Cramér identity pins the ladder law of the `±1` walk: `g 1 = 1/2`, so the walk ever
becomes positive with probability `1/2` (the gambler's-ruin value `p / q`). -/
example : ladderLaw walkP (fun i ω => ω i) 1 = 1 / 2 ∧
    maxTail walkP (fun i ω => ω i) 0 = 1 / 2 := by
  obtain ⟨h1, h2, h3⟩ := coord_hyps stepLaw
  have hzero : ∀ k ≠ 1, ladderLaw walkP (fun i ω => ω i) k = 0 := fun k hk => by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 0 := by omega
      exact ladderLaw_zero _ _
    · exact stepLaw_ladderLaw_eq_zero hk2
  have hsingle := hasSum_single (f := fun k : ℕ =>
      ladderLaw walkP (fun i ω => ω i) k * Real.exp (Real.log 2 * k)) 1
    fun k hk => by simp [hzero k hk]
  have hg1 : ladderLaw walkP (fun i ω => ω i) 1 = 1 / 2 := by
    have h := hsingle.unique stepLaw_cramer
    rw [Nat.cast_one, mul_one, Real.exp_log (by norm_num)] at h
    linarith
  refine ⟨hg1, ?_⟩
  rw [← tsum_ladderLaw h1 h2 h3, tsum_eq_single 1 hzero, hg1]

/-! ### Boundary cases -/

/-- Boundary (`θ = 0`): every law has `𝔼 e^{0 · X} = 1`, but the identity fails at `θ = 0`
for the `±1` walk, so the hypothesis `0 < θ` cannot be dropped. -/
example : mgf (fun ω : ℕ → ℤ => (ω 0 : ℝ)) walkP 0 = 1 ∧
    ¬ HasSum (fun k : ℕ => ladderLaw walkP (fun i ω => ω i) k * Real.exp (0 * k)) 1 := by
  refine ⟨mgf_zero, fun h => ?_⟩
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  exact not_hasSum_exp_mul_of_hasSum_one (Real.log_pos (by norm_num)) (ladderLaw_zero _ _)
    (ladderLaw_nonneg _ _) h stepLaw_cramer

/-- Boundary (degenerate scores): under `X = 0` almost surely (product of `δ₀`),
`𝔼 e^{θ X} = 1` for every `θ`, yet `∑ g j e^{θ j} = 0 ≠ 1`, so the nondegeneracy hypothesis
cannot be dropped. -/
example (θ : ℝ) :
    mgf (fun ω : ℕ → ℤ => (ω 0 : ℝ)) (Measure.infinitePi fun _ : ℕ => Measure.dirac 0) θ = 1 ∧
      ¬ HasSum (fun k : ℕ => ladderLaw (Measure.infinitePi fun _ : ℕ => Measure.dirac (0 : ℤ))
        (fun i ω => ω i) k * Real.exp (θ * k)) 1 := by
  refine ⟨by rw [mgf_coord, integral_dirac]; simp, fun h => ?_⟩
  have hzero : ∀ k, ladderLaw (Measure.infinitePi fun _ : ℕ => Measure.dirac (0 : ℤ))
      (fun i ω => ω i) k = 0 := by
    intro k
    have hnull : ∀ n, (Measure.infinitePi fun _ : ℕ => Measure.dirac (0 : ℤ))
        (ladderEvent (fun i ω => ω i) n k) = 0 := by
      intro n
      refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null fun i =>
        (show (Measure.infinitePi fun _ : ℕ => Measure.dirac (0 : ℤ))
          ((fun ω : ℕ → ℤ => ω i) ⁻¹' {x | x ≠ 0}) = 0 by
            rw [← Measure.map_apply (measurable_pi_apply i) (MeasurableSet.of_discrete),
              Measure.infinitePi_map_eval]
            simp))
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq]
      by_contra hall
      push Not at hall
      obtain ⟨hpos, -, -⟩ := hω
      simp [scoreWalk, hall] at hpos
    rw [ladderLaw, measure_iUnion_null hnull, ENNReal.toReal_zero]
  simp only [hzero, zero_mul] at h
  exact zero_ne_one (h.unique hasSum_zero).symm

end MathlibExtTest.Probability.Renewal.CramerIdentity
