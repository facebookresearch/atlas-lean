/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.GenericChaining
public import MathlibExt.Probability.GenericChainingGaussian
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tests for generic chaining

Non-vacuity checks: the cardinality sequence, an admissible sequence, finiteness and positivity of
`γ₂` on the three-point space `{0, 1, 2} ⊂ ℝ`, and a non-degenerate Gaussian process on that space
that satisfies every hypothesis of the generic chaining, Dudley and Gaussian bounds.
-/

@[expose] public section

namespace MathlibExtTest.Probability.GenericChaining

open MeasureTheory ProbabilityTheory MathlibExt.Probability.GenericChaining
open scoped ENNReal NNReal

example : chainingCard 0 = 1 := rfl
example : chainingCard 1 = 4 := rfl
example : chainingCard 2 = 16 := rfl

/-- The constant sequence of trivial partitions is admissible. -/
def trivialAdmissible (T : Type*) : AdmissibleSequence T where
  cell _ _ := Set.univ
  mem_cell _ _ := Set.mem_univ _
  cell_eq_of_mem _ _ _ _ := rfl
  cell_succ_subset _ _ := le_rfl
  encard_range_le n := by
    rcases isEmpty_or_nonempty T with hT | hT
    · simp [Set.range_eq_empty]
    · rw [Set.range_const]; simpa using one_le_chainingCard n

/-- A three-point subset of the real line, as a finite metric space. -/
abbrev Pts : Type := ↥(({0, 1, 2} : Finset ℝ))

instance : Nonempty Pts := ⟨⟨0, by simp⟩⟩

/-- `γ₂` of a three-point space is finite. -/
example : gammaFunctional 2 (edist : Pts → Pts → ℝ≥0∞) < ⊤ :=
  gammaFunctional_lt_top 2 _ (fun _ _ => edist_ne_top _ _) (fun _ => edist_self _)

/-- `γ₂` of a three-point space is positive: it dominates the diameter. -/
example : 0 < gammaFunctional 2 (edist : Pts → Pts → ℝ≥0∞) := by
  refine lt_of_lt_of_le ?_ (diamWith_univ_le_gammaFunctional 2 _)
  have h0 : (0 : ℝ) ∈ ({0, 1, 2} : Finset ℝ) := by simp
  have h2 : (2 : ℝ) ∈ ({0, 1, 2} : Finset ℝ) := by simp
  refine lt_of_lt_of_le ?_
    (le_diamWith edist (Set.mem_univ (⟨0, h0⟩ : Pts)) (Set.mem_univ (⟨2, h2⟩ : Pts)))
  refine edist_pos.mpr fun h => ?_
  have := congrArg Subtype.val h
  norm_num at this

theorem hasSubgaussianMGF_id_gaussianReal :
    HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) :=
  ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => by simp [mgf_fun_id_gaussianReal]⟩

/-- Two-sided Gaussian tail: `P(|g| ≥ u) ≤ 2 exp(-u² / 2)` for a standard Gaussian `g`. -/
theorem gaussian_abs_tail {u : ℝ} (hu : 0 ≤ u) :
    (gaussianReal 0 1).real {ω : ℝ | u ≤ |ω|} ≤ 2 * Real.exp (-u ^ 2 / 2) := by
  have hmgf := hasSubgaussianMGF_id_gaussianReal
  have h1 := hmgf.measure_ge_le hu
  have h2 := hmgf.neg.measure_ge_le hu
  have hsub : {ω : ℝ | u ≤ |ω|} ⊆ {ω | u ≤ ω} ∪ {ω | u ≤ (-fun x : ℝ => x) ω} := by
    intro ω h
    rcases le_abs'.mp (show u ≤ |ω| from h) with h | h
    · right; show u ≤ -ω; linarith
    · left; exact h
  calc (gaussianReal 0 1).real {ω : ℝ | u ≤ |ω|}
      ≤ (gaussianReal 0 1).real ({ω | u ≤ ω} ∪ {ω | u ≤ (-fun x : ℝ => x) ω}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-u ^ 2 / 2) := by
        simp only [NNReal.coe_one, mul_one] at h1 h2
        linarith

/-- The Gaussian process `X_t = t g`, indexed by a finite set of reals with the distance
`|s - t|`, satisfies the increment condition (2.4). -/
theorem incrementCondition_linearGaussian (S : Finset ℝ) :
    SatisfiesIncrementCondition (gaussianReal 0 1) (fun (t : ↥S) (ω : ℝ) => (t : ℝ) * ω) := by
  intro s t u hu
  have hdist : dist s t = |(s : ℝ) - t| := by rw [Subtype.dist_eq, Real.dist_eq]
  have hfac : ∀ ω : ℝ, (s : ℝ) * ω - (t : ℝ) * ω = ((s : ℝ) - t) * ω := fun ω => by ring
  simp_rw [hfac, hdist]
  by_cases hst : (s : ℝ) - t = 0
  · have : {ω : ℝ | u ≤ |((s : ℝ) - t) * ω|} = ∅ := by
      ext ω; simp [hst, not_le.mpr hu]
    rw [this, measureReal_empty]; positivity
  · have ha : 0 < |(s : ℝ) - t| := abs_pos.mpr hst
    have hset : {ω : ℝ | u ≤ |((s : ℝ) - t) * ω|} = {ω | u / |(s : ℝ) - t| ≤ |ω|} := by
      ext ω
      simp only [Set.mem_ofPred_eq, abs_mul, div_le_iff₀ ha]
      rw [mul_comm]
    rw [hset]
    refine (gaussian_abs_tail (div_nonneg hu.le ha.le)).trans (le_of_eq ?_)
    congr 2
    rw [div_pow, sq_abs]
    field_simp

/-- The generic chaining bound applies to the non-degenerate process `X_t = t g`,
`t ∈ {0, 1, 2}`. -/
example : ENNReal.ofReal (∫ ω, ⨆ t : Pts, (t : ℝ) * ω ∂gaussianReal 0 1) ≤
    10 * gammaFunctional 2 (edist : Pts → Pts → ℝ≥0∞) := by
  refine integral_iSup_le_gammaTwo (gaussianReal 0 1) (fun (t : Pts) (ω : ℝ) => (t : ℝ) * ω)
    (fun t => measurable_id.const_mul _)
    (fun t => hasSubgaussianMGF_id_gaussianReal.integrable.const_mul _)
    (fun t => by rw [integral_const_mul]; simp) (incrementCondition_linearGaussian {0, 1, 2})

/-- Dudley's entropy bound applies to the same process, with a finite right-hand side. -/
example : ENNReal.ofReal (∫ ω, ⨆ t : Pts, (t : ℝ) * ω ∂gaussianReal 0 1) ≤
    17 * ∑' n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * entropyNumber (edist : Pts → Pts → ℝ≥0∞) n :=
  integral_iSup_le_dudley (gaussianReal 0 1) (fun (t : Pts) (ω : ℝ) => (t : ℝ) * ω)
    (fun t => measurable_id.const_mul _)
    (fun t => hasSubgaussianMGF_id_gaussianReal.integrable.const_mul _)
    (fun t => by rw [integral_const_mul]; simp) (incrementCondition_linearGaussian {0, 1, 2})

example : ∑' n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * entropyNumber (edist : Pts → Pts → ℝ≥0∞) n < ⊤ :=
  tsum_entropyNumber_lt_top

/-- The second moment of a standard Gaussian. -/
theorem integral_sq_gaussianReal : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable,
    integral_id_gaussianReal] at h
  simpa using h

/-- The Gaussian version applies to `X_t = t g` on `{0, 1, 2}`: its law is Gaussian and its
canonical distance is the metric `|s - t|`. -/
example : ENNReal.ofReal (∫ ω, ⨆ t : Pts, (t : ℝ) * ω ∂gaussianReal 0 1) ≤
    10 * gammaFunctional 2 (edist : Pts → Pts → ℝ≥0∞) := by
  set L : ℝ →L[ℝ] (Pts → ℝ) := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) fun t => (t : ℝ)
  have hL : (fun (ω : ℝ) (t : Pts) => (t : ℝ) * ω) = ⇑L := by
    funext ω t; simp [L, mul_comm]
  have hG : IsGaussian ((gaussianReal 0 1).map fun (ω : ℝ) (t : Pts) => (t : ℝ) * ω) := by
    rw [hL]; infer_instance
  refine integral_iSup_le_gammaTwo_of_isGaussian (gaussianReal 0 1)
    (fun (t : Pts) (ω : ℝ) => (t : ℝ) * ω) (fun t => measurable_id.const_mul _) hG
    (fun t => by rw [integral_const_mul]; simp) fun s t => ?_
  have hfac : ∀ ω : ℝ, ((s : ℝ) * ω - (t : ℝ) * ω) ^ 2 = ((s : ℝ) - t) ^ 2 * ω ^ 2 :=
    fun ω => by ring
  simp_rw [hfac]
  rw [integral_const_mul, integral_sq_gaussianReal, mul_one, Real.sqrt_sq_eq_abs,
    Subtype.dist_eq, Real.dist_eq]

/-! The increment condition is stated for probability measures: `P.real` reads an infinite
measure as `0`, so under `∞ • P` every process would satisfy it. For a measure that is not a
probability measure it does not elaborate. -/

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Prop := SatisfiesIncrementCondition (0 : Measure ℝ) fun (t : ℝ) (ω : ℝ) => t * ω

/-- The canonical distance is the `L²` norm of the increment, so it is infinite for an increment
that is not square integrable: here the constant increment `1` under Lebesgue measure on `ℝ`.
The real formula `(∫ (X_s - X_t)²)^{1/2}` would read the divergent integral as `0`. -/
example : canonicalDist (volume : Measure ℝ) (fun (t : Bool) (_ : ℝ) => if t then 1 else 0)
    true false = ∞ := by
  simp [canonicalDist, eLpNorm_const _ two_ne_zero (NeZero.ne volume)]

end MathlibExtTest.Probability.GenericChaining
