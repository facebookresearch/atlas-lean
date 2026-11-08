/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BerryEsseenModel
public import MathlibExt.Probability.BerryEsseen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Least common i.i.d. Berry--Esseen coefficient

The coefficient is chosen before the real probability law and positive sample
size. The implemented coefficient-42 theorem proves nonemptiness. Positivity
of the third moment proves boundedness below and closure at the real infimum.
The Bernoulli subclass consists of actual standardized two-point laws.

Source: catalogue constants/19a.md, revision 2c1968cd520b60f1cf3cf50749f7285e800e4e15.
The symbolic Esseen benchmark is a definition, not its asserted optimality.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory BerryEsseenModel
open scoped ENNReal NNReal

namespace BerryEsseenConstant

/-- A common coefficient for every standardized law and every positive sample size. -/
def IsAdmissible (C : ℝ) : Prop :=
  ∀ μ : Measure ℝ, IsStandardizedLaw μ → ∀ n : ℕ+,
    kolmogorovError μ n ≤ C * thirdMoment μ / Real.sqrt (n.1 : ℝ)

/-- The least common coefficient, with nonempty and bounded family proved below. -/
noncomputable def value : ℝ := sInf {C : ℝ | IsAdmissible C}

/-- The exact symbolic Esseen lower benchmark. -/
noncomputable def esseenConstant : ℝ :=
  (Real.sqrt 10 + 3) / (6 * Real.sqrt (2 * Real.pi))

/-- The Esseen benchmark is positive; no decimal is identified with it. -/
theorem esseenConstant_positive : 0 < esseenConstant := by
  unfold esseenConstant
  positivity

/-- Any common coefficient is automatically nonnegative. -/
theorem isAdmissible_nonnegative {C : ℝ} (hC : IsAdmissible C) : 0 ≤ C := by
  have h := hC (gaussianReal 0 1) standardGaussian_isStandardized ⟨1, by decide⟩
  rw [standardGaussian_error_one] at h
  simp only [Nat.cast_one, Real.sqrt_one, div_one] at h
  by_contra hn
  have hneg : C < 0 := lt_of_not_ge hn
  have hprod : C * thirdMoment (gaussianReal 0 1) < 0 :=
    mul_neg_of_neg_of_pos hneg (thirdMoment_positive standardGaussian_isStandardized)
  linarith

/-- The existing implemented Berry--Esseen API supplies the coefficient 42. -/
theorem isAdmissible_fortyTwo : IsAdmissible 42 := by
  intro μ hμ n
  let : IsProbabilityMeasure μ := hμ.probability
  let : IsProbabilityMeasure (iidLaw μ) := iidLaw_probability hμ
  let : IsProbabilityMeasure (normalizedLaw μ n) := normalizedLaw_probability hμ n
  have hd := iidLaw_identDistrib hμ 0
  have hmem : MemLp (fun ω : ℕ → ℝ ↦ ω 0) 3 (iidLaw μ) :=
    hd.memLp_iff.mpr hμ.third_moment
  have hmean : (∫ ω : ℕ → ℝ, ω 0 ∂iidLaw μ) = 0 := hd.integral_eq.trans hμ.mean_zero
  have hvar : variance (fun ω : ℕ → ℝ ↦ ω 0) (iidLaw μ) = 1 :=
    hd.variance_eq.trans hμ.variance_one
  have hthird : (∫ ω : ℕ → ℝ, |ω 0| ^ 3 ∂iidLaw μ) = thirdMoment μ :=
    (hd.comp (continuous_abs.measurable.pow_const 3)).integral_eq
  apply (error_le_iff μ n _).mpr
  intro x
  have h := MathlibExt.Probability.BerryEsseenWanted.berry_esseen_explicit
    (fun i (ω : ℕ → ℝ) ↦ ω i) (fun i ↦ measurable_pi_apply i) (iidLaw_independent hμ)
    (fun i ↦ (iidLaw_identDistrib hμ i).trans hd.symm) hmem hmean
    (by rw [hvar]; norm_num) n.1 n.2 x
  simp only [hvar, mul_one, Real.sqrt_one, one_pow, one_mul, hthird] at h
  simp only [normalCDF, cdf_eq_real]
  exact h

/-- The optimized family is genuinely nonempty. -/
theorem admissible_nonempty : ({C : ℝ | IsAdmissible C} : Set ℝ).Nonempty :=
  ⟨42, isAdmissible_fortyTwo⟩

/-- The optimized family is bounded below by zero. -/
theorem admissible_bddBelow : BddBelow {C : ℝ | IsAdmissible C} :=
  ⟨0, fun _ h ↦ isAdmissible_nonnegative h⟩

/-- The optimal coefficient is nonnegative. -/
theorem value_nonnegative : 0 ≤ value :=
  le_csInf admissible_nonempty (fun _ h ↦ isAdmissible_nonnegative h)

/-- The optimal coefficient is no larger than any admissible coefficient. -/
theorem value_le_of_isAdmissible {C : ℝ} (hC : IsAdmissible C) : value ≤ C :=
  csInf_le admissible_bddBelow hC

/-- A concrete finite bound for the optimizer. -/
theorem value_le_fortyTwo : value ≤ 42 := value_le_of_isAdmissible isAdmissible_fortyTwo

/-- Larger coefficients remain admissible. -/
theorem isAdmissible_mono {C D : ℝ} (hC : IsAdmissible C) (hCD : C ≤ D) :
    IsAdmissible D := by
  intro μ hμ n
  exact (hC μ hμ n).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCD (thirdMoment_nonnegative μ)) (Real.sqrt_nonneg _))

/-- The real infimum satisfies the actual source inequality. -/
theorem value_bound (μ : Measure ℝ) (hμ : IsStandardizedLaw μ) (n : ℕ+) :
    kolmogorovError μ n ≤ value * thirdMoment μ / Real.sqrt (n.1 : ℝ) := by
  have hn : (0 : ℝ) < n.1 := by exact_mod_cast n.2
  have hk : 0 < thirdMoment μ / Real.sqrt (n.1 : ℝ) :=
    div_pos (thirdMoment_positive hμ) (Real.sqrt_pos.mpr hn)
  have hlower : kolmogorovError μ n / (thirdMoment μ / Real.sqrt (n.1 : ℝ)) ≤ value := by
    apply le_csInf admissible_nonempty
    intro C hC
    apply (div_le_iff₀ hk).mpr
    simpa only [mul_div_assoc] using hC μ hμ n
  simpa only [mul_div_assoc] using (div_le_iff₀ hk).mp hlower

/-- The optimizer is admissible, not just an unattained real projection. -/
theorem value_isAdmissible : IsAdmissible value := value_bound

/-- The source word "smallest" is an implemented leastness theorem. -/
theorem value_isLeast : IsLeast {C : ℝ | IsAdmissible C} value :=
  ⟨value_isAdmissible, fun _ h ↦ value_le_of_isAdmissible h⟩

/-- Admissibility is precisely lying above the optimal coefficient. -/
theorem isAdmissible_iff_value_le (C : ℝ) : IsAdmissible C ↔ value ≤ C :=
  ⟨value_le_of_isAdmissible, isAdmissible_mono value_isAdmissible⟩

/-- The same coefficient controls i.i.d. variables on every carrier universe. -/
theorem iid_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    {C : ℝ} (hC : IsAdmissible C) (h : IsIIDModel P X) (n : ℕ+) (x : ℝ) :
    |cdf (P.map (fun ω ↦ (∑ i ∈ Finset.range n.1, X i ω) /
        Real.sqrt (n.1 : ℝ))) x - normalCDF x| ≤
      C * (∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt (n.1 : ℝ) := by
  have hp := (pointwise_le_kolmogorovError (P.map (X 0)) n x).trans
    (hC _ h.standardizedLaw n)
  rw [← h.normalizedLaw_eq n, h.thirdMoment_eq] at hp
  exact hp

/-- A centered, variance-one two-point law is the normalized Bernoulli subclass. -/
def IsBernoulliLaw (μ : Measure ℝ) : Prop :=
  IsStandardizedLaw μ ∧ ∃ a b : ℝ, a ≠ b ∧ μ ({a, b}ᶜ) = 0

/-- A real nondegenerate Bernoulli witness with equal masses at -1 and 1. -/
noncomputable def symmetricBernoulliLaw : Measure ℝ :=
  ((1 / 2 : ℝ≥0) : ENNReal) • Measure.dirac (-1) +
    ((1 / 2 : ℝ≥0) : ENNReal) • Measure.dirac 1

/-- The two actual atom masses add to one. -/
instance symmetricBernoulli_probability : IsProbabilityMeasure symmetricBernoulliLaw where
  measure_univ := by
    simp only [symmetricBernoulliLaw, Measure.add_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    norm_cast
    norm_num

/-- Every moment of the two-point identity is finite. -/
theorem symmetricBernoulli_memLp (p : ENNReal) : MemLp id p symmetricBernoulliLaw := by
  have hbound : ∀ᵐ x ∂symmetricBernoulliLaw, ‖x‖ ≤ 1 := by
    rw [symmetricBernoulliLaw, ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure (by simp) _, Measure.ae_smul_measure (by simp) _⟩
  exact MemLp.of_bound measurable_id.aestronglyMeasurable 1 hbound

/-- Integration against the finite actual law. -/
theorem symmetricBernoulli_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂symmetricBernoulliLaw) = (1 / 2) * f (-1) + (1 / 2) * f 1 := by
  have h₁ : Integrable f (Measure.dirac (-1)) := integrable_dirac (by simp)
  have h₂ : Integrable f (Measure.dirac 1) := integrable_dirac (by simp)
  rw [symmetricBernoulliLaw, integral_add_measure
    (h₁.smul_measure (c := ((1 / 2 : ℝ≥0) : ENNReal)) ENNReal.coe_ne_top)
    (h₂.smul_measure (c := ((1 / 2 : ℝ≥0) : ENNReal)) ENNReal.coe_ne_top)]
  simp [integral_smul_measure, integral_dirac]

/-- The Bernoulli benchmark has the source's actual mean and variance. -/
theorem symmetricBernoulli_isStandardized : IsStandardizedLaw symmetricBernoulliLaw := by
  refine ⟨inferInstance, ?_, ?_, symmetricBernoulli_memLp 3⟩
  · rw [symmetricBernoulli_integral]
    norm_num
  · rw [variance_eq_sub (symmetricBernoulli_memLp 2)]
    change (∫ x, x ^ 2 ∂symmetricBernoulliLaw) -
      (∫ x, x ∂symmetricBernoulliLaw) ^ 2 = 1
    rw [symmetricBernoulli_integral, symmetricBernoulli_integral]
    norm_num

/-- The Bernoulli witness is supported on the two distinct actual points. -/
theorem symmetricBernoulli_isBernoulli : IsBernoulliLaw symmetricBernoulliLaw := by
  refine ⟨symmetricBernoulli_isStandardized, -1, 1, by norm_num, ?_⟩
  norm_num [symmetricBernoulliLaw, Measure.add_apply, Measure.smul_apply]

/-- Its third absolute moment is exactly one. -/
theorem symmetricBernoulli_thirdMoment : thirdMoment symmetricBernoulliLaw = 1 := by
  rw [thirdMoment, symmetricBernoulli_integral]
  norm_num

/-- Common coefficients restricted to the actual Bernoulli subclass. -/
def IsBernoulliAdmissible (C : ℝ) : Prop :=
  ∀ μ : Measure ℝ, IsBernoulliLaw μ → ∀ n : ℕ+,
    kolmogorovError μ n ≤ C * thirdMoment μ / Real.sqrt (n.1 : ℝ)

/-- The optimal Bernoulli-subclass coefficient. -/
noncomputable def bernoulliValue : ℝ := sInf {C : ℝ | IsBernoulliAdmissible C}

/-- The subclass is nonvacuous, so its common coefficients are nonnegative. -/
theorem isBernoulliAdmissible_nonnegative {C : ℝ} (hC : IsBernoulliAdmissible C) :
    0 ≤ C := by
  have h := hC symmetricBernoulliLaw symmetricBernoulli_isBernoulli ⟨1, by decide⟩
  simp only [symmetricBernoulli_thirdMoment, mul_one, Nat.cast_one,
    Real.sqrt_one, div_one] at h
  exact (kolmogorovError_nonnegative _ _).trans h

/-- The coefficient 42 applies to the actual subclass too. -/
theorem bernoulliAdmissible_nonempty : ({C : ℝ | IsBernoulliAdmissible C} : Set ℝ).Nonempty :=
  ⟨42, fun μ hμ ↦ isAdmissible_fortyTwo μ hμ.1⟩

/-- A lower bound on the real family defining the subclass optimum. -/
theorem bernoulliAdmissible_bddBelow : BddBelow {C : ℝ | IsBernoulliAdmissible C} :=
  ⟨0, fun _ h ↦ isBernoulliAdmissible_nonnegative h⟩

/-- The subclass infimum is nonnegative. -/
theorem bernoulliValue_nonnegative : 0 ≤ bernoulliValue :=
  le_csInf bernoulliAdmissible_nonempty (fun _ h ↦ isBernoulliAdmissible_nonnegative h)

/-- Restricting to Bernoulli laws cannot increase the optimized coefficient. -/
theorem bernoulliValue_le_value : bernoulliValue ≤ value :=
  csInf_le bernoulliAdmissible_bddBelow (fun μ hμ ↦ value_isAdmissible μ hμ.1)

end BerryEsseenConstant
