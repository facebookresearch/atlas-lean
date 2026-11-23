/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.CrossFitting
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Tests for cross-fitted AIPW

Fold bookkeeping on a concrete assignment; the cross-fitted estimator computed from its
definition (including a fitted score that reads the training data); the perfect-nuisance
boundary; a fixture with a wrong propensity and a wrong treated-arm regression, where the
remainder is nonzero and the product bound `abs_aipwRemainder_le` is attained; the two vanishing
cases of the remainder; `integral_crossFit_eq` on a one-point fixture; the variance identity
`integral_sq_sum_of_indep` on i.i.d. Rademacher signs; and non-vacuity of the AIPW oracle-gap and
asymptotic-normality theorems on i.i.d. Bernoulli(1/2) treatment over `Measure.infinitePi`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Causality
open MathlibExt.Probability.Causality.AugmentedIPW.CrossFitting

namespace MathlibExtTest.Probability.Causality.AugmentedIPW.CrossFitting

/-- Alternating two-fold assignment, independent of the sample size. -/
def parity : ℕ → ℕ → Fin 2 := fun _ i => ⟨i % 2, Nat.mod_lt _ (by norm_num)⟩

/-- Fold `0` at sample size `4` evaluates the even units and trains on the odd ones. -/
example : evalFold parity 4 0 = {0, 2} ∧ trainFold parity 4 0 = {1, 3} := by
  decide

/-- Boundary: at sample size `0` every fold is empty. -/
example (k : Fin 2) : evalFold parity 0 k = ∅ ∧ trainFold parity 0 k = ∅ := by
  simp [evalFold, trainFold]

/-- For any fold assignment, evaluation and training indices of a fold partition `range n`:
no unit is scored with nuisances fitted on itself. -/
example {K : ℕ} (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) :
    Disjoint (evalFold fold n k) (trainFold fold n k) ∧
      evalFold fold n k ∪ trainFold fold n k = Finset.range n :=
  ⟨Finset.disjoint_filter_filter_not _ _ _, Finset.filter_union_filter_not_eq _ _⟩

/-- A fitted score that ignores the training data: the estimator is the sample mean. With
`W i = i`, at `n = 2` it is `(0 + 1) / 2`. -/
example : crossFitEstimator (fun i (_ : Unit) => (i : ℝ)) parity (fun _ _ z => z.2) 2 () =
    1 / 2 := by
  simp [crossFitEstimator, Finset.sum_range_succ]

/-- A fitted score that reads only the training data (the sum of the training observations).
With `W i = i + 1` and `n = 2`, unit `0` (fold `0`) is scored on the training set `{1}` and unit
`1` (fold `1`) on `{0}`, so the estimator is `(W 1 + W 0) / 2 = 3 / 2`: each unit's own
observation is excluded from its nuisance. -/
example : crossFitEstimator (fun i (_ : Unit) => (i : ℝ) + 1) parity
    (fun n k z => ∑ j : trainFold parity n k, z.1 j) 2 () = 3 / 2 := by
  have h0 : trainFold parity 2 0 = {1} := by decide
  have h1 : trainFold parity 2 1 = {0} := by decide
  have hsum : ∀ k : Fin 2, ∑ j : trainFold parity 2 k, trainData (fun i (_ : Unit) => (i : ℝ) + 1)
      parity 2 k () j = ∑ j ∈ trainFold parity 2 k, ((j : ℝ) + 1) := fun k =>
    Finset.sum_coe_sort (trainFold parity 2 k) (fun j => (j : ℝ) + 1)
  simp only [crossFitEstimator, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hp0 : parity 2 0 = 0 := rfl
  have hp1 : parity 2 1 = 1 := rfl
  rw [hp0, hp1, hsum 0, hsum 1, h0, h1]
  norm_num

/-- Perfect-nuisance boundary: if every fitted score equals the oracle score `ψ`, the
cross-fitted estimator is the oracle estimator `n⁻¹ ∑ ψ(W i)`, so the oracle gap is `0`. -/
example {Ω 𝒲 : Type*} [MeasurableSpace 𝒲] {K : ℕ} (W : ℕ → Ω → 𝒲) (fold : ℕ → ℕ → Fin K)
    (ψ : 𝒲 → ℝ) (n : ℕ) (ω : Ω) :
    crossFitEstimator W fold (fun _ _ z => ψ z.2) n ω =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ψ (W i ω) :=
  rfl

/-- On a one-point space with the full σ-algebra, conditional expectations are the functions
themselves. -/
private lemma condExp_unit (f : Unit → ℝ) :
    (Measure.dirac ())[f | (inferInstance : MeasurableSpace Unit)] = f :=
  condExp_of_stronglyMeasurable le_rfl (measurable_of_countable f).stronglyMeasurable
    (Integrable.of_finite (μ := Measure.dirac ()))

/-- Fixture computed from the definition of `aipwRemainder`: everyone treated (`e* = 1`),
`Y₁ = 2`, `Y₀ = 0`, candidates `e = 1/2`, `g₁ = 0`, `g₀ = 0`. The control regression is correct
(`g₀ = 0 = E[Y₀ | m]`) but the propensity and the treated-arm regression are wrong, so neither
double-robustness condition holds, and the remainder is `(1 - 1/2) · (2 / (1/2)) = 2 ≠ 0`. -/
example : aipwRemainder (Measure.dirac ()) (inferInstance : MeasurableSpace Unit) Set.univ
    (fun _ => 0) (fun _ => 2) (fun _ => 1 / 2) (fun _ => 0) (fun _ => 0) = 2 := by
  simp only [aipwRemainder, condExp_unit, integral_dirac, Set.indicator_univ, Pi.one_apply]
  norm_num

/-- `abs_aipwRemainder_le` applied to the fixture above, with `ε = 1/2`. -/
example : |aipwRemainder (Measure.dirac ()) (inferInstance : MeasurableSpace Unit) Set.univ
    (fun _ => 0) (fun _ => 2) (fun _ => 1 / 2) (fun _ => 0) (fun _ => 0)| ≤
      (1 / 2 : ℝ)⁻¹ *
        √(∫ ω, ((Measure.dirac ())[Set.univ.indicator 1 | (inferInstance : MeasurableSpace Unit)] ω
          - (fun _ => (1 / 2 : ℝ)) ω) ^ 2 ∂Measure.dirac ()) *
        (√(∫ ω, ((Measure.dirac ())[(fun _ => (2 : ℝ)) | (inferInstance : MeasurableSpace Unit)] ω
            - (fun _ => (0 : ℝ)) ω) ^ 2 ∂Measure.dirac ()) +
          √(∫ ω, ((Measure.dirac ())[(fun _ => (0 : ℝ)) | (inferInstance : MeasurableSpace Unit)] ω
            - (fun _ => (0 : ℝ)) ω) ^ 2 ∂Measure.dirac ())) :=
  abs_aipwRemainder_le MeasurableSet.univ (memLp_const _) (memLp_const _)
    aestronglyMeasurable_const (memLp_const _) (memLp_const _) (by norm_num)
    (ae_of_all _ fun _ => by norm_num)

/-- The bound of `abs_aipwRemainder_le` is attained on the fixture: its literal right-hand
side, with the conditional expectations rewritten by `condExp_unit`, is
`2 · (1/2) · (2 + 0) = 2 = |aipwRemainder|`. -/
example : |aipwRemainder (Measure.dirac ()) (inferInstance : MeasurableSpace Unit) Set.univ
    (fun _ => 0) (fun _ => 2) (fun _ => 1 / 2) (fun _ => 0) (fun _ => 0)| =
      (1 / 2 : ℝ)⁻¹ *
        √(∫ ω, ((Measure.dirac ())[Set.univ.indicator 1 | (inferInstance : MeasurableSpace Unit)] ω
          - (fun _ => (1 / 2 : ℝ)) ω) ^ 2 ∂Measure.dirac ()) *
        (√(∫ ω, ((Measure.dirac ())[(fun _ => (2 : ℝ)) | (inferInstance : MeasurableSpace Unit)] ω
            - (fun _ => (0 : ℝ)) ω) ^ 2 ∂Measure.dirac ()) +
          √(∫ ω, ((Measure.dirac ())[(fun _ => (0 : ℝ)) | (inferInstance : MeasurableSpace Unit)] ω
            - (fun _ => (0 : ℝ)) ω) ^ 2 ∂Measure.dirac ())) := by
  simp only [aipwRemainder, condExp_unit, integral_dirac, Set.indicator_univ, Pi.one_apply]
  have h1 : √((1 - 1 / 2 : ℝ) ^ 2) = 1 / 2 := by rw [Real.sqrt_sq (by norm_num)]; norm_num
  have h2 : √((2 - 0 : ℝ) ^ 2) = 2 := by rw [Real.sqrt_sq (by norm_num)]; norm_num
  rw [h1, h2]
  norm_num

/-- `aipwRemainder_eq_zero_of_propensity`: the correct propensity `e = 1` kills the remainder
for arbitrary (wrong) regressions. -/
example : aipwRemainder (Measure.dirac ()) (inferInstance : MeasurableSpace Unit) Set.univ
    (fun _ => 0) (fun _ => 2) (fun _ => 1) (fun _ => 5) (fun _ => 7) = 0 :=
  aipwRemainder_eq_zero_of_propensity (by rw [condExp_unit]; exact ae_of_all _ fun _ => by simp)

/-- `aipwRemainder_eq_zero_of_outcome`: correct regressions `g₁ = 2`, `g₀ = 0` kill the remainder
for the wrong propensity `1/2`. -/
example : aipwRemainder (Measure.dirac ()) (inferInstance : MeasurableSpace Unit) Set.univ
    (fun _ => 0) (fun _ => 2) (fun _ => 1 / 2) (fun _ => 0) (fun _ => 2) = 0 :=
  aipwRemainder_eq_zero_of_outcome (by rw [condExp_unit]) (by rw [condExp_unit])

/-- `integral_crossFit_eq` on a one-point fixture: wrong propensity `1/2`, correct regressions;
the sample-split score is unbiased for the ATE `2`. -/
example : ∫ z, aipwScoreOfSigma Set.univ (fun _ : Unit => (2 : ℝ)) (fun _ : Unit => (1 / 2 : ℝ))
      (fun _ => 0) (fun _ => 2) z.2 ∂((Measure.dirac ()).prod (Measure.dirac ())) =
    ∫ ω, ((fun _ : Unit => (2 : ℝ)) ω - (fun _ : Unit => (0 : ℝ)) ω) ∂Measure.dirac () :=
  integral_crossFit_eq (m := (inferInstance : MeasurableSpace Unit)) (Ωₜ := Unit)
    (μₜ := Measure.dirac ()) (ê := fun _ _ => 1 / 2) (ĝ₀ := fun _ _ => 0) (ĝ₁ := fun _ _ => 2)
    le_rfl MeasurableSet.univ (ae_of_all _ fun _ => by simp [observed])
    (integrable_const _) (integrable_const _) (by simp [condExp_unit])
    (by simp [condExp_unit]; rfl) (fun _ => stronglyMeasurable_const)
    (fun _ => stronglyMeasurable_const) (fun _ => stronglyMeasurable_const)
    (fun _ => integrable_const _) (fun _ => integrable_const _)
    (fun _ => ⟨1 / 2, by norm_num, ae_of_all _ fun _ => by norm_num⟩) Integrable.of_finite
    (ae_of_all _ fun _ => Or.inr ⟨by rw [condExp_unit], by rw [condExp_unit]⟩)

/-- Fair coin on `Bool`. -/
noncomputable def bern : Measure Bool :=
  (2⁻¹ : ENNReal) • Measure.dirac true + (2⁻¹ : ENNReal) • Measure.dirac false

instance : IsProbabilityMeasure bern := ⟨by simp [bern, ENNReal.inv_two_add_inv_two]⟩

/-- I.i.d. fair coins. -/
noncomputable def bernSeq : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => bern)

instance : IsProbabilityMeasure bernSeq := by unfold bernSeq; infer_instance

/-- Each coordinate of `bernSeq` is a fair coin. -/
lemma bernSeq_map (i : ℕ) : bernSeq.map (fun ω => ω i) = bern := Measure.infinitePi_map_eval _ i

/-- The coordinates of `bernSeq` are mutually independent. -/
lemma bernSeq_iIndep : iIndepFun (fun i (ω : ℕ → Bool) => ω i) bernSeq :=
  iIndepFun_infinitePi (P := fun _ => bern) (X := fun _ => id) (fun _ => measurable_id)

/-- `integral_sq_sum_of_indep` on i.i.d. Rademacher signs with trivial training data: the
centered kernel `±1` gives `E[(D₀ + D₁)²] = 2 · E[D²] = 2`; the cross term vanishes. -/
example : ∫ ω, (∑ i ∈ Finset.range 2,
      (fun z : Unit × Bool => if z.2 then (1 : ℝ) else -1) ((), ω i)) ^ 2 ∂bernSeq = 2 := by
  have hW : ∀ i, Measurable (fun ω : ℕ → Bool => ω i) := fun i => measurable_pi_apply i
  have key := integral_sq_sum_of_indep (Finset.range 2) (U := fun _ : ℕ → Bool => ())
    (V := fun i ω => ω i) (ν := bern) (D := fun z : Unit × Bool => if z.2 then (1 : ℝ) else -1)
    measurable_const hW (fun i _ => bernSeq_map i)
    (fun i _ => indepFun_const_left () _)
    (fun i _ j _ hij => (bernSeq_iIndep.indepFun hij).comp (measurable_const.prodMk measurable_id)
      measurable_id)
    (measurable_of_countable _).stronglyMeasurable ?_ Integrable.of_finite
  · refine key.trans ?_
    have h1 : ∀ z : Unit × Bool, (if z.2 then (1 : ℝ) else -1) ^ 2 = 1 := fun z => by
      split_ifs <;> norm_num
    simp only [h1, integral_const, probReal_univ, smul_eq_mul, mul_one, Finset.card_range]
    norm_num
  · intro u
    rw [integral_fintype (Integrable.of_finite (μ := bern)
      (f := fun w : Bool => if (u, w).2 = true then (1 : ℝ) else -1))]
    simp [bern, measureReal_def]

/-- With trivial covariates the true propensity is `1/2`. -/
lemma bern_propensity :
    bern[({true} : Set Bool).indicator 1 | ⊥] = fun _ => (1 / 2 : ℝ) := by
  rw [condExp_bot]; funext _
  rw [integral_indicator (measurableSet_singleton _)]
  simp [bern]

/-- With trivial covariates the regression of the zero outcome is `0`. -/
lemma bern_regression : bern[(fun _ : Bool => (0 : ℝ)) | ⊥] = 0 := condExp_zero

/-- The oracle AIPW score of the Bernoulli fixture vanishes identically. -/
lemma bern_oracle_score : aipwScoreOfSigma {true} (fun _ => (0 : ℝ))
    bern[({true} : Set Bool).indicator 1 | ⊥] bern[(fun _ => (0 : ℝ)) | ⊥]
      bern[(fun _ => (0 : ℝ)) | ⊥] = 0 := by
  funext w
  simp [aipwScoreOfSigma_apply]

/-- Non-vacuity of `tendstoInMeasure_crossFit_aipw_sub_oracle`: nondegenerate i.i.d.
Bernoulli(1/2) treatment, trivial covariates (`m = ⊥`), zero outcomes, correct outcome
regressions and the clipped propensity `1/2`. -/
example : TendstoInMeasure bernSeq (fun (n : ℕ) ω => √(n : ℝ) *
      (crossFitEstimator (fun i ω => ω i) parity (fun _ _ z =>
        aipwScoreOfSigma {true} (fun _ => (0 : ℝ)) (fun _ => 1 / 2) (fun _ => 0) (fun _ => 0)
          z.2) n ω -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          aipwScoreOfSigma {true} (fun _ => (0 : ℝ)) bern[({true} : Set Bool).indicator 1 | ⊥]
            bern[(fun _ => (0 : ℝ)) | ⊥] bern[(fun _ => (0 : ℝ)) | ⊥] (ω i))) Filter.atTop 0 := by
  have hW : ∀ i, Measurable (fun ω : ℕ → Bool => ω i) := fun i => measurable_pi_apply i
  refine tendstoInMeasure_crossFit_aipw_sub_oracle (P := bernSeq) (ν := bern) (m := ⊥)
    (Y₀ := fun _ => 0) (Y₁ := fun _ => 0) (T := {true}) (Y := fun _ => 0) (K := 2)
    (ê := fun _ _ _ _ => 1 / 2) (ĝ₀ := fun _ _ _ _ => 0) (ĝ₁ := fun _ _ _ _ => 0) hW
    bernSeq_iIndep
    (fun i => ⟨(hW i).aemeasurable, (hW 0).aemeasurable,
      (bernSeq_map i).trans (bernSeq_map 0).symm⟩)
    (bernSeq_map 0) bot_le (measurableSet_singleton _) measurable_const
    (Filter.Eventually.of_forall fun w => by cases w <;> simp [observed])
    (memLp_const _) (memLp_const _) ?_ ?_ (ε₀ := 1 / 2) (by norm_num) ?_ parity
    (fun _ _ => measurable_const) (fun _ _ => measurable_const) (fun _ _ => measurable_const)
    (fun _ _ _ => stronglyMeasurable_const) (fun _ _ _ => stronglyMeasurable_const)
    (fun _ _ _ => stronglyMeasurable_const) (fun _ _ _ => memLp_const _)
    (fun _ _ _ => memLp_const _) (ε := 1 / 2) (by norm_num) (fun _ _ _ _ => by norm_num) ?_ ?_
  · exact Filter.Eventually.of_forall fun x => by simp
  · exact Filter.Eventually.of_forall fun x => by simp
  · rw [bern_propensity]; exact Filter.Eventually.of_forall fun _ => by norm_num
  · intro k
    simp only [aipwScoreOfSigma_apply, bern_regression, Pi.zero_apply, sub_self, zero_div,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)
  · intro k
    simp only [bern_regression, Pi.zero_apply, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero, Real.sqrt_zero, add_zero, mul_zero]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)

/-- Non-vacuity of `tendstoInDistribution_crossFit_aipw` on the same fixture: the oracle score is
`0`, so the limit `N(0, 0)` is the point mass at `0` (`gaussianReal_zero_var`). -/
example : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (crossFitEstimator (fun i ω => ω i) parity (fun _ _ z =>
        aipwScoreOfSigma {true} (fun _ => (0 : ℝ)) (fun _ => 1 / 2) (fun _ => 0) (fun _ => 0)
          z.2) n ω -
        ∫ w, ((fun _ : Bool => (0 : ℝ)) w - (fun _ : Bool => (0 : ℝ)) w) ∂bern))
      Filter.atTop (fun _ : Unit => (0 : ℝ)) (fun _ => bernSeq) (Measure.dirac ()) := by
  have hW : ∀ i, Measurable (fun ω : ℕ → Bool => ω i) := fun i => measurable_pi_apply i
  refine tendstoInDistribution_crossFit_aipw (P := bernSeq) (ν := bern) (m := ⊥)
    (Y₀ := fun _ => 0) (Y₁ := fun _ => 0) (T := {true}) (Y := fun _ => 0) (K := 2)
    (ê := fun _ _ _ _ => 1 / 2) (ĝ₀ := fun _ _ _ _ => 0) (ĝ₁ := fun _ _ _ _ => 0) hW
    bernSeq_iIndep
    (fun i => ⟨(hW i).aemeasurable, (hW 0).aemeasurable,
      (bernSeq_map i).trans (bernSeq_map 0).symm⟩)
    (bernSeq_map 0) bot_le (measurableSet_singleton _) measurable_const
    (Filter.Eventually.of_forall fun w => by cases w <;> simp [observed])
    (memLp_const _) (memLp_const _) ?_ ?_ (ε₀ := 1 / 2) (by norm_num) ?_ parity
    (fun _ _ => measurable_const) (fun _ _ => measurable_const) (fun _ _ => measurable_const)
    (fun _ _ _ => stronglyMeasurable_const) (fun _ _ _ => stronglyMeasurable_const)
    (fun _ _ _ => stronglyMeasurable_const) (fun _ _ _ => memLp_const _)
    (fun _ _ _ => memLp_const _) (ε := 1 / 2) (by norm_num) (fun _ _ _ _ => by norm_num) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => by simp
  · exact Filter.Eventually.of_forall fun x => by simp
  · rw [bern_propensity]; exact Filter.Eventually.of_forall fun _ => by norm_num
  · intro k
    simp only [aipwScoreOfSigma_apply, bern_regression, Pi.zero_apply, sub_self, zero_div,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)
  · intro k
    simp only [bern_regression, Pi.zero_apply, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero, Real.sqrt_zero, add_zero, mul_zero]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)
  · rw [bern_oracle_score, variance_zero, Real.toNNReal_zero, gaussianReal_zero_var]
    exact ⟨aemeasurable_const, by simp⟩

end MathlibExtTest.Probability.Causality.AugmentedIPW.CrossFitting
