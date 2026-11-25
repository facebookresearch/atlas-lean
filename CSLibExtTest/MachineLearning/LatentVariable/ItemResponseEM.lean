/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ItemResponseEM
import MathlibExt.Probability.FiniteProbability

/-!
# Tests for the item-response EM correspondence

Repeated observations versus full-outcome normalization, and positive
evidence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open Cslib.MachineLearning.LatentVariable.BernoulliMixture
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open MathlibExt.Probability.Statistics.Measurement

namespace Cslib.MachineLearning.LatentVariable.ItemResponseEM

/-- Valid parameters on one item and two latent states, for the pin tests. -/
private noncomputable def testParams : ValidParams 1 2 :=
  ⟨⟨fun _ => (1 / 2 : ℝ), fun _ _ => (1 / 2 : ℝ)⟩,
    ⟨fun _ => by show (0 : ℝ) < 1 / 2; norm_num,
      by
        show (∑ _ : Fin 2, (1 / 2 : ℝ)) = 1
        simp only [Fin.sum_univ_two]
        norm_num,
      fun _ _ => by show (0 : ℝ) < 1 / 2; norm_num,
      fun _ _ => by show (1 / 2 : ℝ) < 1; norm_num⟩⟩

private theorem localIndepPMF_ne_top {d : ℕ} (q : Fin d → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) (x : Fin d → Bool) :
    localIndepPMF q hq0 hq1 x ≠ ⊤ := by
  rw [localIndepPMF_apply]
  have hle : (∏ i, (if x i then ENNReal.ofReal (q i) else ENNReal.ofReal (1 - q i))) ≤ 1 := by
    apply Finset.prod_le_one
    intro i _
    split
    · calc ENNReal.ofReal (q i) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hq1 i)
        _ = 1 := ENNReal.ofReal_one
    · have h2 : 1 - q i ≤ 1 := by linarith [hq0 i]
      calc ENNReal.ofReal (1 - q i) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h2
        _ = 1 := ENNReal.ofReal_one
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
private theorem localIndepPMF_ne_zero {d : ℕ} (q : Fin d → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1) (x : Fin d → Bool) :
    localIndepPMF q (fun j => (hq0 j).le) (fun j => (hq1 j).le) x ≠ 0 := by
  rw [localIndepPMF_apply, Finset.prod_ne_zero_iff]
  intro i _
  split
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (hq0 i))
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hq1 i)))

/-- The EM marginal evidence is positive. -/
private theorem marginal_joint_pos {d K : ℕ} [Nonempty (Fin K)] (θ : ValidParams d K)
    (x : Fin d → Bool) :
    0 < Cslib.MachineLearning.LatentVariable.ExpectationMaximization.marginal joint θ x := by
  show 0 < ∑ k', joint θ x k'
  apply Finset.sum_pos
  · intro k _
    exact joint_pos θ x k
  · exact Finset.univ_nonempty


-- Repeated observations versus full outcome-space normalization.
/-- A repeated data pattern counts with its multiplicity in a data sum,
while the joint still normalizes over the full outcome space. The
statement is existential over valid parameters on one item and two latent
states, so it is not vacuous for want of a valid parameter; for every
pattern `x` and latent state `k`, the two-point constant data list at `x`
contributes `2 * joint θ x k`, and separately the sum of `joint θ` over
all patterns and latent states is `1`. -/
private theorem pin_test_repeated_observations_vs_full_outcome_normalization :
    ∃ θ : ValidParams 1 2,
      (∀ (x : Fin 1 → Bool) (k : Fin 2),
        (∑ n : Fin 2, joint θ ((fun _ : Fin 2 => x) n) k) = 2 * joint θ x k)
      ∧ (∑ y : Fin 1 → Bool, ∑ k' : Fin 2, joint θ y k' = 1) := by
  refine ⟨testParams, ?_, ?_⟩
  · intro x k
    simp only [Fin.sum_univ_two]
    ring
  · exact joint_sum_one testParams

-- positive evidence and finite real reading; zero evidence excluded.
/-- Under valid interior parameters on one item and two latent states,
every pattern and latent state has positive product-Bernoulli mass,
positive joint mass, and positive marginal evidence; the locally
independent mass is finite and nonzero and its real reading is the
product-Bernoulli mass; and the responsibilities at a pattern sum to
one. Existential quantification over valid parameters keeps the test
nonvacuous. No zero-evidence case is asserted: the positivity clauses
say that, under these hypotheses, zero evidence does not occur. -/
private theorem pin_test_positive_evidence_and_toReal :
    ∃ θ : ValidParams 1 2,
      ∀ (x : Fin 1 → Bool) (k : Fin 2),
        0 < bernPMF (θ.1.prob k) x
        ∧ 0 < joint θ x k
        ∧ 0 < Cslib.MachineLearning.LatentVariable.ExpectationMaximization.marginal
            joint θ x
        ∧ localIndepPMF (θ.1.prob k) (fun j => (θ.2.prob_pos k j).le)
            (fun j => (θ.2.prob_lt_one k j).le) x ≠ ⊤
        ∧ localIndepPMF (θ.1.prob k) (fun j => (θ.2.prob_pos k j).le)
            (fun j => (θ.2.prob_lt_one k j).le) x ≠ 0
        ∧ (localIndepPMF (θ.1.prob k) (fun j => (θ.2.prob_pos k j).le)
            (fun j => (θ.2.prob_lt_one k j).le) x).toReal
          = bernPMF (θ.1.prob k) x
        ∧ ∑ k' : Fin 2, resp θ x k' = 1 := by
  haveI : Nonempty (Fin 2) := ⟨⟨0, by decide⟩⟩
  refine ⟨testParams, fun x k => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bernPMF_pos (testParams.2.prob_pos k) (testParams.2.prob_lt_one k) x
  · exact joint_pos testParams x k
  · exact marginal_joint_pos testParams x
  · exact localIndepPMF_ne_top _ (fun j => (testParams.2.prob_pos k j).le)
      (fun j => (testParams.2.prob_lt_one k j).le) x
  · exact localIndepPMF_ne_zero _ (testParams.2.prob_pos k)
      (testParams.2.prob_lt_one k) x
  · exact localIndepPMF_toReal _ (fun j => (testParams.2.prob_pos k j).le)
      (fun j => (testParams.2.prob_lt_one k j).le) x
  · exact sum_resp testParams x

private noncomputable def testMeasure : Measure (Fin 2) :=
  ∑ k : Fin 2, ENNReal.ofReal (testParams.1.weight k) • Measure.dirac k

private theorem testMeasure_singleton (k' : Fin 2) :
    testMeasure {k'} = ENNReal.ofReal (testParams.1.weight k') := by
  have h0 : ∀ b ∈ (Finset.univ : Finset (Fin 2)), b ≠ k' →
      (ENNReal.ofReal (testParams.1.weight b) • Measure.dirac b) {k'} = 0 := by
    intro b _ hb
    have hbmem : b ∉ ({k'} : Set (Fin 2)) := by
      simp only [Set.mem_singleton_iff]
      exact hb
    rw [Measure.smul_apply, Measure.dirac_apply,
      Set.indicator_of_notMem hbmem, smul_eq_mul, mul_zero]
  have h1 : k' ∉ Finset.univ →
      (ENNReal.ofReal (testParams.1.weight k') • Measure.dirac k') {k'} = 0 :=
    fun h => absurd (Finset.mem_univ k') h
  show ((∑ k : Fin 2, ENNReal.ofReal (testParams.1.weight k) • Measure.dirac k) {k'}
      = ENNReal.ofReal (testParams.1.weight k'))
  rw [Measure.finsetSum_apply, Finset.sum_eq_single k' h0 h1,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton k'),
    smul_eq_mul, mul_one]

private instance testMeasure_finite : IsFiniteMeasure testMeasure := by
  refine ⟨?_⟩
  show ((∑ k : Fin 2, ENNReal.ofReal (testParams.1.weight k) • Measure.dirac k) Set.univ < ∞)
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _)]
  simp only [smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => (testParams.2.weight_pos k).le),
    testParams.2.weight_sum, ENNReal.ofReal_one]
  exact ENNReal.one_lt_top

/-- Test likelihood kernel: `localIndepPMF` masses as a kernel. -/
private noncomputable def testKernel : Kernel (Fin 2) (Fin 1 → Bool) :=
  ⟨fun k => ∑ y : Fin 1 → Bool,
      localIndepPMF (testParams.1.prob k) (fun j => (testParams.2.prob_pos k j).le)
        (fun j => (testParams.2.prob_lt_one k j).le) y • Measure.dirac y,
    measurable_of_countable _⟩

private theorem testKernel_singleton (x : Fin 1 → Bool) (k' : Fin 2) :
    testKernel k' {x}
      = localIndepPMF (testParams.1.prob k')
          (fun j => (testParams.2.prob_pos k' j).le)
          (fun j => (testParams.2.prob_lt_one k' j).le) x := by
  have h0 : ∀ b ∈ (Finset.univ : Finset (Fin 1 → Bool)), b ≠ x →
      (localIndepPMF (testParams.1.prob k')
        (fun j => (testParams.2.prob_pos k' j).le)
        (fun j => (testParams.2.prob_lt_one k' j).le) b • Measure.dirac b) {x} = 0 := by
    intro b _ hb
    have hbmem : b ∉ ({x} : Set (Fin 1 → Bool)) := by
      simp only [Set.mem_singleton_iff]
      exact hb
    rw [Measure.smul_apply, Measure.dirac_apply,
      Set.indicator_of_notMem hbmem, smul_eq_mul, mul_zero]
  have h1 : x ∉ Finset.univ →
      (localIndepPMF (testParams.1.prob k')
        (fun j => (testParams.2.prob_pos k' j).le)
        (fun j => (testParams.2.prob_lt_one k' j).le) x • Measure.dirac x) {x} = 0 :=
    fun h => absurd (Finset.mem_univ x) h
  show ((∑ y : Fin 1 → Bool, localIndepPMF (testParams.1.prob k')
      (fun j => (testParams.2.prob_pos k' j).le)
      (fun j => (testParams.2.prob_lt_one k' j).le) y • Measure.dirac y) {x}
      = localIndepPMF (testParams.1.prob k')
        (fun j => (testParams.2.prob_pos k' j).le)
        (fun j => (testParams.2.prob_lt_one k' j).le) x)
  rw [Measure.finsetSum_apply, Finset.sum_eq_single x h0 h1,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton x),
    smul_eq_mul, mul_one]

private instance testKernel_markov : IsMarkovKernel testKernel :=
  ⟨fun k => ⟨by
    have hLtop : ∀ y : Fin 1 → Bool, localIndepPMF (testParams.1.prob k)
        (fun j => (testParams.2.prob_pos k j).le)
        (fun j => (testParams.2.prob_lt_one k j).le) y ≠ ⊤ :=
      fun y => localIndepPMF_ne_top _ _ _ y
    have h1 : ∀ y : Fin 1 → Bool, localIndepPMF (testParams.1.prob k)
        (fun j => (testParams.2.prob_pos k j).le)
        (fun j => (testParams.2.prob_lt_one k j).le) y
        = ENNReal.ofReal (bernPMF (testParams.1.prob k) y) := by
      intro y
      have h2 := ENNReal.ofReal_toReal (hLtop y)
      rw [localIndepPMF_toReal _ _ _ _] at h2
      exact h2.symm
    show ((∑ y : Fin 1 → Bool, localIndepPMF (testParams.1.prob k)
        (fun j => (testParams.2.prob_pos k j).le)
        (fun j => (testParams.2.prob_lt_one k j).le) y • Measure.dirac y) Set.univ = 1)
    rw [Measure.finsetSum_apply]
    simp_rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _)]
    simp only [smul_eq_mul, mul_one]
    have hsum : ∑ y : Fin 1 → Bool, bernPMF (testParams.1.prob k) y = 1 := by
      have h := MathlibExt.Probability.FiniteProbability.sum_toReal_eq_one
        (localIndepPMF (testParams.1.prob k) (fun j => (testParams.2.prob_pos k j).le)
          (fun j => (testParams.2.prob_lt_one k j).le))
      simpa only [localIndepPMF_toReal] using h
    rw [Finset.sum_congr rfl (fun y _ => h1 y),
      ← ENNReal.ofReal_sum_of_nonneg (fun y _ =>
        (bernPMF_pos (testParams.2.prob_pos k) (testParams.2.prob_lt_one k) y).le),
      hsum, ENNReal.ofReal_one]⟩⟩

private theorem testEvidence_ne_zero (x : Fin 1 → Bool) :
    (testKernel ∘ₘ testMeasure) {x} ≠ 0 := by
  haveI : Nonempty (Fin 2) := ⟨⟨0, by decide⟩⟩
  rw [Measure.bind_apply (measurableSet_singleton x) (Kernel.aemeasurable testKernel)]
  have hμeq : testMeasure
      = (ENNReal.ofReal (testParams.1.weight 0) • Measure.dirac 0)
        + (ENNReal.ofReal (testParams.1.weight 1) • Measure.dirac 1) := by
    show (∑ k : Fin 2, ENNReal.ofReal (testParams.1.weight k) • Measure.dirac k) = _
    rw [Fin.sum_univ_two]
  rw [hμeq, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, testKernel_singleton, testKernel_singleton]
  have hterm : ∀ k' : Fin 2, ENNReal.ofReal (testParams.1.weight k')
        • localIndepPMF (testParams.1.prob k')
          (fun j => (testParams.2.prob_pos k' j).le)
          (fun j => (testParams.2.prob_lt_one k' j).le) x
        = ENNReal.ofReal (joint testParams x k') := by
    intro k'
    rw [smul_eq_mul]
    have hL : localIndepPMF (testParams.1.prob k')
          (fun j => (testParams.2.prob_pos k' j).le)
          (fun j => (testParams.2.prob_lt_one k' j).le) x
        = ENNReal.ofReal (bernPMF (testParams.1.prob k') x) := by
      have h2 := ENNReal.ofReal_toReal (localIndepPMF_ne_top (testParams.1.prob k')
        (fun j => (testParams.2.prob_pos k' j).le)
        (fun j => (testParams.2.prob_lt_one k' j).le) x)
      rw [localIndepPMF_toReal _ _ _ _] at h2
      exact h2.symm
    rw [hL, ← ENNReal.ofReal_mul (testParams.2.weight_pos k').le]
    have hj : joint testParams x k'
        = testParams.1.weight k' * bernPMF (testParams.1.prob k') x := rfl
    rw [hj]
  rw [hterm 0, hterm 1,
    ← ENNReal.ofReal_add (joint_pos testParams x 0).le (joint_pos testParams x 1).le]
  have hmarg : joint testParams x 0 + joint testParams x 1
      = marginal joint testParams x := by
    have h := Fin.sum_univ_two (fun k' => joint testParams x k')
    show joint testParams x 0 + joint testParams x 1 = ∑ k', joint testParams x k'
    rw [← h]
  rw [hmarg]
  exact (ENNReal.ofReal_pos.mpr (marginal_joint_pos testParams x)).ne'

/-- The posterior theorem applies to the test kernel and measure:
responsibilities are the canonical posterior singleton masses. -/
private theorem test_posterior_match_invocation (x : Fin 1 → Bool) (k : Fin 2) :
    resp testParams x k = ((testKernel†testMeasure) x {k}).toReal := by
  haveI : Nonempty (Fin 2) := ⟨⟨0, by decide⟩⟩
  exact (law_objective_posterior_match testParams x k testKernel testMeasure
    testMeasure_singleton (testKernel_singleton x)).2.2

end Cslib.MachineLearning.LatentVariable.ItemResponseEM
