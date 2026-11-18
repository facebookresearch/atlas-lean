/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ItemResponseEM

/-!
# Tests for the item-response EM correspondence

Repeated observations versus full-outcome normalization, and positive
evidence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
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

private theorem bernPMF_sum_one {d : ℕ} (q : Fin d → ℝ) :
    ∑ y : Fin d → Bool, bernPMF q y = 1 := by
  have hfac : (∑ y : Fin d → Bool, bernPMF q y)
      = ∏ j, ∑ b : Bool, (if b then q j else 1 - q j) := by
    have h := Finset.sum_prod_piFinset (ι := Fin d) (κ := Bool)
      (s := Finset.univ)
      (fun j b => if b then q j else 1 - q j)
    rw [Fintype.piFinset_univ] at h
    exact h
  rw [hfac]
  refine Finset.prod_eq_one (fun j _ => ?_)
  rw [Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true]
  ring

/-- The EM joint normalizes over patterns and latent states. -/
private theorem joint_sum_one {d K : ℕ} (θ : ValidParams d K) :
    ∑ y : Fin d → Bool, ∑ k' : Fin K, joint θ y k' = 1 := by
  have hB : ∀ k' : Fin K, ∑ y : Fin d → Bool, bernPMF (θ.1.prob k') y = 1 :=
    fun k' => bernPMF_sum_one (θ.1.prob k')
  show (∑ y : Fin d → Bool, ∑ k' : Fin K, θ.1.weight k' * bernPMF (θ.1.prob k') y) = 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hB, mul_one]
  exact θ.2.weight_sum

/-- Real reading of the locally independent law is the product-Bernoulli mass. -/
private theorem localIndepPMF_toReal {d : ℕ} (q : Fin d → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) (x : Fin d → Bool) :
    (localIndepPMF q hq0 hq1 x).toReal = bernPMF q x := by
  rw [localIndepPMF_apply, ENNReal.toReal_prod]
  unfold bernPMF
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : x i = true
  · simp only [ite_eq_left h]
    exact ENNReal.toReal_ofReal (hq0 i)
  · simp only [ite_eq_right h]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (hq1 i))
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

end Cslib.MachineLearning.LatentVariable.ItemResponseEM
