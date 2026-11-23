/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ExpectationMaximization
public import MathlibExt.Probability.Statistics.Measurement.ItemResponse

/-!
# Expectation maximization for latent weights with fixed items

With item parameters fixed, the latent-weight update replaces each
weight by its posterior average over the data. For a nonempty data
set the update stays among the strictly positive normalized weights,
maximizes the EM auxiliary function over that subtype, and therefore
never decreases the log-likelihood. Rasch and two-parameter logistic
item parameters are instances of the fixed items.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.MachineLearning.LatentVariable.ItemResponseEM

open Real
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open MathlibExt.Probability.Statistics.Measurement

/-- Fixed item parameters on a latent grid `Z`: each latent state `z` has success
probabilities `prob z i` strictly between `0` and `1` on the items `i`. -/
structure FixedItems (Z ι : Type*) where
  /-- The success probability of item `i` at latent state `z`. -/
  prob : Z → ι → ℝ
  prob_pos : ∀ z i, 0 < prob z i
  prob_lt_one : ∀ z i, prob z i < 1

/-- Fixed two-parameter logistic items with discriminations `a` and difficulties `b` on the
latent abilities `θ z`; discriminations `1` give the Rasch model. -/
noncomputable def FixedItems.twoPL {Z ι : Type*} (a b : ι → ℝ) (θ : Z → ℝ) : FixedItems Z ι where
  prob z i := Real.sigmoid (a i * (θ z - b i))
  prob_pos _ _ := Real.sigmoid_pos _
  prob_lt_one _ _ := Real.sigmoid_lt_one _

/-- The response law of a fixed two-parameter logistic latent state is the 2PL law. -/
theorem localIndepPMF_twoPL {Z ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ)
    (θ : Z → ℝ) (z : Z) :
    localIndepPMF ((FixedItems.twoPL a b θ).prob z)
        (fun i => ((FixedItems.twoPL a b θ).prob_pos z i).le)
        (fun i => ((FixedItems.twoPL a b θ).prob_lt_one z i).le)
      = twoPLPMF a b (θ z) := by
  rfl

/-- Latent weights: strictly positive and summing to one. -/
abbrev WeightValid {Z : Type*} [Fintype Z] (w : Z → ℝ) : Prop :=
  (∀ z, 0 < w z) ∧ ∑ z, w z = 1

/-- The valid latent weights, the parameter space of the weights-only step. -/
abbrev ValidWeights (Z : Type*) [Fintype Z] :=
  Cslib.MachineLearning.LatentVariable.ExpectationMaximization.PosWeights Z

/-- The joint `p(w, x, z) = w z * P_z(x)` with the fixed locally independent item law `P_z`. -/
noncomputable def itemJoint {Z ι : Type*} [Fintype Z] [Fintype ι] [DecidableEq ι]
    (F : FixedItems Z ι) (w : ValidWeights Z) (x : ι → Bool) (z : Z) : ℝ :=
  w.1 z * (localIndepPMF (F.prob z) (fun i => (F.prob_pos z i).le)
    (fun i => (F.prob_lt_one z i).le) x).toReal

/-- The joint is strictly positive for every valid weight, pattern and latent state. -/
theorem itemJoint_pos {Z ι : Type*} [Fintype Z] [Fintype ι] [DecidableEq ι]
    (F : FixedItems Z ι) (w : ValidWeights Z) (x : ι → Bool) (z : Z) :
    0 < itemJoint F w x z := by
  refine mul_pos (w.2.1 z) (ENNReal.toReal_pos ?_ (PMF.apply_ne_top _ _))
  unfold localIndepPMF
  rw [PMF.ofFintype_apply, Finset.prod_ne_zero_iff]
  intro i _
  split
  · exact (ENNReal.ofReal_pos.mpr (F.prob_pos z i)).ne'
  · exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr (F.prob_lt_one z i))).ne'

/-- The fixed item likelihood `P_z(x)` (the weight-free part of `itemJoint`). -/
noncomputable def itemLik {Z ι : Type*} [Fintype Z] [Fintype ι] [DecidableEq ι]
    (F : FixedItems Z ι) (x : ι → Bool) (z : Z) : ℝ :=
  (localIndepPMF (F.prob z) (fun i => (F.prob_pos z i).le)
    (fun i => (F.prob_lt_one z i).le) x).toReal

/-- The fixed item likelihood is strictly positive. -/
theorem itemLik_pos {Z ι : Type*} [Fintype Z] [Fintype ι] [DecidableEq ι]
    (F : FixedItems Z ι) (x : ι → Bool) (z : Z) : 0 < itemLik F x z := by
  unfold itemLik
  refine ENNReal.toReal_pos ?_ (PMF.apply_ne_top _ _)
  unfold localIndepPMF
  rw [PMF.ofFintype_apply, Finset.prod_ne_zero_iff]
  intro i _
  split
  · exact (ENNReal.ofReal_pos.mpr (F.prob_pos z i)).ne'
  · exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr (F.prob_lt_one z i))).ne'

/-- **The weights-only EM step** with fixed item parameters: the posterior-average weights, on
data with at least one point. -/
noncomputable def weightOnlyStep {Z ι : Type*} [Fintype Z] [Nonempty Z] [Fintype ι]
    [DecidableEq ι] {N : ℕ} (F : FixedItems Z ι) (xs : Fin N → ι → Bool) (hN : 0 < N)
    (w : ValidWeights Z) : ValidWeights Z :=
  weightStep (hlik := fun x z => itemLik_pos F x z) xs hN w

/-- **The weights-only step maximizes `Q(· | w)`** over all valid latent weights, with the item
parameters fixed. -/
theorem emQ_le_weightOnlyStep {Z ι : Type*} [Fintype Z] [Nonempty Z] [Fintype ι]
    [DecidableEq ι] {N : ℕ} (F : FixedItems Z ι) (xs : Fin N → ι → Bool) (hN : 0 < N)
    (w' w : ValidWeights Z) :
    emQ (itemJoint F) xs w' w ≤ emQ (itemJoint F) xs (weightOnlyStep F xs hN w) w := by
  exact emQ_le_weightStep (hlik := fun x z => itemLik_pos F x z) xs hN w' w

/-- **The weights-only step does not decrease the log-likelihood.** -/
theorem logLik_le_weightOnlyStep {Z ι : Type*} [Fintype Z] [Nonempty Z] [Fintype ι]
    [DecidableEq ι] {N : ℕ} (F : FixedItems Z ι) (xs : Fin N → ι → Bool) (hN : 0 < N)
    (w : ValidWeights Z) :
    logLik (itemJoint F) xs w ≤ logLik (itemJoint F) xs (weightOnlyStep F xs hN w) := by
  exact logLik_le_of_emQ_le (itemJoint_pos F) xs (emQ_le_weightOnlyStep F xs hN _ w)

/-- **The log-likelihood is monotone along the iterates of the weights-only step.** -/
theorem logLik_iterate_weightOnlyStep_monotone {Z ι : Type*} [Fintype Z] [Nonempty Z]
    [Fintype ι] [DecidableEq ι] {N : ℕ} (F : FixedItems Z ι) (xs : Fin N → ι → Bool)
    (hN : 0 < N) (w₀ : ValidWeights Z) :
    Monotone fun t => logLik (itemJoint F) xs ((weightOnlyStep F xs hN)^[t] w₀) := by
  exact logLik_iterate_monotone (itemJoint_pos F) xs
    (M := weightOnlyStep F xs hN) (fun w => emQ_le_weightOnlyStep F xs hN _ w) w₀


end Cslib.MachineLearning.LatentVariable.ItemResponseEM
