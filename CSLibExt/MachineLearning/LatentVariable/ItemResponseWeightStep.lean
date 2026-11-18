/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.BernoulliMixture
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
structure WeightValid {Z : Type*} [Fintype Z] (w : Z → ℝ) : Prop where
  pos : ∀ z, 0 < w z
  sum_eq_one : ∑ z, w z = 1

/-- The valid latent weights, the parameter space of the weights-only step. -/
abbrev ValidWeights (Z : Type*) [Fintype Z] := {w : Z → ℝ // WeightValid w}

/-- The joint `p(w, x, z) = w z * P_z(x)` with the fixed locally independent item law `P_z`. -/
noncomputable def itemJoint {Z ι : Type*} [Fintype Z] [Fintype ι] [DecidableEq ι]
    (F : FixedItems Z ι) (w : ValidWeights Z) (x : ι → Bool) (z : Z) : ℝ :=
  w.1 z * (localIndepPMF (F.prob z) (fun i => (F.prob_pos z i).le)
    (fun i => (F.prob_lt_one z i).le) x).toReal

/-- The joint is strictly positive for every valid weight, pattern and latent state. -/
theorem itemJoint_pos {Z ι : Type*} [Fintype Z] [Fintype ι] [DecidableEq ι]
    (F : FixedItems Z ι) (w : ValidWeights Z) (x : ι → Bool) (z : Z) :
    0 < itemJoint F w x z := by
  refine mul_pos (w.2.pos z) (ENNReal.toReal_pos ?_ (PMF.apply_ne_top _ _))
  unfold localIndepPMF
  rw [PMF.ofFintype_apply, Finset.prod_ne_zero_iff]
  intro i _
  split
  · exact (ENNReal.ofReal_pos.mpr (F.prob_pos z i)).ne'
  · exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr (F.prob_lt_one z i))).ne'

/-- The posterior-average weight update `z ↦ (1 / N) ∑ n, p_θ(z | xₙ)` of a joint model `p`. -/
noncomputable def weightUpdate {Θ X Z : Type*} [Fintype Z] {N : ℕ} (p : Θ → X → Z → ℝ)
    (xs : Fin N → X) (θ : Θ) (z : Z) : ℝ :=
  (∑ n, posterior p θ (xs n) z) / N

/-- For a strictly positive joint and at least one data point, the posterior-average update is
a valid latent weight. -/
theorem weightUpdate_valid {Θ X Z : Type*} [Fintype Z] [Nonempty Z] {N : ℕ}
    {p : Θ → X → Z → ℝ} (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X) (hN : 0 < N) (θ : Θ) :
    WeightValid (weightUpdate p xs θ) := by
  have hm : ∀ x, 0 < marginal p θ x := fun x =>
    Finset.sum_pos (fun z _ => hp θ x z) Finset.univ_nonempty
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsum : ∀ x, ∑ z, posterior p θ x z = 1 := fun x => by
    simp only [posterior]
    rw [← Finset.sum_div]
    exact div_self (hm x).ne'
  refine ⟨fun z => div_pos (Finset.sum_pos (fun n _ => div_pos (hp θ _ z) (hm _))
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩) hNr, ?_⟩
  simp only [weightUpdate]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self hNr.ne'

/-- **The weights-only EM step** with fixed item parameters: the posterior-average weights, on
data with at least one point. -/
noncomputable def weightOnlyStep {Z ι : Type*} [Fintype Z] [Nonempty Z] [Fintype ι]
    [DecidableEq ι] {N : ℕ} (F : FixedItems Z ι) (xs : Fin N → ι → Bool) (hN : 0 < N)
    (w : ValidWeights Z) : ValidWeights Z :=
  ⟨weightUpdate (itemJoint F) xs w, weightUpdate_valid (itemJoint_pos F) xs hN w⟩

/-- **The weights-only step maximizes `Q(· | w)`** over all valid latent weights, with the item
parameters fixed. -/
theorem emQ_le_weightOnlyStep {Z ι : Type*} [Fintype Z] [Nonempty Z] [Fintype ι]
    [DecidableEq ι] {N : ℕ} (F : FixedItems Z ι) (xs : Fin N → ι → Bool) (hN : 0 < N)
    (w' w : ValidWeights Z) :
    emQ (itemJoint F) xs w' w ≤ emQ (itemJoint F) xs (weightOnlyStep F xs hN w) w := by
  have hPz : ∀ (z : Z) (x : ι → Bool), 0 < (localIndepPMF (F.prob z)
      (fun i => (F.prob_pos z i).le) (fun i => (F.prob_lt_one z i).le) x).toReal := by
    intro z x
    refine ENNReal.toReal_pos ?_ (PMF.apply_ne_top _ _)
    unfold localIndepPMF
    rw [PMF.ofFintype_apply, Finset.prod_ne_zero_iff]
    intro i _
    split
    · exact (ENNReal.ofReal_pos.mpr (F.prob_pos z i)).ne'
    · exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr (F.prob_lt_one z i))).ne'
  have hsplit : ∀ (t : ValidWeights Z) (x : ι → Bool) (z : Z),
      log (itemJoint F t x z) = log (t.1 z) + log ((localIndepPMF (F.prob z)
        (fun i => (F.prob_pos z i).le) (fun i => (F.prob_lt_one z i).le) x).toReal) := by
    intro t x z
    unfold itemJoint
    exact Real.log_mul (ne_of_gt (t.2.pos z)) (ne_of_gt (hPz z x))
  have hmJ : ∀ x : ι → Bool, 0 < marginal (itemJoint F) w x := fun x =>
    Finset.sum_pos (fun z _ => itemJoint_pos F w x z) Finset.univ_nonempty
  have hq1 : ∀ x : ι → Bool, ∑ z, posterior (itemJoint F) w x z = 1 := fun x =>
    (isDist_posterior (itemJoint_pos F) w x).2
  have hCeq : (∑ z, ∑ n, posterior (itemJoint F) w (xs n) z) = N := by
    rw [Finset.sum_comm]
    simp only [hq1]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hwnew : ∀ z, (weightOnlyStep F xs hN w).1 z
      = (∑ n, posterior (itemJoint F) w (xs n) z) / N := fun z => rfl
  have hemQ : ∀ t : ValidWeights Z, emQ (itemJoint F) xs t w
      = (∑ z, (∑ n, posterior (itemJoint F) w (xs n) z) * log (t.1 z))
        + (∑ n, ∑ z, posterior (itemJoint F) w (xs n) z
          * log ((localIndepPMF (F.prob z) (fun i => (F.prob_pos z i).le)
            (fun i => (F.prob_lt_one z i).le) (xs n)).toReal)) := by
    intro t
    have hswap : (∑ n, ∑ z, posterior (itemJoint F) w (xs n) z * log (t.1 z))
        = (∑ z, (∑ n, posterior (itemJoint F) w (xs n) z) * log (t.1 z)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [← Finset.sum_mul]
    show (∑ n, ∑ z, posterior (itemJoint F) w (xs n) z
      * log (itemJoint F t (xs n) z)) = _
    simp only [hsplit, mul_add, Finset.sum_add_distrib]
    rw [hswap]
  have hmain : (∑ z, (∑ n, posterior (itemJoint F) w (xs n) z) * log (w'.1 z))
      ≤ (∑ z, (∑ n, posterior (itemJoint F) w (xs n) z)
        * log ((weightOnlyStep F xs hN w).1 z)) := by
    have hc : ∀ z, 0 ≤ ∑ n, posterior (itemJoint F) w (xs n) z :=
      fun z => Finset.sum_nonneg
        (fun n _ => le_of_lt (div_pos (itemJoint_pos F w (xs n) z) (hmJ (xs n))))
    have hC : 0 < ∑ z, ∑ n, posterior (itemJoint F) w (xs n) z := by
      rw [hCeq]
      exact Nat.cast_pos.mpr hN
    have h := Cslib.MachineLearning.LatentVariable.BernoulliMixture.sum_mul_log_le_sum_mul_log_div
      (c := fun z => ∑ n, posterior (itemJoint F) w (xs n) z) (w := w'.1)
      hc hC w'.2.pos w'.2.sum_eq_one
    have h2 : (∑ z, (∑ n, posterior (itemJoint F) w (xs n) z) * log (w'.1 z))
        ≤ (∑ z, (∑ n, posterior (itemJoint F) w (xs n) z)
          * log ((∑ n, posterior (itemJoint F) w (xs n) z)
            / (∑ z', ∑ n, posterior (itemJoint F) w (xs n) z'))) := h
    rw [hCeq] at h2
    have hcongr : (∑ z, (∑ n, posterior (itemJoint F) w (xs n) z)
          * log ((∑ n, posterior (itemJoint F) w (xs n) z) / N))
        = (∑ z, (∑ n, posterior (itemJoint F) w (xs n) z)
          * log ((weightOnlyStep F xs hN w).1 z)) :=
      Finset.sum_congr rfl (fun z _ => by rw [← hwnew])
    rw [hcongr] at h2
    exact h2
  rw [hemQ w', hemQ (weightOnlyStep F xs hN w)]
  exact add_le_add_left hmain _
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
