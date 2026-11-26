/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ItemResponseWeightStep
import CSLibExt.MachineLearning.LatentVariable.BernoulliMixture

/-!
# Tests for the latent-weight EM step

Two latent states, one item, success probabilities 1/4 and 3/4, and
initial weights (1/2, 1/2): the updated weights, observed-mass and
log-likelihood gains, repeated observations, and the excluded
boundaries (empty data, boundary probabilities, non-rich data).
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.MachineLearning.LatentVariable.ItemResponseEM

open Real
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open MathlibExt.Probability.Statistics.Measurement
open Cslib.MachineLearning.LatentVariable.BernoulliMixture

/-! ## nonvacuity

Fixture: two latent states, one item, success probabilities `1/4` and `3/4`
(the Rasch model with difficulty `0` at abilities `∓ log 3`), initial weights `(1/2, 1/2)`.

-/

open Cslib.MachineLearning.LatentVariable.BernoulliMixture

/-- The fixture's success probabilities. -/
private noncomputable def tq : Fin 2 → ℝ := ![1 / 4, 3 / 4]

private noncomputable def tF : FixedItems (Fin 2) (Fin 1) where
  prob z _ := tq z
  prob_pos z _ := by fin_cases z <;> norm_num [tq]
  prob_lt_one z _ := by fin_cases z <;> norm_num [tq]

private noncomputable def tw0 : ValidWeights (Fin 2) :=
  ⟨![1 / 2, 1 / 2], ⟨fun z => by fin_cases z <;> norm_num, by norm_num [Fin.sum_univ_two]⟩⟩

/-- One correct response. -/
private def xs1 : Fin 1 → Fin 1 → Bool := fun _ _ => true

private theorem tjoint_true (w : ValidWeights (Fin 2)) (z : Fin 2) :
    itemJoint tF w (fun _ => true) z = w.1 z * tq z := by
  unfold itemJoint
  congr 1
  rw [localIndepPMF_apply, Fin.prod_univ_one]
  show (ENNReal.ofReal (tF.prob z 0)).toReal = tq z
  have h0 : tF.prob z 0 = tq z := rfl
  rw [h0]
  exact ENNReal.toReal_ofReal (by fin_cases z <;> norm_num [tq])

private theorem tjoint_false (w : ValidWeights (Fin 2)) (z : Fin 2) :
    itemJoint tF w (fun _ => false) z = w.1 z * (1 - tq z) := by
  unfold itemJoint
  congr 1
  rw [localIndepPMF_apply, Fin.prod_univ_one]
  show (ENNReal.ofReal (1 - tF.prob z 0)).toReal = 1 - tq z
  have h0 : tF.prob z 0 = tq z := rfl
  rw [h0]
  exact ENNReal.toReal_ofReal (by fin_cases z <;> norm_num [tq])

private theorem tmarg_true : marginal (itemJoint tF) tw0 (fun _ => true) = 1 / 2 := by
  have e0 : tw0.1 0 = (1 / 2 : ℝ) := by simp [tw0]
  have e1 : tw0.1 1 = (1 / 2 : ℝ) := by simp [tw0]
  have q0 : tq 0 = (1 / 4 : ℝ) := by simp [tq]
  have q1 : tq 1 = (3 / 4 : ℝ) := by simp [tq]
  simp only [marginal, Fin.sum_univ_two, tjoint_true, e0, e1, q0, q1]
  norm_num

private theorem tmarg_false : marginal (itemJoint tF) tw0 (fun _ => false) = 1 / 2 := by
  have e0 : tw0.1 0 = (1 / 2 : ℝ) := by simp [tw0]
  have e1 : tw0.1 1 = (1 / 2 : ℝ) := by simp [tw0]
  have q0 : tq 0 = (1 / 4 : ℝ) := by simp [tq]
  have q1 : tq 1 = (3 / 4 : ℝ) := by simp [tq]
  simp only [marginal, Fin.sum_univ_two, tjoint_false, e0, e1, q0, q1]
  norm_num

private theorem tpost_true (z : Fin 2) :
    posterior (itemJoint tF) tw0 (fun _ => true) z = tq z := by
  have hw : tw0.1 z = (1 / 2 : ℝ) := by fin_cases z <;> simp [tw0]
  simp only [posterior, tjoint_true, tmarg_true, hw]
  rw [div_eq_iff (by norm_num : ((1 / 2 : ℝ)) ≠ 0)]
  ring

private theorem tpost_false (z : Fin 2) :
    posterior (itemJoint tF) tw0 (fun _ => false) z = 1 - tq z := by
  have hw : tw0.1 z = (1 / 2 : ℝ) := by fin_cases z <;> simp [tw0]
  simp only [posterior, tjoint_false, tmarg_false, hw]
  rw [div_eq_iff (by norm_num : ((1 / 2 : ℝ)) ≠ 0)]
  ring

private theorem wstep1_eq (z : Fin 2) :
    (weightOnlyStep tF xs1 Nat.one_pos tw0).1 z
      = posterior (itemJoint tF) tw0 (xs1 0) z := by
  show weightUpdate (itemJoint tF) xs1 tw0 z = _
  unfold weightUpdate
  rw [Fin.sum_univ_one, Nat.cast_one, div_one]

private theorem hxs1 : xs1 0 = (fun _ : Fin 1 => true) := rfl

-- the main computation, one correct observation.
private theorem test_one_correct_step :
    (weightOnlyStep tF xs1 Nat.one_pos tw0).1 = ![1 / 4, 3 / 4] := by
  funext z
  fin_cases z
  · rw [wstep1_eq, hxs1, tpost_true]
    simp [tq]
  · rw [wstep1_eq, hxs1, tpost_true]
    simp [tq]

-- observed mass 1/2 -> 5/8.
private theorem test_one_correct_mass :
    marginal (itemJoint tF) tw0 (xs1 0) = 1 / 2 ∧
      marginal (itemJoint tF) (weightOnlyStep tF xs1 Nat.one_pos tw0) (xs1 0) = 5 / 8 := by
  have q0 : tq 0 = (1 / 4 : ℝ) := by simp [tq]
  have q1 : tq 1 = (3 / 4 : ℝ) := by simp [tq]
  have h0 : (weightOnlyStep tF xs1 Nat.one_pos tw0).1 0 = 1 / 4 := by
    have h := congrFun test_one_correct_step 0
    simpa using h
  have h1 : (weightOnlyStep tF xs1 Nat.one_pos tw0).1 1 = 3 / 4 := by
    have h := congrFun test_one_correct_step 1
    simpa using h
  constructor
  · rw [hxs1]
    exact tmarg_true
  · rw [hxs1]
    simp only [marginal, Fin.sum_univ_two, tjoint_true, h0, h1, q0, q1]
    norm_num

-- strict likelihood gain, log (1/2) < log (5/8).
private theorem test_one_correct_strict_gain :
    logLik (itemJoint tF) xs1 tw0 < logLik (itemJoint tF) xs1 (weightOnlyStep tF xs1 Nat.one_pos tw0)
      := by
  have hm := test_one_correct_mass
  have e : ∀ w : ValidWeights (Fin 2), logLik (itemJoint tF) xs1 w
      = log (marginal (itemJoint tF) w (xs1 0)) := by
    intro w
    show (∑ n, log (marginal (itemJoint tF) w (xs1 n))) = _
    rw [Fin.sum_univ_one]
  simp only [e]
  rw [hm.1, hm.2]
  rw [Real.log_lt_log_iff (by norm_num) (by norm_num)]
  norm_num

-- the accepted update is not the identity.
private theorem test_not_identity : weightOnlyStep tF xs1 Nat.one_pos tw0 ≠ tw0 := by
  intro hcon
  have h0 := congrArg (fun w : ValidWeights (Fin 2) => w.1 0) hcon
  have e0 : tw0.1 0 = (1 / 2 : ℝ) := by simp [tw0]
  have s0 : (weightOnlyStep tF xs1 Nat.one_pos tw0).1 0 = 1 / 4 := by
    have h := congrFun test_one_correct_step 0
    simpa using h
  rw [s0, e0] at h0
  norm_num at h0

-- repeated observations count with multiplicity.
/-- Data (correct, incorrect) leave `(1/2, 1/2)` fixed; repeating the correct response,
(correct, correct, incorrect), gives `(5/12, 7/12)`. -/
private theorem test_repeated_observations :
    (weightOnlyStep tF ![fun _ => true, fun _ => false] (by norm_num) tw0).1 = ![1 / 2, 1 / 2] ∧
      (weightOnlyStep tF ![fun _ => true, fun _ => true, fun _ => false] (by norm_num) tw0).1 =
        ![5 / 12, 7 / 12] := by
  have q0 : tq 0 = (1 / 4 : ℝ) := by simp [tq]
  have q1 : tq 1 = (3 / 4 : ℝ) := by simp [tq]
  have c0 : (![fun _ => true, fun _ => false] : Fin 2 → Fin 1 → Bool) 0
      = fun _ => true := rfl
  have c1 : (![fun _ => true, fun _ => false] : Fin 2 → Fin 1 → Bool) 1
      = fun _ => false := rfl
  have d0 : (![fun _ => true, fun _ => true, fun _ => false] : Fin 3 → Fin 1 → Bool) 0
      = fun _ => true := rfl
  have d1 : (![fun _ => true, fun _ => true, fun _ => false] : Fin 3 → Fin 1 → Bool) 1
      = fun _ => true := rfl
  have d2 : (![fun _ => true, fun _ => true, fun _ => false] : Fin 3 → Fin 1 → Bool) 2
      = fun _ => false := rfl
  have v0 : ((![1 / 2, 1 / 2] : Fin 2 → ℝ)) 0 = (1 / 2 : ℝ) := rfl
  have v1 : ((![1 / 2, 1 / 2] : Fin 2 → ℝ)) 1 = (1 / 2 : ℝ) := rfl
  have w0 : ((![5 / 12, 7 / 12] : Fin 2 → ℝ)) 0 = (5 / 12 : ℝ) := rfl
  have w1 : ((![5 / 12, 7 / 12] : Fin 2 → ℝ)) 1 = (7 / 12 : ℝ) := rfl
  constructor
  · funext z
    fin_cases z
    · show weightUpdate (itemJoint tF) ![fun _ => true, fun _ => false] tw0 0
          = (![1 / 2, 1 / 2] : Fin 2 → ℝ) 0
      unfold weightUpdate
      rw [Fin.sum_univ_two, c0, c1, tpost_true, tpost_false, q0, v0]
      norm_num
    · show weightUpdate (itemJoint tF) ![fun _ => true, fun _ => false] tw0 1
          = (![1 / 2, 1 / 2] : Fin 2 → ℝ) 1
      unfold weightUpdate
      rw [Fin.sum_univ_two, c0, c1, tpost_true, tpost_false, q1, v1]
      norm_num
  · funext z
    fin_cases z
    · show weightUpdate (itemJoint tF) ![fun _ => true, fun _ => true, fun _ => false] tw0 0
          = (![5 / 12, 7 / 12] : Fin 2 → ℝ) 0
      unfold weightUpdate
      rw [Fin.sum_univ_three, d0, d1, d2, tpost_true, tpost_false, q0, w0]
      norm_num
    · show weightUpdate (itemJoint tF) ![fun _ => true, fun _ => true, fun _ => false] tw0 1
          = (![5 / 12, 7 / 12] : Fin 2 → ℝ) 1
      unfold weightUpdate
      rw [Fin.sum_univ_three, d0, d1, d2, tpost_true, tpost_false, q1, w1]
      norm_num

-- N = 0 is excluded; the raw update is zero and leaves the valid weights.
private theorem test_empty_data_excluded :
    weightUpdate (itemJoint tF) (fun n : Fin 0 => n.elim0) tw0 = 0 ∧
      ¬ WeightValid (weightUpdate (itemJoint tF) (fun n : Fin 0 => n.elim0) tw0) := by
  have h0fun : weightUpdate (itemJoint tF) (fun n : Fin 0 => n.elim0) tw0 = 0 := by
    funext z
    show (∑ n : Fin 0, posterior (itemJoint tF) tw0 ((fun n : Fin 0 => n.elim0) n) z)
      / ((0 : ℕ) : ℝ) = 0
    simp
  constructor
  · exact h0fun
  · rw [h0fun]
    intro hcon
    exact lt_irrefl 0 (hcon.1 0)

/-- A boundary fixture: latent state `0` never answers correctly (probability `0`). -/
private noncomputable def bq : Fin 2 → ℝ := ![0, 1 / 2]

private theorem bq_nonneg (z : Fin 2) (i : Fin 1) : 0 ≤ (fun _ : Fin 1 => bq z) i := by
  fin_cases z <;> norm_num [bq]

private theorem bq_le_one (z : Fin 2) (i : Fin 1) : (fun _ : Fin 1 => bq z) i ≤ 1 := by
  fin_cases z <;> norm_num [bq]

/-- The boundary joint `w z * P_z(x)` on raw weights. -/
private noncomputable def bJoint (w : Fin 2 → ℝ) (x : Fin 1 → Bool) (z : Fin 2) : ℝ :=
  w z * (localIndepPMF (fun _ : Fin 1 => bq z) (bq_nonneg z) (bq_le_one z) x).toReal

private theorem bjoint_true (w : Fin 2 → ℝ) (z : Fin 2) :
    bJoint w (fun _ => true) z = w z * bq z := by
  unfold bJoint
  congr 1
  rw [localIndepPMF_apply, Fin.prod_univ_one]
  show (ENNReal.ofReal ((fun _ : Fin 1 => bq z) 0)).toReal = bq z
  have hbq : ∀ z : Fin 2, 0 ≤ bq z := fun z => by fin_cases z <;> norm_num [bq]
  exact ENNReal.toReal_ofReal (hbq z)

-- boundary probabilities are excluded; the joint vanishes and the update leaves the
-- strictly positive weights.
private theorem test_boundary_excluded :
    bJoint ![1 / 2, 1 / 2] (xs1 0) 0 = 0 ∧
      weightUpdate bJoint xs1 ![1 / 2, 1 / 2] = ![0, 1] ∧
      ¬ WeightValid (weightUpdate bJoint xs1 ![1 / 2, 1 / 2]) := by
  have bq0 : bq 0 = (0 : ℝ) := by simp [bq]
  have bq1 : bq 1 = (1 / 2 : ℝ) := by simp [bq]
  have w0 : ((![1 / 2, 1 / 2] : Fin 2 → ℝ)) 0 = (1 / 2 : ℝ) := rfl
  have w1 : ((![1 / 2, 1 / 2] : Fin 2 → ℝ)) 1 = (1 / 2 : ℝ) := rfl
  have bmarg : marginal bJoint ![1 / 2, 1 / 2] (fun _ => true) = 1 / 4 := by
    simp only [marginal, Fin.sum_univ_two, bjoint_true, w0, w1, bq0, bq1]
    norm_num
  have bpost0 : posterior bJoint ![1 / 2, 1 / 2] (fun _ => true) 0 = 0 := by
    simp only [posterior, bjoint_true, bmarg, w0, bq0]
    norm_num
  have bpost1 : posterior bJoint ![1 / 2, 1 / 2] (fun _ => true) 1 = 1 := by
    simp only [posterior, bjoint_true, bmarg, w1, bq1]
    norm_num
  have hwu : weightUpdate bJoint xs1 ![1 / 2, 1 / 2] = ![0, 1] := by
    funext z
    fin_cases z
    · show weightUpdate bJoint xs1 ![1 / 2, 1 / 2] 0 = ((![0, 1] : Fin 2 → ℝ)) 0
      unfold weightUpdate
      rw [Fin.sum_univ_one, Nat.cast_one, div_one, hxs1, bpost0]
      rfl
    · show weightUpdate bJoint xs1 ![1 / 2, 1 / 2] 1 = ((![0, 1] : Fin 2 → ℝ)) 1
      unfold weightUpdate
      rw [Fin.sum_univ_one, Nat.cast_one, div_one, hxs1, bpost1]
      rfl
  refine ⟨?_, hwu, ?_⟩
  · rw [hxs1, bjoint_true, w0, bq0]
    norm_num
  · rw [hwu]
    intro hcon
    have hpos := hcon.1 0
    simp at hpos

/-- The same fixture as Bernoulli-mixture parameters, for the item-parameter M-step. -/
private noncomputable def tθ : ValidParams 1 2 :=
  ⟨⟨![1 / 2, 1 / 2], fun k _ => tq k⟩,
    ⟨fun k => by fin_cases k <;> norm_num, by norm_num [Fin.sum_univ_two],
      fun k _ => by fin_cases k <;> norm_num [tq], fun k _ => by fin_cases k <;> norm_num [tq]⟩⟩

-- non-rich data. The item-parameter M-step leaves the interior (probability 1), while
-- the weights-only step needs no richness and is valid.
private theorem test_non_rich :
    ¬ Rich xs1 ∧ (∀ k, (mStep xs1 tθ).prob k 0 = 1) ∧ ¬ (mStep xs1 tθ).Valid ∧
      WeightValid (weightUpdate (itemJoint tF) xs1 tw0) := by
  have hnot : ¬ Rich xs1 := by
    intro hcon
    obtain ⟨pos, both⟩ := hcon
    obtain ⟨ht, hf⟩ := both 0
    obtain ⟨n, hn⟩ := hf
    simp [xs1] at hn
  have hbern : ∀ k : Fin 2, bernPMF (tθ.1.prob k) (fun _ => true) = tq k := by
    intro k
    simp only [bernPMF, Fin.prod_univ_one]
    exact rfl
  have hbern0 : ∀ k : Fin 2, bernPMF (tθ.1.prob k) (xs1 0) = tq k := fun k => hbern k
  have hjoint : ∀ k : Fin 2, joint tθ (xs1 0) k = (1 / 2) * tq k := by
    intro k
    have hwk : tθ.1.weight k = (1 / 2 : ℝ) := by fin_cases k <;> simp [tθ]
    show tθ.1.weight k * bernPMF (tθ.1.prob k) (xs1 0) = (1 / 2) * tq k
    rw [hbern0, hwk]
  have hmarg : marginal joint tθ (xs1 0) = 1 / 2 := by
    have q0 : tq 0 = (1 / 4 : ℝ) := by simp [tq]
    have q1 : tq 1 = (3 / 4 : ℝ) := by simp [tq]
    simp only [marginal, Fin.sum_univ_two, hjoint, q0, q1]
    norm_num
  have hresp : ∀ k : Fin 2, resp tθ (xs1 0) k ≠ 0 := by
    intro k
    show posterior joint tθ (xs1 0) k ≠ 0
    simp only [posterior, hjoint, hmarg]
    have hqk : tq k ≠ 0 := by
      fin_cases k
      · show tq 0 ≠ 0
        norm_num [tq]
      · show tq 1 ≠ 0
        norm_num [tq]
    have e : ((1 / 2 : ℝ) * tq k) / (1 / 2) = tq k := by
      rw [div_eq_iff (by norm_num : ((1 / 2 : ℝ)) ≠ 0)]
      ring
    rw [e]
    exact hqk
  have hones : ∀ k : Fin 2, ones xs1 tθ k 0 = resp tθ (xs1 0) k := by
    intro k
    show (∑ n : Fin 1, (if xs1 n 0 then resp tθ (xs1 n) k else 0))
      = resp tθ (xs1 0) k
    rw [Fin.sum_univ_one]
    have hcc : xs1 0 0 = true := rfl
    rw [hcc]
    simp
  have hmass : ∀ k : Fin 2, mass xs1 tθ k = resp tθ (xs1 0) k := by
    intro k
    show (∑ n : Fin 1, resp tθ (xs1 n) k) = resp tθ (xs1 0) k
    rw [Fin.sum_univ_one]
  have hprob : ∀ k : Fin 2, (mStep xs1 tθ).prob k 0 = 1 := by
    intro k
    show ones xs1 tθ k 0 / mass xs1 tθ k = 1
    rw [hones, hmass]
    exact div_self (hresp k)
  have hnvalid : ¬ (mStep xs1 tθ).Valid := by
    intro hcon
    have hlt := hcon.prob_lt_one 0 0
    rw [hprob] at hlt
    exact lt_irrefl 1 hlt
  have hvalid : WeightValid (weightUpdate (itemJoint tF) xs1 tw0) :=
    weightUpdate_valid (itemJoint_pos tF) xs1 Nat.one_pos tw0
  exact ⟨hnot, hprob, hnvalid, hvalid⟩

private noncomputable def thlog : Fin 2 → ℝ := ![-Real.log 3, Real.log 3]

-- the fixture is a Rasch model (discrimination 1, difficulty 0, abilities ∓ log 3).
private theorem test_rasch_fixture :
    (FixedItems.twoPL (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0) ![-Real.log 3, Real.log 3]).prob =
      tF.prob := by
  have hexp : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)
  have hsig1 : Real.sigmoid (Real.log 3) = 3 / 4 := by
    simp only [Real.sigmoid]
    rw [Real.exp_neg, hexp]
    norm_num
  have hsig2 : Real.sigmoid (-Real.log 3) = 1 / 4 := by
    simp only [Real.sigmoid]
    rw [neg_neg, hexp]
    norm_num
  have hprob : ∀ (z : Fin 2) (i : Fin 1),
      (FixedItems.twoPL (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0)
        ![-Real.log 3, Real.log 3]).prob z i
        = Real.sigmoid (thlog z) := by
    intro z i
    show Real.sigmoid ((fun _ : Fin 1 => (1 : ℝ)) i
      * (thlog z - (fun _ : Fin 1 => (0 : ℝ)) i))
      = Real.sigmoid (thlog z)
    have harg : (fun _ : Fin 1 => (1 : ℝ)) i
        * (thlog z - (fun _ : Fin 1 => (0 : ℝ)) i)
        = thlog z := by simp
    rw [harg]
  funext z i
  fin_cases z <;> fin_cases i
  · show (FixedItems.twoPL (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0)
        ![-Real.log 3, Real.log 3]).prob 0 0 = tF.prob 0 0
    rw [hprob]
    have e1 : thlog 0 = -Real.log 3 := rfl
    have e2 : tF.prob 0 0 = (1 / 4 : ℝ) := rfl
    rw [e1, e2]
    exact hsig2
  · show (FixedItems.twoPL (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0)
        ![-Real.log 3, Real.log 3]).prob 1 0 = tF.prob 1 0
    rw [hprob]
    have e1 : thlog 1 = Real.log 3 := rfl
    have e2 : tF.prob 1 0 = (3 / 4 : ℝ) := rfl
    rw [e1, e2]
    exact hsig1


end Cslib.MachineLearning.LatentVariable.ItemResponseEM
