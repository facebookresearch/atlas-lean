/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCountMLE

import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Finset
open scoped Nat
open MathlibExt.Biology.Omics.HierarchicalCount

namespace MathlibExtTest.Biology.Omics.HierarchicalCountMLE

/-- One zero count, `a = b = s = 1`: the marginal mass is `NB(1, 1)(0) = 1 / 2`, so the log
marginal likelihood is `-log 2`, both from the definition and from the closed form. -/
example : logMarginalLik 1 1 (fun _ : Unit => (1 : ℝ)) (fun _ => 0) = -log 2 := by
  rw [logMarginalLik_eq one_pos one_pos (fun _ => one_pos)]
  norm_num

example : log (marginalLik 1 1 1 0) = -log 2 := by
  rw [marginalLik_eq_negBinomialReal one_pos one_pos zero_le_one]
  norm_num [negBinomialReal, ← log_inv]

/-- The digamma increment at `a = 1`, `k = 3` is the harmonic number `1 + 1/2 + 1/3 = 11/6`. -/
example : digammaIncrement 1 3 = 11 / 6 := by
  norm_num [digammaIncrement, sum_range_succ]

/-- The digamma increment of a zero count is `0`. -/
example (a : ℝ) : digammaIncrement a 0 = 0 := by simp [digammaIncrement]

/-- Score equations at a concrete point: one count `k = 1`, `s = 1`, `a = b = 1`. The rate score
`1 - 2 / 2` vanishes; the shape score is `1 + log 1 - log 2 = 1 - log 2`. -/
example : rateScore 1 1 (fun _ : Unit => (1 : ℝ)) (fun _ => 1) = 0 ∧
    shapeScore 1 1 (fun _ : Unit => (1 : ℝ)) (fun _ => 1) = 1 - log 2 := by
  refine ⟨by norm_num [rateScore], ?_⟩
  norm_num [shapeScore, digammaIncrement]

/-- The shape derivative of `ℓ` at that point is the shape score. -/
example : HasDerivAt (fun x => logMarginalLik x 1 (fun _ : Unit => (1 : ℝ)) (fun _ => 1))
    (1 - log 2) 1 := by
  have h := hasDerivAt_logMarginalLik_shape (a := 1) (b := 1) one_pos one_pos
    (s := fun _ : Unit => (1 : ℝ)) (fun _ => one_pos) (fun _ => 1)
  convert h using 1
  norm_num [shapeScore, digammaIncrement]

/-- The rate derivative of `ℓ` at that point vanishes. -/
example : HasDerivAt (fun y => logMarginalLik 1 y (fun _ : Unit => (1 : ℝ)) (fun _ => 1)) 0 1 := by
  have h := hasDerivAt_logMarginalLik_rate (a := 1) (b := 1) one_pos one_pos
    (s := fun _ : Unit => (1 : ℝ)) (fun _ => one_pos) (fun _ => 1)
  convert h using 1
  norm_num [rateScore]

/-- **Boundary: all-zero counts.** With two zero counts the rate score `2 (1 - 1 / 2) = 1` is
positive, as `rateScore_pos_of_counts_eq_zero` predicts: no finite rate MLE. -/
example : rateScore 1 1 (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 0) = 1 ∧
    0 < rateScore 1 1 (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 0) := by
  refine ⟨by norm_num [rateScore], ?_⟩
  exact rateScore_pos_of_counts_eq_zero one_pos one_pos (fun _ => one_pos) (fun _ => rfl)

/-- **Strict concavity is non-vacuous.** One positive count suffices for strict concavity in the
shape, and a nonempty sample for strict concavity in the log rate. -/
example : StrictConcaveOn ℝ (Set.Ioi 0)
    (fun x => logMarginalLik x 1 (fun _ : Unit => (1 : ℝ)) (fun _ => 2)) :=
  strictConcaveOn_logMarginalLik_shape one_pos (fun _ => one_pos) ⟨(), two_pos⟩

example : StrictConcaveOn ℝ Set.univ
    (fun t => logMarginalLik 1 (exp t) (fun _ : Unit => (1 : ℝ)) (fun _ => 0)) :=
  strictConcaveOn_logMarginalLik_logRate one_pos (fun _ => one_pos) _

/-- Concavity in the shape holds even for all-zero counts (then `ℓ` is affine in `a`). -/
example : ConcaveOn ℝ (Set.Ioi 0)
    (fun x => logMarginalLik x 1 (fun _ : Unit => (1 : ℝ)) (fun _ => 0)) :=
  concaveOn_logMarginalLik_shape one_pos (fun _ => one_pos) _

/-- The joint log marginal likelihood is not concave. -/
example : ¬ ConcaveOn ℝ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    (fun p : ℝ × ℝ => logMarginalLik p.1 p.2 (fun _ : Unit => (1 : ℝ)) (fun _ => 0)) :=
  not_concaveOn_logMarginalLik

/-- `rateScoreLog` at `b = 0` is `n a`, and the rate MLE at `a = 1` for the sample `(0, 2)` at
size factor `1` exists. -/
example : rateScoreLog 1 0 (fun _ : Fin 2 => (1 : ℝ)) (fun i => if i = 0 then 0 else 2) = 2 := by
  norm_num [rateScoreLog]

example : ∃ b, 0 < b ∧
    rateScore 1 b (fun _ : Fin 2 => (1 : ℝ)) (fun i => if i = 0 then 0 else 2) = 0 :=
  exists_rateScore_eq_zero one_pos (fun _ => one_pos) ⟨1, by simp⟩

/-- At a fixed rate the shape MLE exists for the sample `(0, 2)`. -/
example : ∃ a, 0 < a ∧
    shapeScore a 1 (fun _ : Fin 2 => (1 : ℝ)) (fun i => if i = 0 then 0 else 2) = 0 :=
  exists_shapeScore_eq_zero one_pos (fun _ => one_pos) ⟨1, by simp⟩

/-- **Common size factor.** For the sample `(1, 1)` at `σ = 1` and shape `a = 2`, the rate MLE is
`σ a / M = 2`; it is the unique root and the global maximizer of `ℓ(2, ·)`. -/
example : countMean (fun _ : Fin 2 => 1) = 1 := by norm_num [countMean]

example : rateScore 2 2 (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) = 0 := by
  norm_num [rateScore]

example : logMarginalLik 2 3 (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) <
    logMarginalLik 2 2 (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) :=
  logMarginalLik_lt_of_rateScore_eq_zero two_pos two_pos (by norm_num) (by norm_num)
    (fun _ => one_pos) (by norm_num [rateScore])

/-- The rate score is unbiased under the marginal law, here at `a = 2`, `b = 1`, `s = 3`. -/
example : HasSum (fun k : ℕ => (2 / 1 - (2 + k) / (1 + 3)) * marginalLik 2 1 3 k) 0 :=
  hasSum_rateScore_term_mul_marginalLik two_pos one_pos (by norm_num)

/-- The sample `(0, 0, 3)`: mean `M = 1`, biased variance `V = 3 - 1 = 2`, overdispersed. -/
private def k003 : Fin 3 → ℕ := ![0, 0, 3]

example : countMean k003 = 1 := by
  norm_num [countMean, k003, Fin.sum_univ_three]

example : countVar k003 = 2 := by
  norm_num [countVar, countMean, k003, Fin.sum_univ_three]

/-- **Overdispersion gives a solution of the score equations**, here for `(0, 0, 3)` (`M = 1 < 2
= V`) at `σ = 1`; by the next examples it is not the moment estimate `(1, 1)`. -/
example : ∃ a b, 0 < a ∧ 0 < b ∧ shapeScore a b (fun _ : Fin 3 => (1 : ℝ)) k003 = 0 ∧
    rateScore a b (fun _ : Fin 3 => (1 : ℝ)) k003 = 0 := by
  have hM : countMean k003 = 1 := by norm_num [countMean, k003, Fin.sum_univ_three]
  have hV : countVar k003 = 2 := by norm_num [countVar, countMean, k003, Fin.sum_univ_three]
  exact exists_score_root_of_overdispersed one_pos (hM ▸ one_pos) (by rw [hM, hV]; norm_num)

/-- **Method of moments solves the rate equation.** For `(0, 0, 3)` at `σ = 1`, the moment
estimates `(1, 1)` solve the rate score equation. -/
example : momShape 1 2 = 1 ∧ momRate 1 1 2 = 1 ∧
    rateScore 1 1 (fun _ : Fin 3 => (1 : ℝ)) k003 = 0 := by
  have hM : countMean k003 = 1 := by norm_num [countMean, k003, Fin.sum_univ_three]
  have h := rateScore_mom_eq_zero (σ := 1) (V := 2) one_pos (hM ▸ one_pos) (by rw [hM]; norm_num)
  rw [hM] at h
  refine ⟨by norm_num [momShape], by norm_num [momRate], ?_⟩
  norm_num [momShape, momRate] at h
  exact h

/-- **The MLE differs from the method of moments.** For `(0, 0, 3)` the moment shape estimate
`1` is not a root of the profile shape score: `11/6 - 3 log 2 < 0`, so the moment estimates do not
solve the shape score equation. -/
example : profileShapeScore 1 k003 = 11 / 6 - 3 * log 2 ∧ profileShapeScore 1 k003 < 0 := by
  have hM : countMean k003 = 1 := by norm_num [countMean, k003, Fin.sum_univ_three]
  have hval : profileShapeScore 1 k003 = 11 / 6 - 3 * log 2 := by
    rw [profileShapeScore, hM]
    norm_num [k003, Fin.sum_univ_three, digammaIncrement, sum_range_succ]
  refine ⟨hval, ?_⟩
  rw [hval]
  linarith [log_two_gt_d9]

example : ¬ (shapeScore 1 1 (fun _ : Fin 3 => (1 : ℝ)) k003 = 0 ∧
    rateScore 1 1 (fun _ : Fin 3 => (1 : ℝ)) k003 = 0) := by
  have hM : countMean k003 = 1 := by norm_num [countMean, k003, Fin.sum_univ_three]
  rw [score_eq_zero_iff_const one_pos one_pos one_pos (hM ▸ one_pos), hM]
  rintro ⟨-, h⟩
  have hval : profileShapeScore 1 k003 = 11 / 6 - 3 * log 2 := by
    rw [profileShapeScore, hM]
    norm_num [k003, Fin.sum_univ_three, digammaIncrement, sum_range_succ]
  rw [hval] at h
  linarith [log_two_gt_d9]

/-- The MLE and the moment estimator share the plug-in prior mean `M / σ`. -/
example {a b : ℝ} (hb : 0 < b) (h : rateScore a b (fun _ : Fin 3 => (1 : ℝ)) k003 = 0) :
    a / b = 1 := by
  have hM : countMean k003 = 1 := by norm_num [countMean, k003, Fin.sum_univ_three]
  have := (div_eq_mom_of_rateScore_eq_zero (V := 2) hb one_pos (hM ▸ one_pos)
    (by rw [hM]; norm_num) h).1
  rwa [hM, div_one] at this

/-- The population profile shape score of the constant count `2` at `a = 1` is
`(1 + 1/2) - (log 3 - log 1)`. -/
example : popProfileShapeScore (Measure.dirac ()) (fun _ : Unit => 2) 1 = 3 / 2 - log 3 := by
  norm_num [popProfileShapeScore, digammaIncrement, sum_range_succ]

/-- **The rate-MLE consistency theorem is non-vacuous.** The constant count sequence `Xᵢ ≡ 1` on a
one-point probability space is pairwise independent and identically distributed with mean `1`,
the marginal mean at `a = b = σ = 1`; the theorem then gives `b̂ₙ → 1`. -/
example : ∀ᵐ _ ∂(Measure.dirac ()),
    Tendsto (fun n => 1 * 1 / countMean (fun _ : Fin n => 1)) atTop (𝓝 (1 : ℝ)) := by
  have h := ae_tendsto_rateMLE (μ := Measure.dirac ()) (X := fun _ _ => 1) (a := 1) (b := 1)
    (σ := 1) one_pos one_pos one_pos (fun i j _ => indepFun_const_left 1 _)
    (fun _ => IdentDistrib.refl aemeasurable_const) (integrable_const _) (by simp)
  filter_upwards [h] with _ hω using hω.2

end MathlibExtTest.Biology.Omics.HierarchicalCountMLE
