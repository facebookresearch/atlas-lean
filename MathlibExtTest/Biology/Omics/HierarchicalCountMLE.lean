/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCountMLE

import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Finset Function
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

/-- **Cubic bound, checked at a point.** At `a = 10`, `k = 3`, computed from the definitions, the
increment is `1/10 + 1/11 + 1/12 = 181/660 ≈ 0.2742` and the cubic bound is
`3/10 - 3/100 + 27/1000 = 297/1000`, so the bound holds with slack `< 0.023`. -/
example : digammaIncrement 10 3 = 181 / 660 ∧
    ((3 : ℕ) : ℝ) / 10 - ((3 : ℕ) * ((3 : ℕ) - 1) / 2) / 10 ^ 2 + ((3 : ℕ) : ℝ) ^ 3 / 10 ^ 3 =
      297 / 1000 ∧
    (181 / 660 : ℝ) ≤ 297 / 1000 ∧ (297 / 1000 : ℝ) - 181 / 660 < 23 / 1000 := by
  refine ⟨by norm_num [digammaIncrement, sum_range_succ], by norm_num, by norm_num, by norm_num⟩

example : digammaIncrement 10 3 ≤ 297 / 1000 := by
  have h := digammaIncrement_le_cubic (a := 10) (by norm_num) 3
  norm_num at h
  exact h

/-- **Tight at `k = 0`**: both sides of `digammaIncrement_le_cubic` are `0`. -/
example (a : ℝ) : digammaIncrement a 0 =
    ((0 : ℕ) : ℝ) / a - ((0 : ℕ) * ((0 : ℕ) - 1) / 2) / a ^ 2 + ((0 : ℕ) : ℝ) ^ 3 / a ^ 3 := by
  simp [digammaIncrement]

/-- **The cubic term is needed.** At `a = 1`, `k = 2` the increment `1 + 1/2 = 3/2` exceeds the
second-order truncation `2/1 - (2 · 1 / 2)/1² = 1`, so the bound fails without `k³ / a³`. -/
example : ((2 : ℕ) : ℝ) / 1 - ((2 : ℕ) * ((2 : ℕ) - 1) / 2) / 1 ^ 2 < digammaIncrement 1 2 := by
  norm_num [digammaIncrement, sum_range_succ]

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

/-- **Boundary: all-zero counts, shape.** With one zero count the shape score
`log b - log (b + 1)` is negative at every shape, so there is no shape root. -/
example {a b : ℝ} (hb : 0 < b) : shapeScore a b (fun _ : Unit => (1 : ℝ)) (fun _ => 0) < 0 := by
  simp [shapeScore, digammaIncrement]
  exact log_lt_log hb (by linarith)

/-- With all-zero counts `ℓ` is affine in the shape, so strict concavity fails: the hypothesis
"some count is positive" of `strictConcaveOn_logMarginalLik_shape` is needed. -/
example : ¬ StrictConcaveOn ℝ (Set.Ioi 0)
    (fun x => logMarginalLik x 1 (fun _ : Unit => (1 : ℝ)) (fun _ => 0)) := by
  intro h
  have e : ∀ x : ℝ, 0 < x →
      logMarginalLik x 1 (fun _ : Unit => (1 : ℝ)) (fun _ => 0) = -(x * log 2) := by
    intro x hx; rw [logMarginalLik_eq hx one_pos (fun _ => one_pos)]; norm_num
  have := h.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (3 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (by norm_num)
  simp only [smul_eq_mul] at this
  rw [e _ (by norm_num), e _ (by norm_num), e _ (by norm_num)] at this
  nlinarith

/-- One count `k = 1` at `s = 1`, shape `a = 1`: `ℓ(1, b) = log b - 2 log (b + 1)`. -/
private lemma logMarginalLik_one_one {b : ℝ} (hb : 0 < b) :
    logMarginalLik 1 b (fun _ : Unit => (1 : ℝ)) (fun _ => 1) = log b - 2 * log (b + 1) := by
  rw [logMarginalLik_eq one_pos hb (fun _ => one_pos)]
  norm_num

/-- `2 ℓ(1, 5) < ℓ(1, 3) + ℓ(1, 7)` for one count `k = 1` at `s = 1`, because
`25 · 1024 < 21 · 1296`. -/
private lemma midpoint_fails :
    2 * logMarginalLik 1 5 (fun _ : Unit => (1 : ℝ)) (fun _ => 1) <
      logMarginalLik 1 3 (fun _ : Unit => (1 : ℝ)) (fun _ => 1) +
        logMarginalLik 1 7 (fun _ : Unit => (1 : ℝ)) (fun _ => 1) := by
  rw [logMarginalLik_one_one (by norm_num), logMarginalLik_one_one (by norm_num),
    logMarginalLik_one_one (by norm_num)]
  have h : ((5 : ℝ) ^ 2 * ((4 : ℝ) ^ 2 * (8 : ℝ) ^ 2)) < (3 * 7) * (6 : ℝ) ^ 4 := by norm_num
  have hl := log_lt_log (by positivity) h
  rw [log_mul (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num),
    log_mul (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num)] at hl
  simp only [log_pow] at hl
  norm_num at hl ⊢
  linarith

/-- **Not concave in the rate.** For one count `k = 1` at `s = 1` and shape `a = 1`,
`b ↦ ℓ(1, b)` is not concave on `(0, ∞)`; concavity holds in `log b`
(`strictConcaveOn_logMarginalLik_logRate`). -/
example : ¬ ConcaveOn ℝ (Set.Ioi 0)
    (fun b => logMarginalLik 1 b (fun _ : Unit => (1 : ℝ)) (fun _ => 1)) := by
  intro h
  have := h.2 (show (3 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (7 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at this
  norm_num at this
  linarith [midpoint_fails]

/-- **Not jointly concave, with a positive count.** The same sample shows that `ℓ` is not jointly
concave on data where the conditional rate MLE exists. -/
example : ¬ ConcaveOn ℝ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    (fun p : ℝ × ℝ => logMarginalLik p.1 p.2 (fun _ : Unit => (1 : ℝ)) (fun _ => 1)) := by
  intro h
  have := h.2 (show ((1 : ℝ), (3 : ℝ)) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) by norm_num)
    (show ((1 : ℝ), (7 : ℝ)) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hpt : ((1 / 2 : ℝ) • ((1 : ℝ), (3 : ℝ)) + (1 / 2 : ℝ) • ((1 : ℝ), (7 : ℝ))) =
      ((1 : ℝ), (5 : ℝ)) := by
    ext <;> simp <;> norm_num
  rw [hpt] at this
  simp only [smul_eq_mul] at this
  linarith [midpoint_fails]

/-- `rateScoreLog` at `b = 0` is `n a`, and the rate MLE at `a = 1` for the sample `(0, 2)` at
size factor `1` exists. -/
example : rateScoreLog 1 0 (fun _ : Fin 2 => (1 : ℝ)) (fun i => if i = 0 then 0 else 2) = 2 := by
  norm_num [rateScoreLog]

example : ∃ b, 0 < b ∧
    rateScore 1 b (fun _ : Fin 2 => (1 : ℝ)) (fun i => if i = 0 then 0 else 2) = 0 :=
  exists_rateScore_eq_zero one_pos (fun _ => one_pos) ⟨1, by simp⟩

/-- At a fixed rate a shape root exists for the sample `(0, 2)`. -/
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

/-- **The moment estimate does not solve the shape equation.** For `(0, 0, 3)` the moment shape
estimate `1` is not a root of the profile shape score: `11/6 - 3 log 2 < 0`, so the moment
estimates do not solve the shape score equation. -/
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

/-- Every root of the rate equation has the moment plug-in prior mean `M / σ`. -/
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

namespace TwoPoint

/-- The population profile shape score of the two-point law below, in closed form:
`(1/3) (1/a + 1/(a+1) + 1/(a+2)) - (log (a + 1) - log a)`. -/
noncomputable def q (a : ℝ) : ℝ :=
  (1 / 3) * (a⁻¹ + (a + 1)⁻¹ + (a + 2)⁻¹) - (log (a + 1) - log a)

private lemma hasDerivAt_q {a : ℝ} (ha : 0 < a) :
    HasDerivAt q ((1 / 3) * (-(a ^ 2)⁻¹ - ((a + 1) ^ 2)⁻¹ - ((a + 2) ^ 2)⁻¹) -
      ((a + 1)⁻¹ - a⁻¹)) a := by
  have h0 := hasDerivAt_inv ha.ne'
  have h1 := (hasDerivAt_inv (by positivity : a + 1 ≠ 0)).comp a ((hasDerivAt_id a).add_const 1)
  have h2 := (hasDerivAt_inv (by positivity : a + 2 ≠ 0)).comp a ((hasDerivAt_id a).add_const 2)
  have hl1 := ((hasDerivAt_id a).add_const (1 : ℝ)).log (by simp only [id]; positivity)
  have hl0 := (hasDerivAt_id a).log ha.ne'
  have := (((h0.add h1).add h2).const_mul (1 / 3)).sub (hl1.sub hl0)
  convert this using 1
  · funext x; simp [q, Function.comp_def]
  · simp only [id]; field_simp; ring

private lemma q_strictAnti : StrictAntiOn q (Set.Ioc 0 (1 / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 (1 / 2))
    (fun x hx => (hasDerivAt_q hx.1).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Ioc] at hx
  obtain ⟨hx0, hx1⟩ := hx
  rw [(hasDerivAt_q hx0).deriv]
  have key : -(1 / 3) * (x ^ 2)⁻¹ - ((x + 1)⁻¹ - x⁻¹) = (2 * x - 1) / (3 * x ^ 2 * (x + 1)) := by
    field_simp; ring
  have hneg : (2 * x - 1) / (3 * x ^ 2 * (x + 1)) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  have : 0 < ((x + 1) ^ 2)⁻¹ + ((x + 2) ^ 2)⁻¹ := by positivity
  nlinarith

private lemma q_pos : 0 < q (3 / 10) := by
  have hlog : log (3 / 10 + 1) - log (3 / 10) < 3 / 2 := by
    rw [← log_div (by norm_num) (by norm_num), log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have h3 : exp (3 / 2) ^ 2 = exp 1 ^ 3 := by
      rw [← exp_nat_mul, ← exp_nat_mul]; norm_num
    have : ((3 / 10 + 1) / (3 / 10) : ℝ) ^ 2 < exp (3 / 2) ^ 2 := by
      rw [h3]; nlinarith [pow_lt_pow_left₀ he (by norm_num) (three_ne_zero)]
    exact lt_of_pow_lt_pow_left₀ 2 (exp_pos _).le this
  unfold q; norm_num at hlog ⊢; linarith

private lemma q_neg : q (1 / 2) < 0 := by
  have h2 := Real.log_two_gt_d9
  have h32 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have hhalf : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, log_inv]
  unfold q
  rw [hhalf]
  norm_num at h32 ⊢
  linarith

/-- The two-point count law on `Bool`: `false ↦ 0` with probability `2/3`, `true ↦ 3` with `1/3`. -/
noncomputable def ν : Measure Bool :=
  (2 / 3 : ENNReal) • Measure.dirac false + (1 / 3 : ENNReal) • Measure.dirac true

instance : IsProbabilityMeasure ν := ⟨by
  simp only [ν, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same]; norm_num; exact ENNReal.div_self (by norm_num) (by norm_num)⟩

/-- The count read from one coordinate. -/
def g : Bool → ℕ := fun b => if b then 3 else 0

private lemma integral_ν (F : ℕ → ℝ) : ∫ b, F (g b) ∂ν = 2 / 3 * F 0 + 1 / 3 * F 3 := by
  rw [integral_fintype Integrable.of_finite]
  simp [ν, Measure.real, g, ENNReal.toReal_div]
  ring

/-- I.i.d. coordinates with law `ν`. -/
noncomputable abbrev μ : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => ν)

/-- The `i`-th count. -/
def X (i : ℕ) (ω : ℕ → Bool) : ℕ := g (ω i)

private lemma hg : Measurable g := measurable_of_finite g

private lemma hX (i : ℕ) : Measurable (X i) := hg.comp (measurable_pi_apply i)

private lemma integral_X (F : ℕ → ℝ) : ∫ ω, F (X 0 ω) ∂μ = 2 / 3 * F 0 + 1 / 3 * F 3 := by
  have hmp := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => ν) 0
  rw [← integral_ν, ← hmp.map_eq, integral_map (measurable_pi_apply 0).aemeasurable
    (Integrable.of_finite).aestronglyMeasurable]
  rfl

private lemma indep : Pairwise ((· ⟂ᵢ[μ] ·) on X) := fun _ _ hij =>
  (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => g) (fun _ => hg)).indepFun hij

private lemma ident (i : ℕ) : IdentDistrib (X i) (X 0) μ μ := by
  have h : ∀ j, MeasurePreserving (fun ω : ℕ → Bool => ω j) μ ν := fun j =>
    measurePreserving_eval_infinitePi (μ := fun _ : ℕ => ν) j
  exact (⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
    by rw [(h i).map_eq, (h 0).map_eq]⟩ : IdentDistrib (fun ω : ℕ → Bool => ω i)
      (fun ω => ω 0) μ μ).comp hg

private lemma integrable_X : Integrable (fun ω => (X 0 ω : ℝ)) μ := by
  refine (integrable_const (3 : ℝ)).mono' ((measurable_from_nat.comp (hX 0)).aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  simp only [X, g]; split_ifs <;> norm_num

private lemma mean_X : μ[fun ω => (X 0 ω : ℝ)] = 1 := by
  have := integral_X (fun k => (k : ℝ)); norm_num at this; exact this

private lemma pop_eq (a : ℝ) : popProfileShapeScore μ (X 0) a = q a := by
  rw [popProfileShapeScore, mean_X, integral_X (fun k => digammaIncrement a k)]
  simp [q, digammaIncrement, sum_range_succ]

private lemma exists_root : ∃ a₀ ∈ Set.Ioo (3 / 10 : ℝ) (1 / 2), q a₀ = 0 := by
  have hcont : ContinuousOn q (Set.Icc (3 / 10) (1 / 2)) := fun x hx =>
    (hasDerivAt_q (by linarith [hx.1] : (0 : ℝ) < x)).continuousAt.continuousWithinAt
  obtain ⟨a₀, ha, h⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨q_neg.le, q_pos.le⟩
  refine ⟨a₀, ⟨lt_of_le_of_ne ha.1 ?_, lt_of_le_of_ne ha.2 ?_⟩, h⟩
  · rintro rfl; linarith [q_pos]
  · rintro rfl; linarith [q_neg]

/-- **The joint-consistency theorem is non-vacuous.** For i.i.d. counts with the two-point law
(`0` w.p. `2/3`, `3` w.p. `1/3`, mean `1`) at `σ = 1` and `b₀ = a₀`, the population profile shape
score `q` is strictly decreasing on `(0, 1/2]`, positive at `3/10` and negative at `1/2`; its root
`a₀` (irrational, from the intermediate value theorem) satisfies every hypothesis of
`ae_eventually_exists_score_root`. The law is not negative binomial. -/
example : ∃ a₀ ∈ Set.Ioo (3 / 10 : ℝ) (1 / 2), ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ n in atTop,
    ∃ a b, 0 < a ∧ 0 < b ∧ |a - a₀| < ε ∧ |b - a₀| < ε ∧
      shapeScore a b (fun _ : Fin n => (1 : ℝ)) (fun i => X i ω) = 0 ∧
      rateScore a b (fun _ : Fin n => (1 : ℝ)) (fun i => X i ω) = 0 := by
  obtain ⟨a₀, ⟨ha₁, ha₂⟩, hq⟩ := exists_root
  have ha₀ : 0 < a₀ := by linarith
  refine ⟨a₀, ⟨ha₁, ha₂⟩, ae_eventually_exists_score_root ha₀ ha₀ one_pos (hX 0) indep ident
    integrable_X (by rw [mean_X]; field_simp) ?_⟩
  have hu : (0 : ℝ) < min a₀ (1 / 2 - a₀) := lt_min ha₀ (by linarith)
  refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨_, hu, fun ε hε => ?_⟩
  obtain ⟨hε0, hεu⟩ := hε
  have h1 := lt_of_lt_of_le hεu (min_le_left _ _)
  have h2 := lt_of_lt_of_le hεu (min_le_right _ _)
  simp only [Set.mem_ofPred_eq, pop_eq]
  constructor
  · rw [← hq]
    exact q_strictAnti ⟨by linarith, by linarith⟩ ⟨ha₀, ha₂.le⟩ (by linarith)
  · rw [← hq]
    exact q_strictAnti ⟨ha₀, ha₂.le⟩ ⟨by linarith, by linarith⟩ (by linarith)

end TwoPoint

end MathlibExtTest.Biology.Omics.HierarchicalCountMLE
