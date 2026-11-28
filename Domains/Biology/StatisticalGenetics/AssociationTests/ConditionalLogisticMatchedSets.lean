/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional case probabilities in matched sets

Given exactly one case in a matched set, the case probabilities are independent of the
intercept and invariant under a common additive shift of all subjects' exposure vectors.

For independent 1:1 pairs with binary exposure and independent outcomes within each pair,
if both discordant counts `n₁₀` and `n₀₁` are positive, the unconditional log-likelihood of
these discordant pairs is maximized at slope `2 log (n₁₀ / n₀₁)` with each pair's own
intercept equal to minus half that slope. In the source, concordant pairs do not affect the
maximizing slope because their contributions can be maximized separately at any slope.

## References

* N. E. Breslow and N. E. Day, *Statistical Methods in Cancer Research Volume I: The Analysis
  of Case-Control Studies*, IARC Scientific Publications No. 32, Lyon (1980), ch. 7, §§7.1–7.2,
  pp. 249–251. The unconditional maximizer is on p. 250.
* E. B. Andersen, *Conditional Inference and Models for Measuring*, Mentalhygiejnisk Forlag,
  København (1973), p. 69, credited by Breslow and Day for the squared discordant-pair ratio.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.ConditionalLogisticMatchedSetsWanted

/-- The probability that subject `j` of a matched set is the only case, when outcomes are
independent with `P(y_i = 1) = σ(α + β · x_i)`:
`σ(α + β · x_j) ∏_{i ≠ j} (1 - σ(α + β · x_i))`. Here `σ` is the logistic
function `Real.sigmoid`. -/
noncomputable def onlyCaseProb {M K : ℕ} (α : ℝ) (β : Fin K → ℝ) (x : Fin (M + 1) → Fin K → ℝ)
    (j : Fin (M + 1)) : ℝ :=
  Real.sigmoid (α + β ⬝ᵥ x j) * ∏ i ∈ Finset.univ.erase j, (1 - Real.sigmoid (α + β ⬝ᵥ x i))

/-- The conditional probability that subject `j` is the case, given exactly one case in the set. The
denominator is always positive (every factor lies in `(0, 1)`), so no division by zero occurs. -/
noncomputable def conditionalCaseProb {M K : ℕ} (α : ℝ) (β : Fin K → ℝ)
    (x : Fin (M + 1) → Fin K → ℝ) (j : Fin (M + 1)) : ℝ :=
  onlyCaseProb α β x j / ∑ i, onlyCaseProb α β x i

/-- **The conditional probability is free of the intercept** (Breslow and Day 1980, ch. 7). For
a matched set of `M + 1` subjects with exposures `x_i ∈ ℝ^K`, independent outcomes with
`P(y_i = 1) = σ(α + β · x_i)`, every intercept `α ∈ ℝ` and coefficient vector `β`, the
probability that subject `j` is the case given exactly one case is
`exp(β · x_j) / ∑_i exp(β · x_i)`.
Here `σ` is the logistic function `Real.sigmoid`.

Source: Breslow and Day (1980), p. 251. -/
public theorem conditionalCaseProb_eq {M K : ℕ} (α : ℝ) (β : Fin K → ℝ)
    (x : Fin (M + 1) → Fin K → ℝ) (j : Fin (M + 1)) :
    conditionalCaseProb α β x j = Real.exp (β ⬝ᵥ x j) / ∑ i, Real.exp (β ⬝ᵥ x i) := by
  -- `σ t = e^t (1 - σ t)`, so each `onlyCaseProb` is `e^(β · x_i)` times one positive constant.
  have hσ (t : ℝ) : Real.sigmoid t = Real.exp t * (1 - Real.sigmoid t) := by
    have h := Real.sigmoid_mul_rexp_neg (-t)
    rw [neg_neg, Real.sigmoid_neg] at h
    rw [mul_comm]
    exact h.symm
  set c := Real.exp α * ∏ k, (1 - Real.sigmoid (α + β ⬝ᵥ x k)) with hc
  have hc0 : 0 < c :=
    mul_pos (Real.exp_pos _) (Finset.prod_pos fun k _ => sub_pos.mpr (Real.sigmoid_lt_one _))
  have honly (i : Fin (M + 1)) : onlyCaseProb α β x i = Real.exp (β ⬝ᵥ x i) * c := by
    rw [onlyCaseProb, hσ (α + β ⬝ᵥ x i), mul_assoc,
      Finset.mul_prod_erase Finset.univ (fun k => 1 - Real.sigmoid (α + β ⬝ᵥ x k))
        (Finset.mem_univ i), Real.exp_add, hc]
    ring
  simp_rw [conditionalCaseProb, honly, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ hc0.ne'

/-- **Matching variables drop out** (Breslow and Day 1980, p. 251). For a matched set of `M + 1`
subjects with exposures `x_i ∈ ℝ^K`, independent outcomes with `P(y_i = 1) = σ(α + β · x_i)`,
every intercept `α`, coefficient vector `β` and vector `z ∈ ℝ^K` common to the whole set, the
conditional probability that subject `j` is the case given exactly one case is unchanged when
every exposure `x_i` is replaced by `x_i + z`.
Here `σ` is the logistic function `Real.sigmoid`.

Source: Breslow and Day (1980), p. 251. -/
public theorem conditionalCaseProb_add_const {M K : ℕ} (α : ℝ) (β : Fin K → ℝ)
    (x : Fin (M + 1) → Fin K → ℝ) (z : Fin K → ℝ) (j : Fin (M + 1)) :
    conditionalCaseProb α β (fun i => x i + z) j = conditionalCaseProb α β x j := by
  simp_rw [conditionalCaseProb_eq, dotProduct_add, Real.exp_add, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ (Real.exp_pos (β ⬝ᵥ z)).ne'

/-- **Incidental-parameter log-likelihood of independent pairs.** The log-likelihood of the
discordant pairs, with a separate nuisance intercept for every pair (not a valid estimating
likelihood for `β`): a pair with the case exposed and the control unexposed contributes
`log (σ(α + β) (1 - σ α))`, and a pair with the reverse contributes `log (σ α (1 - σ(α + β)))`.
Each term takes the two subjects of a pair to be independent, and the sum is the joint
log-likelihood when the pairs are independent of one another. Here `σ` is the logistic function
`Real.sigmoid`. -/
noncomputable def perPairInterceptLogLik {n₁₀ n₀₁ : ℕ} (α₁₀ : Fin n₁₀ → ℝ)
    (α₀₁ : Fin n₀₁ → ℝ) (β : ℝ) : ℝ :=
  (∑ i, Real.log (Real.sigmoid (α₁₀ i + β) * (1 - Real.sigmoid (α₁₀ i)))) +
    ∑ i, Real.log (Real.sigmoid (α₀₁ i) * (1 - Real.sigmoid (α₀₁ i + β)))

/-- **Log-likelihood with an intercept constant within each discordant pair type.** If all pairs of
one type share an intercept, the corresponding log-probability is weighted by that type's count.
The intercepts `a₁₀` and `a₀₁` may differ. -/
public theorem perPairInterceptLogLik_const (n₁₀ n₀₁ : ℕ) (a₁₀ a₀₁ β : ℝ) :
    perPairInterceptLogLik (fun _ : Fin n₁₀ => a₁₀) (fun _ : Fin n₀₁ => a₀₁) β =
      n₁₀ * Real.log (Real.sigmoid (a₁₀ + β) * (1 - Real.sigmoid a₁₀)) +
        n₀₁ * Real.log (Real.sigmoid a₀₁ * (1 - Real.sigmoid (a₀₁ + β))) := by
  simp only [perPairInterceptLogLik, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

private theorem log_sigmoid_mul_le_midpoint (x y : ℝ) :
    Real.log (Real.sigmoid x * Real.sigmoid y) ≤ 2 * Real.log (Real.sigmoid ((x + y) / 2)) := by
  let a := Real.exp (-((x + y) / 2))
  let b := Real.exp (-x)
  let c := Real.exp (-y)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hc : 0 < c := Real.exp_pos _
  have hsq : a ^ 2 = b * c := by
    dsimp only [a, b, c]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hmean := two_mul_le_add_of_sq_le_mul hb.le hc.le hsq.le
  have hdenom : (1 + a) * (1 + a) ≤ (1 + b) * (1 + c) := by
    nlinarith only [hmean, hsq]
  rw [two_mul, ← Real.log_mul (Real.sigmoid_pos _).ne' (Real.sigmoid_pos _).ne']
  simp only [Real.sigmoid_def, ← mul_inv]
  exact Real.log_le_log (by positivity) (inv_anti₀ (by positivity) hdenom)

/-- **Maximizer of the incidental-parameter log-likelihood** (Breslow and Day 1980, p. 250). For
`n₁₀ > 0` discordant pairs with the case exposed and `n₀₁ > 0` with the control exposed, let
`β̂ = 2 log (n₁₀ / n₀₁)`, so that `e^β̂ = (n₁₀ / n₀₁)²`. Then the incidental-parameter
log-likelihood, with a separate intercept for every pair, is maximized at `β = β̂` with every
intercept equal to `-β̂ / 2`: for all intercepts `α₁₀, α₀₁` and every `β`, its value is at most
the value at that point. Thus the maximizing odds ratio `(n₁₀ / n₀₁)²` is the square of the
conditional estimate `n₁₀ / n₀₁` of `pairedConditionalLogLik_max` (moving any positive estimate
`≠ 1` farther from `1`; this algebraic identity for the maximizer does not by itself state a
statistical expectation/bias theorem).

Source: Breslow and Day (1980), p. 250. -/
public theorem perPairInterceptLogLik_le {n₁₀ n₀₁ : ℕ} (h₁₀ : 0 < n₁₀) (h₀₁ : 0 < n₀₁)
    (α₁₀ : Fin n₁₀ → ℝ) (α₀₁ : Fin n₀₁ → ℝ) (β : ℝ) :
    perPairInterceptLogLik α₁₀ α₀₁ β ≤
      perPairInterceptLogLik (fun _ : Fin n₁₀ => -Real.log (n₁₀ / n₀₁))
        (fun _ : Fin n₀₁ => -Real.log (n₁₀ / n₀₁)) (2 * Real.log (n₁₀ / n₀₁)) := by
  let a : ℝ := n₁₀
  let b : ℝ := n₀₁
  let s := Real.log (a / b)
  let p := Real.sigmoid (β / 2)
  have ha : 0 < a := Nat.cast_pos.mpr h₁₀
  have hb : 0 < b := Nat.cast_pos.mpr h₀₁
  have hab : 0 < a + b := add_pos ha hb
  -- For a fixed slope, each pair's two logit arguments have a fixed midpoint.
  have hprofile : perPairInterceptLogLik α₁₀ α₀₁ β ≤
      a * (2 * Real.log p) + b * (2 * Real.log (1 - p)) := by
    calc
      _ ≤ (∑ _ : Fin n₁₀, 2 * Real.log p) + (∑ _ : Fin n₀₁, 2 * Real.log (1 - p)) := by
        simp only [perPairInterceptLogLik, p, ← Real.sigmoid_neg]
        apply add_le_add <;> apply Finset.sum_le_sum
        · intro i _
          simpa only [show (α₁₀ i + β + -α₁₀ i) / 2 = β / 2 by ring] using
            log_sigmoid_mul_le_midpoint (α₁₀ i + β) (-α₁₀ i)
        · intro i _
          simpa only [show (α₀₁ i + -(α₀₁ i + β)) / 2 = -(β / 2) by ring] using
            log_sigmoid_mul_le_midpoint (α₀₁ i) (-(α₀₁ i + β))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, a, b]
  -- Apply the logarithm's tangent bound at each fitted frequency. The linear errors cancel.
  have hterm (w z : ℝ) (hw : 0 < w) (hz : 0 < z) :
      w * Real.log z ≤ w * Real.log (w / (a + b)) + ((a + b) * z - w) := by
    have hq := div_pos hw hab
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hz hq)) hw.le
    rw [Real.log_div hz.ne' hq.ne'] at h
    have halg : w * (z / (w / (a + b)) - 1) = (a + b) * z - w := by
      field_simp
    rw [halg] at h
    linarith only [h]
  have hweighted : a * Real.log p + b * Real.log (1 - p) ≤
      a * Real.log (a / (a + b)) + b * Real.log (b / (a + b)) := by
    calc
      _ ≤ (a * Real.log (a / (a + b)) + ((a + b) * p - a)) +
          (b * Real.log (b / (a + b)) + ((a + b) * (1 - p) - b)) :=
        add_le_add (hterm a p ha (Real.sigmoid_pos _))
          (hterm b (1 - p) hb (sub_pos.mpr (Real.sigmoid_lt_one _)))
      _ = _ := by ring
  have hσ₀₁ : Real.sigmoid (-s) = b / (a + b) := by
    dsimp only [s]
    rw [Real.sigmoid_def, neg_neg, Real.exp_log (div_pos ha hb)]
    field_simp
    ring
  have hσ₁₀ : Real.sigmoid s = a / (a + b) := by
    rw [← sub_sub_cancel 1 (Real.sigmoid s), ← Real.sigmoid_neg, hσ₀₁]
    field_simp
    ring
  refine hprofile.trans ?_
  calc
    _ ≤ 2 * (a * Real.log (a / (a + b)) + b * Real.log (b / (a + b))) := by
      linarith only [hweighted]
    _ = perPairInterceptLogLik (fun _ : Fin n₁₀ => -s) (fun _ : Fin n₀₁ => -s) (2 * s) := by
      rw [← hσ₁₀, ← hσ₀₁, perPairInterceptLogLik_const]
      simp only [show -s + 2 * s = s by ring, ← Real.sigmoid_neg, neg_neg,
        Real.log_mul (Real.sigmoid_pos _).ne' (Real.sigmoid_pos _).ne']
      ring

end WantedExt.Biology.StatisticalGenetics.ConditionalLogisticMatchedSetsWanted
