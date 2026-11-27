/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conditional likelihood for matched case-control sets

In a matched set of `M + 1` subjects with exposures `x_0, …, x_M ∈ ℝ^K`, suppose the outcomes are
independent with `P(y_j = 1) = σ(α + β · x_j)`, where the intercept `α` is specific to the
set. Given that the set contains exactly one case, the probability that the case is subject `j`
is `exp(β · x_j) / ∑_i exp(β · x_i)`, free of `α`. If the outcomes are also independent across
sets, the conditional likelihood of `n` sets, each with its case listed first, is the product
`∏ exp(β · x_0) / ∑_j exp(β · x_j)`, equivalently `∏ 1 / (1 + ∑_{j ≥ 1} exp(β · (x_j - x_0)))`
(Breslow and Day 1980, (7.2), (7.3)). The two products agree as an algebraic identity; reading
them as a joint likelihood needs that independence across sets, which independence within each
set does not give. A variable taking the same value within each set (a matching variable) drops
out.

For 1:1 matching on a binary exposure, let `n₁₀` pairs have the case exposed and the control not,
and `n₀₁` the reverse, with the pairs independent of one another. The conditional likelihood is
maximized at `ψ = exp β = n₁₀ / n₀₁`. By contrast, maximizing the likelihood jointly over `β` and
a separate intercept for every pair (the incidental-parameter likelihood) yields
`β̂ = 2 log (n₁₀ / n₀₁)`, i.e. `ψ̂ = (n₁₀ / n₀₁)²` — the square of the conditional estimate (for
any positive estimate `≠ 1`, squaring moves it farther from `1`, e.g. `1/2 ↦ 1/4` and `2 ↦ 4`;
Breslow and Day 1980, p. 250). Concordant pairs carry no information about `β`.

Here `σ t = 1 / (1 + exp (-t))` is the logistic function, Mathlib's `Real.sigmoid`.

Sources: N. E. Breslow and N. E. Day, *Statistical Methods in Cancer Research, Vol. I: The
Analysis of Case-Control Studies*, IARC Sci. Publ. 32 (1980), ch. 7, pp. 249–253.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul

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

/-- **Two forms of the conditional likelihood of independent matched sets.** For `n` matched
sets, set `s` having `M_s + 1` subjects with exposures `x_{s,j} ∈ ℝ^K` and its case listed first
(`j = 0`), and every coefficient vector `β`, `∏_s exp(β · x_{s,0}) / ∑_j exp(β · x_{s,j})` equals
`∏_s 1 / (1 + ∑_{j ≥ 1} exp(β · (x_{s,j} - x_{s,0})))` (Breslow and Day 1980, (7.2), (7.3)); for
`M_s = 1` this is (7.3). The identity is algebraic. Each factor of the first product is the
conditional probability that the case of set `s` is subject `0` (`conditionalCaseProb_eq`), and the
product is the joint conditional likelihood of the `n` sets only when the outcomes are independent
across sets as well as within each set: independence within each set does not justify
multiplying probabilities across sets.

Source: Breslow and Day (1980), p. 251, (7.2), and p. 253, (7.3). -/
public theorem_wanted prod_conditionalLikelihood_eq {n K : ℕ} (M : Fin n → ℕ) (β : Fin K → ℝ)
    (x : (s : Fin n) → Fin (M s + 1) → Fin K → ℝ) :
    ∏ s, Real.exp (β ⬝ᵥ x s 0) / ∑ j, Real.exp (β ⬝ᵥ x s j) =
      ∏ s, 1 / (1 + ∑ j : Fin (M s), Real.exp (β ⬝ᵥ (x s j.succ - x s 0)))

/-- **Matching variables drop out** (Breslow and Day 1980, p. 251). For a matched set of `M + 1`
subjects with exposures `x_i ∈ ℝ^K`, independent outcomes with `P(y_i = 1) = σ(α + β · x_i)`,
every intercept `α`, coefficient vector `β` and vector `z ∈ ℝ^K` common to the whole set, the
conditional probability that subject `j` is the case given exactly one case is unchanged when
every exposure `x_i` is replaced by `x_i + z`.
Here `σ` is the logistic function `Real.sigmoid`.

Source: Breslow and Day (1980), p. 251. -/
public theorem_wanted conditionalCaseProb_add_const {M K : ℕ} (α : ℝ) (β : Fin K → ℝ)
    (x : Fin (M + 1) → Fin K → ℝ) (z : Fin K → ℝ) (j : Fin (M + 1)) :
    conditionalCaseProb α β (fun i => x i + z) j = conditionalCaseProb α β x j

/-- **Conditional log-likelihood of independent 1:1 pairs.** For `n₁₀` pairs with the case
exposed and the control unexposed and `n₀₁` pairs with the reverse, the binary-exposure conditional
log-likelihood `n₁₀ log (e^β / (1 + e^β)) + n₀₁ log (1 / (1 + e^β))`. Each pair contributes the log
of its conditional probability given one case in the pair, and the sum is the joint conditional
log-likelihood when the pairs are independent of one another. The denominators `1 + e^β` are
always positive, so no division by zero occurs. -/
noncomputable def pairedConditionalLogLik (n₁₀ n₀₁ : ℕ) (β : ℝ) : ℝ :=
  n₁₀ * Real.log (Real.exp β / (1 + Real.exp β)) + n₀₁ * Real.log (1 / (1 + Real.exp β))

/-- **Conditional MLE for 1:1 matching** (Breslow and Day 1980, p. 250). For `n₁₀ > 0` discordant
pairs with the case exposed and `n₀₁ > 0` with the control exposed, the conditional
log-likelihood is maximized exactly at `β = log (n₁₀ / n₀₁)`, that is `ψ = e^β = n₁₀ / n₀₁`: its
value there is at least its value at every `β`, with equality only at that point.

Source: Breslow and Day (1980), p. 250. -/
public theorem_wanted pairedConditionalLogLik_max {n₁₀ n₀₁ : ℕ} (h₁₀ : 0 < n₁₀) (h₀₁ : 0 < n₀₁)
    (β : ℝ) :
    pairedConditionalLogLik n₁₀ n₀₁ β ≤
        pairedConditionalLogLik n₁₀ n₀₁ (Real.log (n₁₀ / n₀₁)) ∧
      (pairedConditionalLogLik n₁₀ n₀₁ β =
          pairedConditionalLogLik n₁₀ n₀₁ (Real.log (n₁₀ / n₀₁)) ↔
        β = Real.log (n₁₀ / n₀₁))

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
public theorem_wanted perPairInterceptLogLik_le {n₁₀ n₀₁ : ℕ} (h₁₀ : 0 < n₁₀) (h₀₁ : 0 < n₀₁)
    (α₁₀ : Fin n₁₀ → ℝ) (α₀₁ : Fin n₀₁ → ℝ) (β : ℝ) :
    perPairInterceptLogLik α₁₀ α₀₁ β ≤
      perPairInterceptLogLik (fun _ : Fin n₁₀ => -Real.log (n₁₀ / n₀₁))
        (fun _ : Fin n₀₁ => -Real.log (n₁₀ / n₀₁)) (2 * Real.log (n₁₀ / n₀₁))

end WantedExt.Biology.StatisticalGenetics.ConditionalLogisticMatchedSetsWanted
