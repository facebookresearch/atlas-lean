/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conditional likelihood for matched case-control sets

In a matched set of `M + 1` subjects with exposures `x_0, …, x_M ∈ ℝ^K`, suppose the outcomes are
independent with `P(y_j = 1) = expit(α + β · x_j)`, where the intercept `α` is specific to the
set. Given that the set contains exactly one case, the probability that the case is subject `j`
is `exp(β · x_j) / ∑_i exp(β · x_i)`, free of `α`. With the case listed first, the conditional
likelihood of `n` sets is `∏ exp(β · x_0) / ∑_j exp(β · x_j)`, equivalently
`∏ 1 / (1 + ∑_{j ≥ 1} exp(β · (x_j - x_0)))` (Breslow and Day 1980, (7.2), (7.3)); a variable
taking the same value within each set (a matching variable) drops out.

For 1:1 matching on a binary exposure, let `n₁₀` pairs have the case exposed and the control not,
and `n₀₁` the reverse. The conditional likelihood is maximized at `ψ = exp β = n₁₀ / n₀₁`. By
contrast, maximizing the likelihood jointly over `β` and a separate intercept for every pair (the
incidental-parameter likelihood) gives `ψ = (n₁₀ / n₀₁)²`, which overstates the odds ratio; this is
the bias that conditioning removes (Breslow and Day 1980, p. 250). Concordant pairs carry no
information about `β`.

Sources: N. E. Breslow and N. E. Day, *Statistical Methods in Cancer Research, Vol. I: The
Analysis of Case-Control Studies*, IARC Sci. Publ. 32 (1980), ch. 7, pp. 249–253.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.ConditionalLogisticMatchedSetsWanted

/-- The logistic function `expit t = 1 / (1 + exp (-t))`. -/
noncomputable def expit (t : ℝ) : ℝ :=
  1 / (1 + Real.exp (-t))

/-- The probability that subject `j` of a matched set is the only case, when outcomes are
independent with `P(y_i = 1) = expit(α + β · x_i)`:
`expit(α + β · x_j) ∏_{i ≠ j} (1 - expit(α + β · x_i))`. -/
noncomputable def onlyCaseProb {M K : ℕ} (α : ℝ) (β : Fin K → ℝ) (x : Fin (M + 1) → Fin K → ℝ)
    (j : Fin (M + 1)) : ℝ :=
  expit (α + β ⬝ᵥ x j) * ∏ i ∈ Finset.univ.erase j, (1 - expit (α + β ⬝ᵥ x i))

/-- The conditional probability that subject `j` is the case, given exactly one case in the set.
-/
noncomputable def conditionalCaseProb {M K : ℕ} (α : ℝ) (β : Fin K → ℝ)
    (x : Fin (M + 1) → Fin K → ℝ) (j : Fin (M + 1)) : ℝ :=
  onlyCaseProb α β x j / ∑ i, onlyCaseProb α β x i

/-- **The conditional probability is free of the intercept** (Breslow and Day 1980, ch. 7). For
a matched set of `M + 1` subjects with exposures `x_i ∈ ℝ^K`, independent outcomes with
`P(y_i = 1) = expit(α + β · x_i)`, every intercept `α ∈ ℝ` and coefficient vector `β`, the
probability that subject `j` is the case given exactly one case is
`exp(β · x_j) / ∑_i exp(β · x_i)`.

Source: Breslow and Day (1980), p. 251. -/
public theorem_wanted conditionalCaseProb_eq {M K : ℕ} (α : ℝ) (β : Fin K → ℝ)
    (x : Fin (M + 1) → Fin K → ℝ) (j : Fin (M + 1)) :
    conditionalCaseProb α β x j = Real.exp (β ⬝ᵥ x j) / ∑ i, Real.exp (β ⬝ᵥ x i)

/-- **The two forms of the conditional likelihood** (Breslow and Day 1980, (7.2), (7.3)). For `n`
matched sets, set `s` having `M_s + 1` subjects with exposures `x_{s,j} ∈ ℝ^K` and its case
listed first (`j = 0`), and every coefficient vector `β`,
`∏_s exp(β · x_{s,0}) / ∑_j exp(β · x_{s,j})` equals
`∏_s 1 / (1 + ∑_{j ≥ 1} exp(β · (x_{s,j} - x_{s,0})))`.
For `M_s = 1` this is (7.3).

Source: Breslow and Day (1980), p. 251, (7.2), and p. 253, (7.3). -/
public theorem_wanted prod_conditionalLikelihood_eq {n K : ℕ} (M : Fin n → ℕ) (β : Fin K → ℝ)
    (x : (s : Fin n) → Fin (M s + 1) → Fin K → ℝ) :
    ∏ s, Real.exp (β ⬝ᵥ x s 0) / ∑ j, Real.exp (β ⬝ᵥ x s j) =
      ∏ s, 1 / (1 + ∑ j : Fin (M s), Real.exp (β ⬝ᵥ (x s j.succ - x s 0)))

/-- **Matching variables drop out** (Breslow and Day 1980, p. 251). For a matched set of `M + 1`
subjects with exposures `x_i ∈ ℝ^K`, independent outcomes with `P(y_i = 1) = expit(α + β · x_i)`,
every intercept `α`, coefficient vector `β` and vector `z ∈ ℝ^K` common to the whole set, the
conditional probability that subject `j` is the case given exactly one case is unchanged when
every exposure `x_i` is replaced by `x_i + z`.

Source: Breslow and Day (1980), p. 251. -/
public theorem_wanted conditionalCaseProb_add_const {M K : ℕ} (α : ℝ) (β : Fin K → ℝ)
    (x : Fin (M + 1) → Fin K → ℝ) (z : Fin K → ℝ) (j : Fin (M + 1)) :
    conditionalCaseProb α β (fun i => x i + z) j = conditionalCaseProb α β x j

/-- The 1:1 binary-exposure conditional log-likelihood
`n₁₀ log (e^β / (1 + e^β)) + n₀₁ log (1 / (1 + e^β))`, from `n₁₀` pairs with the case exposed and
the control unexposed and `n₀₁` pairs with the reverse. -/
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

/-- The incidental-parameter log-likelihood of the discordant pairs, with a separate nuisance
intercept for every pair (not a valid estimating likelihood for `β`): a pair
with the case exposed and the control unexposed contributes
`log (expit(α + β) (1 - expit α))`, and a pair with the reverse contributes
`log (expit α (1 - expit(α + β)))`. -/
noncomputable def perPairInterceptLogLik {n₁₀ n₀₁ : ℕ} (α₁₀ : Fin n₁₀ → ℝ)
    (α₀₁ : Fin n₀₁ → ℝ) (β : ℝ) : ℝ :=
  (∑ i, Real.log (expit (α₁₀ i + β) * (1 - expit (α₁₀ i)))) +
    ∑ i, Real.log (expit (α₀₁ i) * (1 - expit (α₀₁ i + β)))

/-- **The incidental-parameter estimate is biased** (Breslow and Day 1980, p. 250). For `n₁₀ > 0`
discordant pairs with the case exposed and `n₀₁ > 0` with the control exposed, let
`β̂ = 2 log (n₁₀ / n₀₁)`, so that `e^β̂ = (n₁₀ / n₀₁)²`. Then the incidental-parameter
log-likelihood, with a separate intercept for every pair, is maximized at `β = β̂` with every
intercept equal to `-β̂ / 2`: for all intercepts `α₁₀, α₀₁` and every `β`, its value is at most the
value at that point. The maximizing odds ratio is the square of the conditional estimate
`n₁₀ / n₀₁` of `pairedConditionalLogLik_max`, which shows the bias of estimating `β` jointly with
one nuisance intercept per pair.

Source: Breslow and Day (1980), p. 250. -/
public theorem_wanted perPairInterceptLogLik_le {n₁₀ n₀₁ : ℕ} (h₁₀ : 0 < n₁₀) (h₀₁ : 0 < n₀₁)
    (α₁₀ : Fin n₁₀ → ℝ) (α₀₁ : Fin n₀₁ → ℝ) (β : ℝ) :
    perPairInterceptLogLik α₁₀ α₀₁ β ≤
      perPairInterceptLogLik (fun _ : Fin n₁₀ => -Real.log (n₁₀ / n₀₁))
        (fun _ : Fin n₀₁ => -Real.log (n₁₀ / n₀₁)) (2 * Real.log (n₁₀ / n₀₁))

end WantedExt.Biology.StatisticalGenetics.ConditionalLogisticMatchedSetsWanted
