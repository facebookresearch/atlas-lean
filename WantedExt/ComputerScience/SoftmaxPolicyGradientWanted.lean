/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Policy gradients for softmax policies

Sources:
A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, "On the Theory of Policy Gradient Methods:
Optimality, Approximation, and Distribution Shift", arXiv:1908.00261v5, equation (11) and
Theorem 5.1 (equation (11) and Theorem 10 in the JMLR version, JMLR 22(98) (2021)); A. Agarwal,
N. Jiang, S. M. Kakade, W. Sun, "Reinforcement Learning: Theory and Algorithms",
https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Theorem 12.3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.MDP.SoftmaxPolicyGradient

@[expose] public section

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

/-!
# Policy gradients for softmax policies

For a finite discounted MDP and the softmax policies `π_θ` of `CSLibExt/Algorithms/Lean/MDP/
NaturalPolicyGradient.lean`, the objective `θ ↦ V^{π_θ}(μ) = ∑ s₀, μ s₀ V^{π_θ}(s₀)` has partial
derivatives `∂V^{π_θ}(μ)/∂θ(s, a) = (1 - γ)⁻¹ d^{π_θ}_μ(s) π_θ(a | s) A^{π_θ}(s, a)` (the policy
gradient theorem for softmax policies, `hasDerivAt_softmaxObjective`, proved in
`CSLibExt/Algorithms/Lean/MDP/SoftmaxPolicyGradient.lean`). Gradient ascent on it with step size
`η ≤ (1 - γ)³ / 8` and a start distribution charging every state converges to the optimal value,
without a rate. The natural-gradient variant, with its dimension-free rate, is proved in
`NaturalPolicyGradient.lean` (`optimalValue_sub_stochValue_npgPolicy_le`).
-/

open StochasticPolicy

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] [DecidableEq A]
  {M : MDP S A ℝ} {γ : ℝ}

/-- Gradient ascent on the softmax objective from `θ_0 = 0`, with step size `η`:
`θ_{t+1} = θ_t + η ∇_θ V^{π_{θ_t}}(μ)`, the gradient written in the closed form of
`hasDerivAt_softmaxObjective` (AKLM equation (11); AJKS Chapter 12, equation (0.2)). -/
noncomputable def softmaxPGLogits (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ)
    (η : ℝ) : ℕ → S → A → ℝ
  | 0 => 0
  | t + 1 => fun s a => softmaxPGLogits hM hγ0 hγ1 μ η t s a +
      η * softmaxPolicyGradient hM hγ0 hγ1 μ (softmaxPGLogits hM hγ0 hγ1 μ η t) s a

/-- **Global convergence of softmax policy gradient** (AKLM Theorem 5.1; AJKS Theorem 12.3): for
rewards in `[0, 1]`, a start distribution `μ` charging every state and a step size
`0 < η ≤ (1 - γ)³ / 8`, the values of the gradient-ascent iterates converge to the optimal
value in every state. The iterates start from `θ_0 = 0`, a special case: the source fixes no
initialization. -/
public theorem_wanted tendsto_stochValue_softmaxPGLogits (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hr : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1) (μ : S → ℝ)
    (hμ : ∀ s, 0 < μ s) (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ (1 - γ) ^ 3 / 8) (s : S) :
    Filter.Tendsto (fun t => stochValue M γ hM hγ0 hγ1
        (softmax (softmaxPGLogits hM hγ0 hγ1 μ η t)) s) Filter.atTop
      (nhds (optimalValue M γ hM hγ0 hγ1 s))

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
