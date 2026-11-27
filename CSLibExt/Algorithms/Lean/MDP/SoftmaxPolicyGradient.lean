/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.NaturalPolicyGradient
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The policy gradient theorem for softmax policies

For a finite stochastic MDP with discount `0 ≤ γ < 1`, a vector `μ : S → ℝ` of initial weights
and the softmax policies `π_θ(a | s) = exp θ(s, a) / ∑ b, exp θ(s, b)` of
`CSLibExt.Algorithms.Lean.MDP.NaturalPolicyGradient`, the objective is
`V^{π_θ}(μ) = ∑ s₀, μ s₀ V^{π_θ}(s₀)` (`softmaxObjective`).

`hasDerivAt_softmaxObjective`: **the policy gradient theorem for softmax policies** (Agarwal,
Kakade, Lee and Mahajan, *On the Theory of Policy Gradient Methods*, arXiv:1908.00261v5,
equation (10) and Lemma C.1, which are equation (10) and Lemma 40 in the JMLR version; Agarwal,
Jiang, Kakade and Sun, *Reinforcement Learning: Theory and Algorithms*, Lemma 12.2): the partial
derivative of `θ ↦ V^{π_θ}(μ)` in the coordinate `θ(s, a)` is
`(1 - γ)⁻¹ d^{π_θ}_μ(s) π_θ(a | s) A^{π_θ}(s, a)` (`softmaxPolicyGradient`), where
`d^{π_θ}_μ(s) = ∑ s₀, μ s₀ d^{π_θ}_{s₀}(s)` and `A^{π_θ}` is the advantage function.

## Proof outline

Let `θ_x` be the logits `θ` with the coordinate `θ(s, a)` replaced by `x`, so that `θ_x = θ` at
`x = θ(s, a)`, and write `π_x = π_{θ_x}`, `π = π_θ`.

* The performance difference lemma (`performance_difference_initial`) gives
  `V^{π_x}(μ) - V^π(μ) = (1 - γ)⁻¹ ∑ s', d^{π_x}_μ(s') ∑ b, π_x(b | s') A^π(s', b)`. The policies
  `π_x` and `π` agree outside `s`, where `∑ b, π(b | s') A^π(s', b) = 0`, so only the term
  `s' = s` remains: `V^{π_x}(μ) - V^π(μ) = g(x) h(x)` with
  `g(x) = (1 - γ)⁻¹ d^{π_x}_μ(s)` and `h(x) = ∑ b, π_x(b | s) A^π(s, b)`, and `h(θ(s, a)) = 0`.
* `h(x) = N(x) / D(x)` with `N(x) = ∑ b, exp θ_x(s, b) A^π(s, b)` and
  `D(x) = ∑ b, exp θ_x(s, b)`, whose derivatives at `θ(s, a)` are `exp θ(s, a) A^π(s, a)` and
  `exp θ(s, a)`. Since `N(θ(s, a)) = 0`, the quotient rule gives `h'(θ(s, a)) = π(a | s) A^π(s, a)`.
* `g` is continuous at `θ(s, a)`: the value of a Markov reward process depends continuously on its
  transition matrix, by the perturbation identity `V_Q - V_P = (I - γ Q)⁻¹ (γ (Q - P) V_P)` and
  the bound `‖(I - γ Q)⁻¹ c‖∞ ≤ ‖c‖∞ / (1 - γ)`, and the transition matrix of `π_x` is
  continuous in `x`.
* So the difference quotient `g(x) (h(x) - h(θ(s, a))) / (x - θ(s, a))` tends to
  `g(θ(s, a)) π(a | s) A^π(s, a)`, the claimed derivative.

## Implementation notes

The names, statements and docstrings of `softmaxObjective`, `softmaxPolicyGradient` and
`hasDerivAt_softmaxObjective` are those of the former wanted declarations; their docstrings cite
the first source by its arXiv numbering (AKLM Lemma C.1). The sources state the gradient for a
start distribution `μ`; here `μ` is any real vector, since both sides are linear in `μ`. The
hypotheses `M.Stochastic` and `0 ≤ γ < 1` are those under which values, advantages and
occupancies are defined.

## References

* A. Agarwal, S. M. Kakade, J. D. Lee and G. Mahajan, *On the Theory of Policy Gradient Methods:
  Optimality, Approximation, and Distribution Shift*, arXiv:1908.00261v5, equation (10) and
  Lemma C.1; JMLR 22(98) (2021), equation (10) and Lemma 40.
* A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and Algorithms*,
  https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 12.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

open Filter Topology StochasticPolicy

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] [DecidableEq A]
  {M : MDP S A ℝ} {γ : ℝ}

/-- The objective `V^{π_θ}(μ) = ∑ s₀, μ s₀ V^{π_θ}(s₀)` of softmax policy optimization. -/
noncomputable def softmaxObjective (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ)
    (θ : S → A → ℝ) : ℝ :=
  ∑ s₀, μ s₀ * stochValue M γ hM hγ0 hγ1 (softmax θ) s₀

/-- The softmax policy gradient `(1 - γ)⁻¹ d^{π_θ}_μ(s) π_θ(a | s) A^{π_θ}(s, a)` (AKLM
Lemma C.1; AJKS Lemma 12.2), where `d^{π_θ}_μ(s) = ∑ s₀, μ s₀ d^{π_θ}_{s₀}(s)`. -/
noncomputable def softmaxPolicyGradient (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) (θ : S → A → ℝ) (s : S) (a : A) : ℝ :=
  (1 - γ)⁻¹ * (∑ s₀, μ s₀ * occupancy hM hγ0 hγ1 (softmax θ) s₀ s) * (softmax θ).prob s a *
    advantage hM hγ0 hγ1 (softmax θ) s a

/-! ## The derivative -/

open Real in
/-- Along the coordinate `a` of the logits `v`, the softmax average `∑ b, π_v(b) w(b)` of a vector
`w` with `∑ b, π_v(b) w(b) = 0` has derivative `π_v(a) w(a)`. -/
private theorem hasDerivAt_softmax_average {v w : A → ℝ} (a : A)
    (hw : ∑ b, exp (v b) / (∑ c, exp (v c)) * w b = 0) :
    HasDerivAt
      (fun x => ∑ b, exp (Function.update v a x b) / (∑ c, exp (Function.update v a x c)) * w b)
      (exp (v a) / (∑ c, exp (v c)) * w a) (v a) := by
  have hu : ∀ b, HasDerivAt (fun x => Function.update v a x b) (if b = a then 1 else 0) (v a) := by
    intro b
    by_cases hb : b = a
    · subst hb
      simpa using hasDerivAt_id' (v b)
    · simpa [Function.update_of_ne hb, hb] using hasDerivAt_const (v a) (v b)
  -- with `v_x = Function.update v a x`: the denominator `D x = ∑ c, exp (v_x c)` and the
  -- numerator `N x = ∑ b, exp (v_x b) * w b`
  have hD : HasDerivAt (fun x => ∑ c, exp (Function.update v a x c)) (exp (v a)) (v a) := by
    convert HasDerivAt.sum (u := Finset.univ) fun c _ => (hu c).exp using 1
    · ext x
      simp
    · simp
  have hN : HasDerivAt (fun x => ∑ b, exp (Function.update v a x b) * w b) (exp (v a) * w a)
      (v a) := by
    convert HasDerivAt.sum (u := Finset.univ) fun b _ => ((hu b).exp).mul_const (w b) using 1
    · ext x
      simp
    · simp
  have hZ : 0 < ∑ c, exp (v c) := Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty
  have hN0 : ∑ b, exp (v b) * w b = 0 := by
    have : ∑ b, exp (v b) / (∑ c, exp (v c)) * w b =
        (∑ b, exp (v b) * w b) / ∑ c, exp (v c) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, div_eq_zero_iff] at hw
    exact hw.resolve_right hZ.ne'
  convert hN.div hD (by simpa using hZ.ne') using 1
  · ext x
    rw [Pi.div_apply, Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => by ring
  · simp only [Function.update_eq_self, hN0]
    field_simp
    ring

/-- **The policy gradient theorem for softmax policies** (AKLM Lemma C.1; AJKS Lemma 12.2): the
partial derivative of `θ ↦ V^{π_θ}(μ)` in the coordinate `θ(s, a)` is
`(1 - γ)⁻¹ d^{π_θ}_μ(s) π_θ(a | s) A^{π_θ}(s, a)`. -/
theorem hasDerivAt_softmaxObjective (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (μ : S → ℝ) (θ : S → A → ℝ) (s : S) (a : A) :
    HasDerivAt (fun x => softmaxObjective hM hγ0 hγ1 μ
        (Function.update θ s (Function.update (θ s) a x)))
      (softmaxPolicyGradient hM hγ0 hγ1 μ θ s a) (θ s a) := by
  -- `θx x` is `θ` with the coordinate `θ(s, a)` replaced by `x`
  set θx : ℝ → S → A → ℝ := fun x => Function.update θ s (Function.update (θ s) a x)
  set w : A → ℝ := advantage hM hγ0 hγ1 (softmax θ) s
  set g : ℝ → ℝ := fun x =>
    (1 - γ)⁻¹ * ∑ s₀, μ s₀ * occupancy hM hγ0 hγ1 (softmax (θx x)) s₀ s
  set h : ℝ → ℝ := fun x => ∑ b, Real.exp (Function.update (θ s) a x b) /
    (∑ c, Real.exp (Function.update (θ s) a x c)) * w b
  have hθx0 : θx (θ s a) = θ := by simp [θx]
  -- the policies `π_{θx x}` and `π_θ` agree outside `s`
  have hprob_ne : ∀ x s', s' ≠ s → ∀ b,
      (softmax (θx x)).prob s' b = (softmax θ).prob s' b := by
    intro x s' hs' b
    rw [softmax_prob, softmax_prob]
    simp only [θx, Function.update_of_ne hs']
  have hprob_s : ∀ x b, (softmax (θx x)).prob s b = Real.exp (Function.update (θ s) a x b) /
      ∑ c, Real.exp (Function.update (θ s) a x c) := by
    intro x b
    rw [softmax_prob]
    simp only [θx, Function.update_self]
  -- the performance difference lemma leaves only the term of the state `s`
  have hdiff : ∀ x, softmaxObjective hM hγ0 hγ1 μ (θx x) - softmaxObjective hM hγ0 hγ1 μ θ =
      g x * h x := by
    intro x
    unfold softmaxObjective
    rw [performance_difference_initial hM hγ0 hγ1 (softmax θ) (softmax (θx x)) μ,
      Finset.sum_eq_single s]
    · simp only [g, h, w, hprob_s]
      ring
    · intro s' _ hs'
      simp only [hprob_ne x s' hs']
      rw [sum_prob_mul_advantage, mul_zero]
    · intro hs
      exact absurd (Finset.mem_univ s) hs
  -- the derivative of `h`
  have hw : ∑ b, Real.exp (θ s b) / (∑ c, Real.exp (θ s c)) * w b = 0 := by
    have := sum_prob_mul_advantage hM hγ0 hγ1 (softmax θ) s
    simpa only [softmax_prob] using this
  have hh := hasDerivAt_softmax_average a hw
  have hh0 : h (θ s a) = 0 := by
    simpa only [h, Function.update_eq_self] using hw
  -- the continuity of `g`
  have hθc : ∀ s' c, Continuous fun x => θx x s' c := by
    intro s' c
    by_cases hs : s' = s
    · by_cases hc : c = a
      · simpa only [θx, hs, hc, Function.update_self] using continuous_id'
      · simpa only [θx, hs, Function.update_self, Function.update_of_ne hc] using continuous_const
    · simpa only [θx, Function.update_of_ne hs] using continuous_const
  have hg : Tendsto g (𝓝 (θ s a))
      (𝓝 ((1 - γ)⁻¹ * ∑ s₀, μ s₀ * occupancy hM hγ0 hγ1 (softmax θ) s₀ s)) := by
    refine (tendsto_finsetSum _ fun s₀ _ => ((tendsto_occupancy_of_tendsto hM hγ0 hγ1
      (fun s' b => ?_) s₀ s).const_mul (μ s₀))).const_mul _
    have hc : Continuous fun x => (softmax (θx x)).prob s' b := by
      simp only [softmax_prob]
      exact (Real.continuous_exp.comp (hθc s' b)).div
        (continuous_finsetSum _ fun c _ => Real.continuous_exp.comp (hθc s' c))
        fun x => (sum_exp_pos (θx x) s').ne'
    simpa only [hθx0] using hc.tendsto (θ s a)
  -- the difference quotient
  have key := (hg.mono_left nhdsWithin_le_nhds).mul (hasDerivAt_iff_tendsto_slope.1 hh)
  have hL : softmaxPolicyGradient hM hγ0 hγ1 μ θ s a =
      ((1 - γ)⁻¹ * ∑ s₀, μ s₀ * occupancy hM hγ0 hγ1 (softmax θ) s₀ s) *
        (Real.exp (θ s a) / (∑ c, Real.exp (θ s c)) * w a) := by
    rw [softmaxPolicyGradient, softmax_prob]
    ring
  rw [hasDerivAt_iff_tendsto_slope, hL]
  refine Tendsto.congr (fun x => ?_) key
  rw [slope_def_field, slope_def_field]
  change g x * ((h x - h (θ s a)) / (x - θ s a)) = (softmaxObjective hM hγ0 hγ1 μ (θx x) -
    softmaxObjective hM hγ0 hγ1 μ (θx (θ s a))) / (x - θ s a)
  rw [hh0, sub_zero, ← mul_div_assoc, hθx0, hdiff x]

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
