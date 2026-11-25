/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Optimization.LineSearch
public import Mathlib.Topology.Bornology.Basic

/-!
# Wanted: global convergence of the Fletcher–Reeves method under strong Wolfe line searches
-/

@[expose] public section

namespace WantedExt.Analysis.Optimization.FletcherReevesWanted

open scoped RealInnerProductSpace
open MathlibExt.Analysis.Optimization.LineSearch

/-- **Global convergence of the Fletcher–Reeves method under strong Wolfe steps.** Let `f` be a
function on a finite-dimensional real inner product space whose level set `{y | f y ≤ f (x 0)}`
is bounded and which, on an open neighbourhood `U` of that level set, is differentiable with
`L`-Lipschitz gradient. Run `x (k + 1) = x k + α k • d k` with `d 0 = -∇f(x 0)` and
`d (k + 1) = -∇f(x (k + 1)) + (‖∇f(x (k + 1))‖² / ‖∇f(x k)‖²) • d k`, where every step length
`α k > 0` satisfies the strong Wolfe conditions with `0 < δ < σ ≤ 1/2`. If no gradient vanishes,
then `liminf ‖∇f(x k)‖ = 0`.

Y. H. Dai and Y. Yuan, *A note on the nonlinear conjugate gradient method*, J. Comput. Math. 20
(2002), Theorem 4.2 under Assumption 2.1, deduced there from its Theorem 3.3 and its Lemma 4.1
(every Fletcher–Reeves direction is a descent direction), whose proof it refers to Al-Baali.
Al-Baali (IMA J. Numer. Anal. 5 (1985)) proved the case `σ < 1/2`; the endpoint `σ = 1/2` is due
to Liu, Han and Yin (1993) and to Dai and Yuan (IMA J. Numer. Anal. 16 (1996)). -/
theorem_wanted fletcherReeves_liminf_norm_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {δ σ L : ℝ} (hδ : 0 < δ)
    (hδσ : δ < σ) (hσ : σ ≤ 1 / 2) {x d : ℕ → E} {α : ℕ → ℝ}
    (hlevel : Bornology.IsBounded {y | f y ≤ f (x 0)}) {U : Set E} (hU : IsOpen U)
    (hlevelU : {y | f y ≤ f (x 0)} ⊆ U) (hdiff : DifferentiableOn ℝ f U)
    (hlip : ∀ y ∈ U, ∀ z ∈ U, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖)
    (hx : ∀ k, x (k + 1) = x k + α k • d k) (hα : ∀ k, 0 < α k)
    (hd0 : d 0 = -gradient f (x 0))
    (hd : ∀ k, d (k + 1) = -gradient f (x (k + 1)) +
      (‖gradient f (x (k + 1))‖ ^ 2 / ‖gradient f (x k)‖ ^ 2) • d k)
    (hwolfe : ∀ k, StrongWolfeConditions f δ σ (x k) (d k) (α k))
    (hg : ∀ k, gradient f (x k) ≠ 0) :
    ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, ‖gradient f (x k)‖ < ε

end WantedExt.Analysis.Optimization.FletcherReevesWanted
