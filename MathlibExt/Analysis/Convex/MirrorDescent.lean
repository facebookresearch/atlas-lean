/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Mirror descent with Bregman divergences

A *proximal setup* for a convex set `X` in a real normed space `E` is a norm (the norm of `E`) and
a distance-generating function `ω : E → ℝ` with a selection `ω'` of its derivative, valued in the
dual space `E →L[ℝ] ℝ` (whose operator norm is the dual norm `‖·‖_*`). Its Bregman divergence,
or prox-function, is `V_x(u) = ω u - ω x - ω'(x) (u - x)`. Mirror descent replaces the Euclidean
projection step of the subgradient method by the prox step
`x_{t+1} = argmin_{u ∈ X} {γ_t ⟨g_t, u⟩ + V_{x_t}(u)}`, which the results below use only through
its first-order optimality condition.

Following A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale
optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.),
*Optimization for Machine Learning*, MIT Press (2011), Section 5.2, and A. Nemirovski,
A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic
programming*, SIAM J. Optim. 19(4) (2009), 1574–1609, Section 2.3, with strong convexity
modulus `α > 0`:

* `bregman_three_point`: the three-point identity
  `V_x(u) - V_y(u) - V_x(y) = (ω'(y) - ω'(x)) (u - y)`.
* `bregman_prox_step_le`: the one-step inequality of mirror descent
  `V_{x⁺}(u) ≤ V_x(u) + ξ (u - x) + ‖ξ‖²/(2α)` (Lemma 2.1 of Nemirovski–Juditsky–Lan–Shapiro).
* `mirror_descent_sum_le`: the telescoped bound (5.7) of Juditsky–Nemirovski.
* `mirror_descent_exists_le`, `mirror_descent_average_le`: the rate (5.8) for the best iterate
  and, for convex `f`, the weighted average.
* `mirror_descent_exists_le_sqrt`: the constant-step rate `L √(2Ω) / √(α N)` of (5.10)–(5.11).
* `stochastic_mirror_descent_average_le`: the pathwise bound (2.39) of
  Nemirovski–Juditsky–Lan–Shapiro for mirror descent driven by noisy subgradients.
-/

@[expose] public section

open Finset

namespace MathlibExt.Analysis.Convex.MirrorDescent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Bregman divergence (prox-function) of a distance-generating function.** For
`ω : E → ℝ` with a derivative selection `ω' : E → (E →L[ℝ] ℝ)`,
`V_x(u) = ω u - ω x - ω'(x) (u - x)` (Juditsky and Nemirovski, *First order methods for nonsmooth
convex large-scale optimization, I*, 2011, equation (5.4); Nemirovski, Juditsky, Lan and Shapiro,
SIAM J. Optim. 19 (2009), equation (2.30)). -/
noncomputable def bregman (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (x u : E) : ℝ :=
  ω u - ω x - ω' x (u - x)

/-- **Three-point identity for Bregman divergences.** For all `x y u`,
`V_x(u) - V_y(u) - V_x(y) = (ω'(y) - ω'(x)) (u - y)`; this is the rearrangement in equation (5.12)
of Juditsky and Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I*
(2011), that turns the optimality condition of a prox step into a telescoping inequality. -/
theorem bregman_three_point (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (x y u : E) :
    bregman ω ω' x u - bregman ω ω' y u - bregman ω ω' x y = (ω' y - ω' x) (u - y) := by
  simp only [bregman, sub_apply, map_sub]
  ring

/-- `a s - (α/2) s² ≤ a² / (2α)` for `α > 0`. -/
private lemma mul_sub_sq_le {a s α : ℝ} (hα : 0 < α) : a * s - α / 2 * s ^ 2 ≤ a ^ 2 / (2 * α) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (a - α * s), hα]

/-- **One-step inequality of mirror descent.** Let `α > 0` and let `x⁺` satisfy the first-order
optimality condition `(ξ - ω'(x) + ω'(x⁺)) (u - x⁺) ≥ 0` of the prox step
`x⁺ = argmin_{u ∈ X} {ξ u + V_x(u)}` at a point `u`, and let `V_x(x⁺) ≥ (α/2) ‖x⁺ - x‖²`
(strong convexity of `V_x`). Then `V_{x⁺}(u) ≤ V_x(u) + ξ (u - x) + ‖ξ‖_*² / (2α)`.
This is Lemma 2.1, inequality (2.33), of A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro,
*Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19 (2009),
for one fixed `u`, with the optimality condition and the strong convexity of `V_x` that its proof
uses as hypotheses; with `ξ = γ f'(x)` it is (5.13) of Juditsky–Nemirovski (2011). -/
theorem bregman_prox_step_le (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α : ℝ} (hα : 0 < α)
    {x xplus u : E} {ξ : E →L[ℝ] ℝ}
    (hopt : 0 ≤ (ξ - ω' x + ω' xplus) (u - xplus))
    (hsc : α / 2 * ‖xplus - x‖ ^ 2 ≤ bregman ω ω' x xplus) :
    bregman ω ω' xplus u ≤ bregman ω ω' x u + ξ (u - x) + ‖ξ‖ ^ 2 / (2 * α) := by
  have h3 := bregman_three_point ω ω' x xplus u
  have hopt' : 0 ≤ ξ (u - xplus) + (ω' xplus - ω' x) (u - xplus) := by
    simpa [sub_apply, add_apply, sub_add_eq_add_sub,
      add_sub_assoc] using hopt
  have hsplit : ξ (u - x) = ξ (u - xplus) - ξ (x - xplus) := by
    rw [← map_sub]; congr 1; abel
  have hdual : ξ (x - xplus) ≤ ‖ξ‖ * ‖xplus - x‖ := by
    calc ξ (x - xplus) ≤ |ξ (x - xplus)| := le_abs_self _
      _ = ‖ξ (x - xplus)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ξ‖ * ‖x - xplus‖ := ξ.le_opNorm _
      _ = ‖ξ‖ * ‖xplus - x‖ := by rw [norm_sub_rev]
  have hq := mul_sub_sq_le (a := ‖ξ‖) (s := ‖xplus - x‖) hα
  linarith

/-- Strong convexity of the Bregman divergence makes it nonnegative. -/
private lemma bregman_nonneg_of_sc {ω : E → ℝ} {ω' : E → E →L[ℝ] ℝ} {α : ℝ} (hα : 0 < α)
    {x u : E} (hsc : α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u) : 0 ≤ bregman ω ω' x u :=
  le_trans (by positivity) hsc

/-- **Telescoped mirror descent bound.** Let `α > 0`, `Xo ⊆ X`, and let the distance-generating
function be `α`-strongly convex in the Bregman form `V_x(u) ≥ (α/2) ‖u - x‖²` for `x ∈ Xo`,
`u ∈ X`. Let the iterates `x t ∈ Xo` satisfy, for every `t`, the optimality condition
`(γ_t g_t - ω'(x_t) + ω'(x_{t+1})) (u - x_{t+1}) ≥ 0` for all `u ∈ X` of the prox step
`x_{t+1} = argmin_{u ∈ X} {γ_t g_t u + V_{x_t}(u)}`, for arbitrary `g t ∈ E →L[ℝ] ℝ`. Then for
every `u ∈ X` and every number of steps `N`,
`∑_{t < N} γ_t g_t (x_t - u) ≤ V_{x_0}(u) + (1/(2α)) ∑_{t < N} γ_t² ‖g_t‖_*²`.
This is inequality (5.7) of Juditsky and Nemirovski, *First order methods for nonsmooth convex
large-scale optimization, I* (2011), Proposition 5.1(i) (there with `α = 1` and iterates indexed
from `1`); summed with `g_t` the stochastic gradients it is (2.37) of Nemirovski, Juditsky, Lan
and Shapiro (2009) before the noise is split off. The source states strong convexity in the
monotone form (5.3); the proof uses it in the Bregman form assumed here. -/
theorem mirror_descent_sum_le (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α : ℝ} (hα : 0 < α)
    {X Xo : Set E} (hXo : Xo ⊆ X)
    (hsc : ∀ x ∈ Xo, ∀ u ∈ X, α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u)
    {x : ℕ → E} {g : ℕ → E →L[ℝ] ℝ} {γ : ℕ → ℝ} (hx : ∀ t, x t ∈ Xo)
    (hstep : ∀ t, ∀ u ∈ X, 0 ≤ (γ t • g t - ω' (x t) + ω' (x (t + 1))) (u - x (t + 1)))
    {u : E} (hu : u ∈ X) (N : ℕ) :
    ∑ t ∈ range N, γ t * g t (x t - u) ≤
      bregman ω ω' (x 0) u + (∑ t ∈ range N, γ t ^ 2 * ‖g t‖ ^ 2) / (2 * α) := by
  -- Telescoping with the last divergence kept.
  have key : ∀ n, ∑ t ∈ range n, γ t * g t (x t - u) + bregman ω ω' (x n) u ≤
      bregman ω ω' (x 0) u + (∑ t ∈ range n, γ t ^ 2 * ‖g t‖ ^ 2) / (2 * α) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hone := bregman_prox_step_le ω ω' hα (x := x n) (xplus := x (n + 1)) (u := u)
        (ξ := γ n • g n) (hstep n u hu) (hsc _ (hx n) _ (hXo (hx (n + 1))))
      have hξ : (γ n • g n) (u - x n) = -(γ n * g n (x n - u)) := by
        rw [smul_apply, smul_eq_mul, ← neg_sub, map_neg]; ring
      have hn : ‖γ n • g n‖ ^ 2 = γ n ^ 2 * ‖g n‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hξ, hn] at hone
      rw [sum_range_succ, sum_range_succ, add_div]
      linarith
  have hlast := bregman_nonneg_of_sc hα (hsc _ (hx N) _ hu)
  linarith [key N]

/-- **Rate of mirror descent for the best iterate.** In the setting of `mirror_descent_sum_le`,
let `g t` be a subgradient of `f` at `x t` relative to `X` (`f (x t) + g_t (y - x t) ≤ f y` for
`y ∈ X`), with `‖g t‖_* ≤ L`, and let the steps be positive. Then for every `xstar ∈ X` and
`N ≥ 1` some iterate `t < N` satisfies
`f (x t) - f xstar ≤ (V_{x_0}(xstar) + (L²/(2α)) ∑_{t<N} γ_t²) / ∑_{t<N} γ_t`.
This is (5.8) of Juditsky and Nemirovski, *First order methods for nonsmooth convex large-scale
optimization, I* (2011), Proposition 5.1(i), for the best iterate `x̂` (there with `α = 1`). -/
theorem mirror_descent_exists_le (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α : ℝ} (hα : 0 < α)
    {X Xo : Set E} (hXo : Xo ⊆ X)
    (hsc : ∀ x ∈ Xo, ∀ u ∈ X, α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u)
    {f : E → ℝ} {L : ℝ} {x : ℕ → E} {g : ℕ → E →L[ℝ] ℝ} {γ : ℕ → ℝ} (hx : ∀ t, x t ∈ Xo)
    (hstep : ∀ t, ∀ u ∈ X, 0 ≤ (γ t • g t - ω' (x t) + ω' (x (t + 1))) (u - x (t + 1)))
    (hsub : ∀ t, ∀ y ∈ X, f (x t) + g t (y - x t) ≤ f y) (hg : ∀ t, ‖g t‖ ≤ L)
    (hγ : ∀ t, 0 < γ t) {xstar : E} (hxstar : xstar ∈ X) {N : ℕ} (hN : 0 < N) :
    ∃ t < N, f (x t) - f xstar ≤
      (bregman ω ω' (x 0) xstar + L ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α)) /
        ∑ t ∈ range N, γ t := by
  have hsum := mirror_descent_sum_le ω ω' hα hXo hsc hx hstep hxstar N
  have hS : 0 < ∑ t ∈ range N, γ t := sum_pos (fun t _ => hγ t) (nonempty_range_iff.mpr hN.ne')
  have hL : 0 ≤ L := le_trans (norm_nonneg _) (hg 0)
  have hgap : ∀ t, f (x t) - f xstar ≤ g t (x t - xstar) := by
    intro t
    have := hsub t xstar hxstar
    have h2 : g t (xstar - x t) = -g t (x t - xstar) := by rw [← map_neg, neg_sub]
    linarith
  have hsq : ∑ t ∈ range N, γ t ^ 2 * ‖g t‖ ^ 2 ≤ L ^ 2 * ∑ t ∈ range N, γ t ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun t _ => ?_
    have : ‖g t‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hg t) 2
    nlinarith [sq_nonneg (γ t)]
  by_contra hcon
  push Not at hcon
  set m := (bregman ω ω' (x 0) xstar + L ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α)) /
    ∑ t ∈ range N, γ t
  have hlt : m * ∑ t ∈ range N, γ t < ∑ t ∈ range N, γ t * g t (x t - xstar) := by
    rw [mul_sum]
    refine sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hN.ne') fun t ht => ?_
    have := hcon t (mem_range.mp ht)
    have := hgap t
    nlinarith [hγ t]
  have hm : m * ∑ t ∈ range N, γ t =
      bregman ω ω' (x 0) xstar + L ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α) := by
    simp only [m]; field_simp
  have : (∑ t ∈ range N, γ t ^ 2 * ‖g t‖ ^ 2) / (2 * α) ≤
      L ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α) := by
    gcongr
  linarith

/-- **Rate of mirror descent for the weighted average.** In the setting of
`mirror_descent_exists_le`, if moreover `f` is convex on `X`, then the weighted average
`x̄_N = (∑_{t<N} γ_t)⁻¹ ∑_{t<N} γ_t x_t` satisfies
`f x̄_N - f xstar ≤ (V_{x_0}(xstar) + (L²/(2α)) ∑_{t<N} γ_t²) / ∑_{t<N} γ_t`.
This is (5.8) of Juditsky and Nemirovski, *First order methods for nonsmooth convex large-scale
optimization, I* (2011), Proposition 5.1(i), for the averaged iterate `x̄` (there with
`α = 1`). -/
theorem mirror_descent_average_le (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α : ℝ} (hα : 0 < α)
    {X Xo : Set E} (hXo : Xo ⊆ X)
    (hsc : ∀ x ∈ Xo, ∀ u ∈ X, α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u)
    {f : E → ℝ} (hf : ConvexOn ℝ X f) {L : ℝ} {x : ℕ → E} {g : ℕ → E →L[ℝ] ℝ} {γ : ℕ → ℝ}
    (hx : ∀ t, x t ∈ Xo)
    (hstep : ∀ t, ∀ u ∈ X, 0 ≤ (γ t • g t - ω' (x t) + ω' (x (t + 1))) (u - x (t + 1)))
    (hsub : ∀ t, ∀ y ∈ X, f (x t) + g t (y - x t) ≤ f y) (hg : ∀ t, ‖g t‖ ≤ L)
    (hγ : ∀ t, 0 < γ t) {xstar : E} (hxstar : xstar ∈ X) {N : ℕ} (hN : 0 < N) :
    f ((∑ t ∈ range N, γ t)⁻¹ • ∑ t ∈ range N, γ t • x t) - f xstar ≤
      (bregman ω ω' (x 0) xstar + L ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α)) /
        ∑ t ∈ range N, γ t := by
  have hsum := mirror_descent_sum_le ω ω' hα hXo hsc hx hstep hxstar N
  set S := ∑ t ∈ range N, γ t with hSdef
  have hS : 0 < S := sum_pos (fun t _ => hγ t) (nonempty_range_iff.mpr hN.ne')
  have hgap : ∀ t, f (x t) - f xstar ≤ g t (x t - xstar) := by
    intro t
    have := hsub t xstar hxstar
    have h2 : g t (xstar - x t) = -g t (x t - xstar) := by rw [← map_neg, neg_sub]
    linarith
  have hsq : ∑ t ∈ range N, γ t ^ 2 * ‖g t‖ ^ 2 ≤ L ^ 2 * ∑ t ∈ range N, γ t ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun t _ => ?_
    have : ‖g t‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hg t) 2
    nlinarith [sq_nonneg (γ t)]
  -- Jensen's inequality for the weights `γ_t / S`.
  have hjensen : f (∑ t ∈ range N, (γ t / S) • x t) ≤ ∑ t ∈ range N, (γ t / S) * f (x t) := by
    have := hf.map_sum_le (t := range N) (w := fun t => γ t / S) (p := x)
      (fun t _ => div_nonneg (hγ t).le hS.le)
      (by rw [show (∑ i ∈ range N, γ i / S) = (∑ i ∈ range N, γ i) / S by
        simp [div_eq_mul_inv, Finset.sum_mul], ← hSdef, div_self hS.ne'])
      (fun t _ => hXo (hx t))
    simpa [smul_eq_mul] using this
  have hpt : (S)⁻¹ • ∑ t ∈ range N, γ t • x t = ∑ t ∈ range N, (γ t / S) • x t := by
    rw [smul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [smul_smul, div_eq_inv_mul]
  rw [hpt]
  have hlin : ∑ t ∈ range N, (γ t / S) * f (x t) - f xstar =
      (∑ t ∈ range N, γ t * (f (x t) - f xstar)) / S := by
    rw [eq_div_iff hS.ne', sub_mul, sum_mul]
    have : ∑ t ∈ range N, γ t * (f (x t) - f xstar) =
        ∑ t ∈ range N, γ t * f (x t) - S * f xstar := by
      rw [hSdef, sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun t _ => by ring
    rw [this]
    congr 1
    · refine sum_congr rfl fun t _ => ?_
      field_simp
    · ring
  have hwt : ∑ t ∈ range N, γ t * (f (x t) - f xstar) ≤ ∑ t ∈ range N, γ t * g t (x t - xstar) :=
    sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hgap t) (hγ t).le
  have hdiv : (∑ t ∈ range N, γ t * (f (x t) - f xstar)) / S ≤
      (bregman ω ω' (x 0) xstar + L ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α)) / S := by
    apply div_le_div_of_nonneg_right _ hS.le
    have : (∑ t ∈ range N, γ t ^ 2 * ‖g t‖ ^ 2) / (2 * α) ≤
        L ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α) := by gcongr
    linarith
  linarith

/-- **Constant-step rate of mirror descent.** In the setting of `mirror_descent_exists_le` with
`L > 0`, let `V_{x_0}(xstar) ≤ Ω` (for instance `Ω` the `ω`-diameter of `X` when `x_0` minimizes
`ω` on `X`), and run `N ≥ 1` steps with the constant step `γ_t = √(2αΩ) / (L √N)`, `Ω > 0`.
Then some iterate `t < N` satisfies `f (x t) - f xstar ≤ L √(2Ω) / √(αN)`.
With `α = 1` this is the bound `√(2Ω) L / √N` of (5.10)–(5.11) in Juditsky and Nemirovski,
*First order methods for nonsmooth convex large-scale optimization, I* (2011),
Proposition 5.1(ii), for the best iterate (the source also certifies it by an online lower bound,
not formalized here). -/
theorem mirror_descent_exists_le_sqrt (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α : ℝ} (hα : 0 < α)
    {X Xo : Set E} (hXo : Xo ⊆ X)
    (hsc : ∀ x ∈ Xo, ∀ u ∈ X, α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u)
    {f : E → ℝ} {L Ω : ℝ} (hL : 0 < L) (hΩ : 0 < Ω) {x : ℕ → E} {g : ℕ → E →L[ℝ] ℝ}
    {N : ℕ} (hN : 0 < N) (hx : ∀ t, x t ∈ Xo)
    (hstep : ∀ t, ∀ u ∈ X, 0 ≤ ((√(2 * α * Ω) / (L * √N)) • g t - ω' (x t) + ω' (x (t + 1)))
      (u - x (t + 1)))
    (hsub : ∀ t, ∀ y ∈ X, f (x t) + g t (y - x t) ≤ f y) (hg : ∀ t, ‖g t‖ ≤ L)
    {xstar : E} (hxstar : xstar ∈ X) (hV : bregman ω ω' (x 0) xstar ≤ Ω) :
    ∃ t < N, f (x t) - f xstar ≤ L * √(2 * Ω) / √(α * N) := by
  set c := √(2 * α * Ω) / (L * √N) with hc
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hcpos : 0 < c := by positivity
  obtain ⟨t, ht, hle⟩ := mirror_descent_exists_le ω ω' hα hXo hsc (γ := fun _ => c) hx hstep hsub
    hg (fun _ => hcpos) hxstar hN
  refine ⟨t, ht, hle.trans ?_⟩
  simp only [sum_const, card_range, nsmul_eq_mul]
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hNr
  have h2 : (0 : ℝ) < √(2 * α * Ω) := Real.sqrt_pos.mpr (by positivity)
  have hcsq : c ^ 2 = 2 * α * Ω / (L ^ 2 * N) := by
    rw [hc, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hNr.le]
  have hαN : √(α * N) = √α * √N := Real.sqrt_mul hα.le _
  have h2Ω : √(2 * α * Ω) = √α * √(2 * Ω) := by
    rw [show 2 * α * Ω = α * (2 * Ω) by ring, Real.sqrt_mul hα.le]
  have hsα : 0 < √α := Real.sqrt_pos.mpr hα
  have hs2Ω : 0 < √(2 * Ω) := Real.sqrt_pos.mpr (by positivity)
  have hΩsq : √(2 * Ω) ^ 2 = 2 * Ω := Real.sq_sqrt (by positivity)
  have hαsq : √α ^ 2 = α := Real.sq_sqrt hα.le
  have hNsq : √(N : ℝ) ^ 2 = N := Real.sq_sqrt hNr.le
  rw [div_le_div_iff₀ (by positivity) (by positivity), hαN]
  -- Reduce to the exact value of the bound at this step size.
  have hval : (Ω + L ^ 2 * (N * c ^ 2) / (2 * α)) * (√α * √N) = L * √(2 * Ω) * (N * c) := by
    rw [hcsq, hc, h2Ω]
    have e1 : √(Ω * 2) ^ 2 = Ω * 2 := Real.sq_sqrt (by positivity)
    field_simp
    nlinarith [hΩsq, hαsq, hNsq, e1]
  have hmono : (bregman ω ω' (x 0) xstar + L ^ 2 * (N * c ^ 2) / (2 * α)) * (√α * √N) ≤
      (Ω + L ^ 2 * (N * c ^ 2) / (2 * α)) * (√α * √N) := by
    gcongr
  linarith

/-- **Pathwise bound of stochastic mirror descent.** In the setting of `mirror_descent_sum_le`,
let the prox steps use noisy vectors `G t = g t + Δ t`, where `g t` is a subgradient of the convex
function `f` at `x t` relative to `X`, and let the steps be positive. Then for every `xstar ∈ X`
and `N ≥ 1` the weighted average `x̃_N = (∑_{t<N} γ_t)⁻¹ ∑_{t<N} γ_t x_t` satisfies
`f x̃_N - f xstar ≤ (V_{x_0}(xstar) + (1/(2α)) ∑ γ_t² ‖G_t‖_*² - ∑ γ_t Δ_t (x_t - xstar)) / ∑ γ_t`.
This is inequality (2.39) of A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust
stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19 (2009),
Section 2.3, which holds for every realization of the noise; taking expectations of it gives their
efficiency estimate (2.44), which is
`RobustStochasticApproximation.integral_robust_sa_average_sub_le` (with a bounded stochastic
subgradient). -/
theorem stochastic_mirror_descent_average_le (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α : ℝ}
    (hα : 0 < α) {X Xo : Set E} (hXo : Xo ⊆ X)
    (hsc : ∀ x ∈ Xo, ∀ u ∈ X, α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u)
    {f : E → ℝ} (hf : ConvexOn ℝ X f) {x : ℕ → E} {g Δ : ℕ → E →L[ℝ] ℝ} {γ : ℕ → ℝ}
    (hx : ∀ t, x t ∈ Xo)
    (hstep : ∀ t, ∀ u ∈ X,
      0 ≤ (γ t • (g t + Δ t) - ω' (x t) + ω' (x (t + 1))) (u - x (t + 1)))
    (hsub : ∀ t, ∀ y ∈ X, f (x t) + g t (y - x t) ≤ f y)
    (hγ : ∀ t, 0 < γ t) {xstar : E} (hxstar : xstar ∈ X) {N : ℕ} (hN : 0 < N) :
    f ((∑ t ∈ range N, γ t)⁻¹ • ∑ t ∈ range N, γ t • x t) - f xstar ≤
      (bregman ω ω' (x 0) xstar + (∑ t ∈ range N, γ t ^ 2 * ‖g t + Δ t‖ ^ 2) / (2 * α) -
        ∑ t ∈ range N, γ t * Δ t (x t - xstar)) / ∑ t ∈ range N, γ t := by
  have hsum := mirror_descent_sum_le ω ω' hα hXo hsc (g := fun t => g t + Δ t) hx hstep hxstar N
  set S := ∑ t ∈ range N, γ t with hSdef
  have hS : 0 < S := sum_pos (fun t _ => hγ t) (nonempty_range_iff.mpr hN.ne')
  have hgap : ∀ t, f (x t) - f xstar ≤ g t (x t - xstar) := by
    intro t
    have := hsub t xstar hxstar
    have h2 : g t (xstar - x t) = -g t (x t - xstar) := by rw [← map_neg, neg_sub]
    linarith
  have hsplit : ∑ t ∈ range N, γ t * (g t + Δ t) (x t - xstar) =
      ∑ t ∈ range N, γ t * g t (x t - xstar) + ∑ t ∈ range N, γ t * Δ t (x t - xstar) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [add_apply]; ring
  have hjensen : f (∑ t ∈ range N, (γ t / S) • x t) ≤ ∑ t ∈ range N, (γ t / S) * f (x t) := by
    have := hf.map_sum_le (t := range N) (w := fun t => γ t / S) (p := x)
      (fun t _ => div_nonneg (hγ t).le hS.le)
      (by rw [show (∑ i ∈ range N, γ i / S) = (∑ i ∈ range N, γ i) / S by
        simp [div_eq_mul_inv, Finset.sum_mul], ← hSdef, div_self hS.ne'])
      (fun t _ => hXo (hx t))
    simpa [smul_eq_mul] using this
  have hpt : (S)⁻¹ • ∑ t ∈ range N, γ t • x t = ∑ t ∈ range N, (γ t / S) • x t := by
    rw [smul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [smul_smul, div_eq_inv_mul]
  rw [hpt]
  have hlin : ∑ t ∈ range N, (γ t / S) * f (x t) - f xstar =
      (∑ t ∈ range N, γ t * (f (x t) - f xstar)) / S := by
    rw [eq_div_iff hS.ne', sub_mul, sum_mul]
    have : ∑ t ∈ range N, γ t * (f (x t) - f xstar) =
        ∑ t ∈ range N, γ t * f (x t) - S * f xstar := by
      rw [hSdef, sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun t _ => by ring
    rw [this]
    congr 1
    · refine sum_congr rfl fun t _ => ?_
      field_simp
    · ring
  have hwt : ∑ t ∈ range N, γ t * (f (x t) - f xstar) ≤ ∑ t ∈ range N, γ t * g t (x t - xstar) :=
    sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hgap t) (hγ t).le
  have hdiv : (∑ t ∈ range N, γ t * (f (x t) - f xstar)) / S ≤
      (bregman ω ω' (x 0) xstar + (∑ t ∈ range N, γ t ^ 2 * ‖g t + Δ t‖ ^ 2) / (2 * α) -
        ∑ t ∈ range N, γ t * Δ t (x t - xstar)) / S := by
    apply div_le_div_of_nonneg_right _ hS.le
    linarith
  linarith

end MathlibExt.Analysis.Convex.MirrorDescent
