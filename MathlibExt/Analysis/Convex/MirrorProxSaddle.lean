/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.MirrorProx

/-!
# Mirror-prox for convex-concave saddle-point problems

For a function `f` on `X × Y`, convex in `x` and concave in `y`, the saddle-point problem
`min_{x ∈ X} max_{y ∈ Y} f(x, y)` is the variational inequality with the monotone operator
`F(x, y) = (∂ₓf(x, y), -∂ᵧf(x, y))`. Running mirror-prox (`MirrorProx`) on it, the averages
`(x̄_N, ȳ_N)` of the leading points satisfy `f(x̄_N, y) - f(x, ȳ_N) ≤ V_{z₀}(x, y) / (γ N)` for all
`(x, y) ∈ X × Y`, hence the saddle-point accuracy
`max_y f(x̄_N, y) - min_x f(x, ȳ_N) ≤ √2 Θ L / (α N)` of A. Nemirovski, *Prox-method with rate of
convergence O(1/t) for variational inequalities with Lipschitz continuous monotone operators and
smooth convex-concave saddle point problems*, SIAM J. Optim. 15 (2004), Theorem 3.2, (3.10).

The partial derivatives enter only through the first-order inequalities of convexity in `x` and
concavity in `y` at the leading points.

* `mirror_prox_sum_le`: the telescoped bound `γ ∑_{t<N} F(w_t)(w_t - u) ≤ V_{z₀}(u)`.
* `mirror_prox_saddle_le`, `mirror_prox_saddle_le_sqrt_two`: the saddle-point bounds.
-/

@[expose] public section

open Finset

namespace MathlibExt.Analysis.Convex.MirrorProx

open MathlibExt.Analysis.Convex.MirrorDescent

/-- **Telescoped mirror-prox bound.** In the setting of `mirror_prox_average_le` but without
monotonicity, with `0 < γ`, `γ L ≤ α` and `F` `L`-Lipschitz on `Z`, the leading points satisfy
`γ ∑_{t<N} F(w_t)(w_t - u) ≤ V_{z₀}(u)` for every `u ∈ Z` and every `N`.
This is the sum over the steps of Lemma 3.1, (3.7.b)–(3.7.d), in A. Nemirovski, *Prox-method with
rate of convergence O(1/t) for variational inequalities with Lipschitz continuous monotone operators
and smooth convex-concave saddle point problems*, SIAM J. Optim. 15 (2004), as in the proof of
Proposition 2.2 there. -/
theorem mirror_prox_sum_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α γ L : ℝ} (hα : 0 < α)
    (hγ : 0 < γ) (hγL : γ * L ≤ α) {Z : Set E}
    (hsc : ∀ x ∈ Z, ∀ u ∈ Z, α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u)
    (F : E → E →L[ℝ] ℝ) (hlip : ∀ a ∈ Z, ∀ b ∈ Z, ‖F a - F b‖ ≤ L * ‖a - b‖)
    {z w : ℕ → E} (hz : ∀ t, z t ∈ Z) (hw : ∀ t, w t ∈ Z)
    (hoptw : ∀ t, ∀ u ∈ Z, 0 ≤ (γ • F (z t) - ω' (z t) + ω' (w t)) (u - w t))
    (hoptz : ∀ t, ∀ u ∈ Z, 0 ≤ (γ • F (w t) - ω' (z t) + ω' (z (t + 1))) (u - z (t + 1)))
    {u : E} (hu : u ∈ Z) (N : ℕ) :
    γ * ∑ t ∈ range N, F (w t) (w t - u) ≤ bregman ω ω' (z 0) u := by
  have hstep : ∀ t, γ * F (w t) (w t - u) ≤ bregman ω ω' (z t) u - bregman ω ω' (z (t + 1)) u := by
    intro t
    refine mirror_prox_step_le ω ω' hα hγ.le hsc F (hz t) (hw t) (hz (t + 1)) (hoptw t)
      (hoptz t) ?_ hu
    calc γ * ‖F (z t) - F (w t)‖ ≤ γ * (L * ‖z t - w t‖) :=
          mul_le_mul_of_nonneg_left (hlip _ (hz t) _ (hw t)) hγ.le
      _ = (γ * L) * ‖z t - w t‖ := by ring
      _ ≤ α * ‖z t - w t‖ := mul_le_mul_of_nonneg_right hγL (norm_nonneg _)
  have htel : ∀ n, γ * ∑ t ∈ range n, F (w t) (w t - u) ≤
      bregman ω ω' (z 0) u - bregman ω ω' (z n) u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, mul_add]
      linarith [hstep n]
  have hlast : 0 ≤ bregman ω ω' (z N) u := le_trans (by positivity) (hsc _ (hz N) _ hu)
  linarith [htel N]

variable {Ex Ey : Type*} [NormedAddCommGroup Ex] [NormedSpace ℝ Ex] [NormedAddCommGroup Ey]
  [NormedSpace ℝ Ey]

/-- **Mirror-prox for convex-concave saddle points.** Let `X ⊆ Ex`, `Y ⊆ Ey`, let `f` be
convex in `x ∈ X` for every `y ∈ Y` and concave in `y ∈ Y` for every `x ∈ X`, and let the operator
`F(x, y)(a, b) = Fₓ(x, y)(a) - F_y(x, y)(b)` on `Ex × Ey` (with the product norm) be built from
partial (super/sub)gradients: `f(x', y) ≥ f(x, y) + Fₓ(x, y)(x' - x)` and
`f(x, y') ≤ f(x, y) + F_y(x, y)(y' - y)` for `(x, y) ∈ X × Y`, `x' ∈ X`, `y' ∈ Y`. Let `F` be
`L`-Lipschitz on `Z = X × Y`, let `ω` be `α`-strongly convex on `Z` in the Bregman form, and let
`0 < γ` with `γ L ≤ α`. If `z t, w t ∈ Z` satisfy the optimality conditions of the mirror-prox
steps, then for `N ≥ 1` the average `(x̄_N, ȳ_N) = N⁻¹ ∑_{t<N} w_t` satisfies
`f(x̄_N, y) - f(x, ȳ_N) ≤ V_{z₀}(x, y) / (γ N)` for every `(x, y) ∈ X × Y`.
This is the saddle-point part of Proposition 2.2(ii) (the bound on `ε_f`, with `ε_t = 0`) of
A. Nemirovski, *Prox-method with rate of convergence O(1/t) for variational inequalities with
Lipschitz continuous monotone operators and smooth convex-concave saddle point problems*, SIAM J.
Optim. 15 (2004), for constant steps and the iteration that always performs both prox steps; the
source takes `f` continuously differentiable and `F = (f'ₓ, -f'_y)`. -/
theorem mirror_prox_saddle_le (ω : Ex × Ey → ℝ) (ω' : Ex × Ey → (Ex × Ey) →L[ℝ] ℝ)
    {α γ L : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hγL : γ * L ≤ α) {X : Set Ex} {Y : Set Ey}
    (hsc : ∀ p ∈ X ×ˢ Y, ∀ q ∈ X ×ˢ Y, α / 2 * ‖q - p‖ ^ 2 ≤ bregman ω ω' p q)
    {f : Ex × Ey → ℝ} (hfx : ∀ y ∈ Y, ConvexOn ℝ X fun x => f (x, y))
    (hfy : ∀ x ∈ X, ConcaveOn ℝ Y fun y => f (x, y))
    (F : Ex × Ey → (Ex × Ey) →L[ℝ] ℝ) (Fx : Ex × Ey → Ex →L[ℝ] ℝ) (Fy : Ex × Ey → Ey →L[ℝ] ℝ)
    (hF : ∀ p q, F p q = Fx p q.1 - Fy p q.2)
    (hgx : ∀ p ∈ X ×ˢ Y, ∀ x' ∈ X, f p + Fx p (x' - p.1) ≤ f (x', p.2))
    (hgy : ∀ p ∈ X ×ˢ Y, ∀ y' ∈ Y, f (p.1, y') ≤ f p + Fy p (y' - p.2))
    (hlip : ∀ a ∈ X ×ˢ Y, ∀ b ∈ X ×ˢ Y, ‖F a - F b‖ ≤ L * ‖a - b‖)
    {z w : ℕ → Ex × Ey} (hz : ∀ t, z t ∈ X ×ˢ Y) (hw : ∀ t, w t ∈ X ×ˢ Y)
    (hoptw : ∀ t, ∀ u ∈ X ×ˢ Y, 0 ≤ (γ • F (z t) - ω' (z t) + ω' (w t)) (u - w t))
    (hoptz : ∀ t, ∀ u ∈ X ×ˢ Y, 0 ≤ (γ • F (w t) - ω' (z t) + ω' (z (t + 1))) (u - z (t + 1)))
    {N : ℕ} (hN : 0 < N) {x : Ex} {y : Ey} (hx : x ∈ X) (hy : y ∈ Y) :
    f (((N : ℝ)⁻¹ • ∑ t ∈ range N, w t).1, y) - f (x, ((N : ℝ)⁻¹ • ∑ t ∈ range N, w t).2) ≤
      bregman ω ω' (z 0) (x, y) / (γ * N) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hu : (x, y) ∈ X ×ˢ Y := ⟨hx, hy⟩
  have hsum := mirror_prox_sum_le ω ω' hα hγ hγL hsc F hlip hz hw hoptw hoptz hu N
  -- Each leading point: `F(w)(w - (x, y)) ≥ f(w.1, y) - f(x, w.2)`.
  have hgap : ∀ t, f ((w t).1, y) - f (x, (w t).2) ≤ F (w t) (w t - (x, y)) := by
    intro t
    have h1 := hgx (w t) (hw t) x hx
    have h2 := hgy (w t) (hw t) y hy
    rw [hF]
    have e1 : Fx (w t) (x - (w t).1) = -Fx (w t) ((w t - (x, y)).1) := by
      rw [← map_neg]; congr 1; simp
    have e2 : Fy (w t) (y - (w t).2) = -Fy (w t) ((w t - (x, y)).2) := by
      rw [← map_neg]; congr 1; simp
    linarith
  -- Jensen in each variable.
  have hw0 : ∀ t ∈ range N, (0 : ℝ) ≤ (N : ℝ)⁻¹ := fun _ _ => by positivity
  have hw1 : ∑ _t ∈ range N, (N : ℝ)⁻¹ = 1 := by
    rw [sum_const, card_range, nsmul_eq_mul, mul_inv_cancel₀ hNr.ne']
  have hfst : ((N : ℝ)⁻¹ • ∑ t ∈ range N, w t).1 = ∑ t ∈ range N, (N : ℝ)⁻¹ • (w t).1 := by
    rw [Prod.smul_fst, Prod.fst_sum, smul_sum]
  have hsnd : ((N : ℝ)⁻¹ • ∑ t ∈ range N, w t).2 = ∑ t ∈ range N, (N : ℝ)⁻¹ • (w t).2 := by
    rw [Prod.smul_snd, Prod.snd_sum, smul_sum]
  have hj1 : f (∑ t ∈ range N, (N : ℝ)⁻¹ • (w t).1, y) ≤
      ∑ t ∈ range N, (N : ℝ)⁻¹ * f ((w t).1, y) := by
    have := (hfx y hy).map_sum_le (t := range N) (w := fun _ => (N : ℝ)⁻¹)
      (p := fun t => (w t).1) hw0 hw1 (fun t _ => (hw t).1)
    simpa [smul_eq_mul] using this
  have hj2 : ∑ t ∈ range N, (N : ℝ)⁻¹ * f (x, (w t).2) ≤
      f (x, ∑ t ∈ range N, (N : ℝ)⁻¹ • (w t).2) := by
    have := (hfy x hx).le_map_sum (t := range N) (w := fun _ => (N : ℝ)⁻¹)
      (p := fun t => (w t).2) hw0 hw1 (fun t _ => (hw t).2)
    simpa [smul_eq_mul] using this
  rw [hfst, hsnd]
  have havg : ∑ t ∈ range N, (N : ℝ)⁻¹ * f ((w t).1, y) -
      ∑ t ∈ range N, (N : ℝ)⁻¹ * f (x, (w t).2) =
      (∑ t ∈ range N, (f ((w t).1, y) - f (x, (w t).2))) / N := by
    rw [← mul_sum, ← mul_sum, ← mul_sub, ← sum_sub_distrib, inv_mul_eq_div]
  have hle : (∑ t ∈ range N, (f ((w t).1, y) - f (x, (w t).2))) / N ≤
      bregman ω ω' (z 0) (x, y) / (γ * N) := by
    rw [div_le_div_iff₀ hNr (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left (sum_le_sum fun t (_ : t ∈ range N) => hgap t) hγ.le
    have h2 := mul_le_mul_of_nonneg_right (h1.trans hsum) hNr.le
    calc (∑ t ∈ range N, (f ((w t).1, y) - f (x, (w t).2))) * (γ * N)
        = γ * (∑ t ∈ range N, (f ((w t).1, y) - f (x, (w t).2))) * N := by ring
      _ ≤ bregman ω ω' (z 0) (x, y) * N := h2
  linarith

/-- **The `O(1/N)` saddle-point accuracy of mirror-prox with the step `α / (√2 L)`.** In the setting
of `mirror_prox_saddle_le` with `L > 0`, the step `γ = α / (√2 L)` and `V_{z₀} ≤ Θ` on `X × Y`,
`f(x̄_N, y) - f(x, ȳ_N) ≤ √2 Θ L / (α N)` for all `x ∈ X`, `y ∈ Y`; taking the supremum over `y`
and the infimum over `x` gives the accuracy `ε_f(z̄_N) ≤ √2 Θ L / (α N)`.
This is the efficiency estimate (3.10) of Theorem 3.2 in A. Nemirovski, *Prox-method with rate of
convergence O(1/t) for variational inequalities with Lipschitz continuous monotone operators and
smooth convex-concave saddle point problems*, SIAM J. Optim. 15 (2004), with the step (3.2). -/
theorem mirror_prox_saddle_le_sqrt_two (ω : Ex × Ey → ℝ) (ω' : Ex × Ey → (Ex × Ey) →L[ℝ] ℝ)
    {α L Θ : ℝ} (hα : 0 < α) (hL : 0 < L) {X : Set Ex} {Y : Set Ey}
    (hsc : ∀ p ∈ X ×ˢ Y, ∀ q ∈ X ×ˢ Y, α / 2 * ‖q - p‖ ^ 2 ≤ bregman ω ω' p q)
    {f : Ex × Ey → ℝ} (hfx : ∀ y ∈ Y, ConvexOn ℝ X fun x => f (x, y))
    (hfy : ∀ x ∈ X, ConcaveOn ℝ Y fun y => f (x, y))
    (F : Ex × Ey → (Ex × Ey) →L[ℝ] ℝ) (Fx : Ex × Ey → Ex →L[ℝ] ℝ) (Fy : Ex × Ey → Ey →L[ℝ] ℝ)
    (hF : ∀ p q, F p q = Fx p q.1 - Fy p q.2)
    (hgx : ∀ p ∈ X ×ˢ Y, ∀ x' ∈ X, f p + Fx p (x' - p.1) ≤ f (x', p.2))
    (hgy : ∀ p ∈ X ×ˢ Y, ∀ y' ∈ Y, f (p.1, y') ≤ f p + Fy p (y' - p.2))
    (hlip : ∀ a ∈ X ×ˢ Y, ∀ b ∈ X ×ˢ Y, ‖F a - F b‖ ≤ L * ‖a - b‖)
    {z w : ℕ → Ex × Ey} (hz : ∀ t, z t ∈ X ×ˢ Y) (hw : ∀ t, w t ∈ X ×ˢ Y)
    (hoptw : ∀ t, ∀ u ∈ X ×ˢ Y,
      0 ≤ ((α / (√2 * L)) • F (z t) - ω' (z t) + ω' (w t)) (u - w t))
    (hoptz : ∀ t, ∀ u ∈ X ×ˢ Y,
      0 ≤ ((α / (√2 * L)) • F (w t) - ω' (z t) + ω' (z (t + 1))) (u - z (t + 1)))
    (hΘ : ∀ u ∈ X ×ˢ Y, bregman ω ω' (z 0) u ≤ Θ) {N : ℕ} (hN : 0 < N) {x : Ex} {y : Ey}
    (hx : x ∈ X) (hy : y ∈ Y) :
    f (((N : ℝ)⁻¹ • ∑ t ∈ range N, w t).1, y) - f (x, ((N : ℝ)⁻¹ • ∑ t ∈ range N, w t).2) ≤
      √2 * Θ * L / (α * N) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs2 : (1 : ℝ) ≤ √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hγ : 0 < α / (√2 * L) := by positivity
  have hγL : α / (√2 * L) * L ≤ α := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs2 (mul_pos hα hL).le]
  refine (mirror_prox_saddle_le ω ω' hα hγ hγL hsc hfx hfy F Fx Fy hF hgx hgy hlip hz hw
    hoptw hoptz hN hx hy).trans ?_
  have hval : Θ / (α / (√2 * L) * N) = √2 * Θ * L / (α * N) := by field_simp
  rw [← hval]
  exact div_le_div_of_nonneg_right (hΘ _ ⟨hx, hy⟩) (by positivity)

end MathlibExt.Analysis.Convex.MirrorProx
