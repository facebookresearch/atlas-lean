/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.MirrorDescent

/-!
# The mirror-prox method

For a variational inequality on a convex set `Z` with a monotone operator `F : E → (E →L[ℝ] ℝ)`
that is `L`-Lipschitz from `‖·‖` to the dual norm, the mirror-prox method of A. Nemirovski
(*Prox-method with rate of convergence O(1/t) for variational inequalities with Lipschitz
continuous monotone operators and smooth convex-concave saddle point problems*, SIAM J. Optim.
15(1) (2004), 229–251) makes two prox steps from the current point `z_t`, with the Bregman
divergence `V` of a distance-generating function `ω` (`MirrorDescent.bregman`):
`w_t = argmin_{u ∈ Z} {γ F(z_t) u + V_{z_t}(u)}` and
`z_{t+1} = argmin_{u ∈ Z} {γ F(w_t) u + V_{z_t}(u)}`. In the Euclidean setup it is Korpelevich's
extragradient method. Its ergodic average `w̄_N` of the `w_t` solves the variational inequality to
accuracy `O(1/N)`, against `O(1/√N)` for black-box nonsmooth methods.

Main results (with strong convexity modulus `α > 0`):

* `mirror_prox_step_le`: the one-step inequality
  `γ F(w) (w - u) ≤ V_z(u) - V_{z⁺}(u)` when `γ L ≤ α` (from Lemma 3.1 of the source).
* `mirror_prox_average_le`: `F(u) (w̄_N - u) ≤ V_{z_0}(u) / (γ N)` for all `u ∈ Z`.
* `mirror_prox_average_le_sqrt_two`: with the source's step `γ = α / (√2 L)`, the bound
  `max_{u ∈ Z} F(u) (w̄_N - u) ≤ √2 Θ L / (α N)` of (3.9), Theorem 3.2.
-/

@[expose] public section

open Finset

namespace MathlibExt.Analysis.Convex.MirrorProx

open MathlibExt.Analysis.Convex.MirrorDescent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **One-step inequality of mirror-prox.** Let `α > 0`, `γ ≥ 0`, and let `ω` be `α`-strongly
convex on `Z` in the Bregman form `V_x(u) ≥ (α/2) ‖u - x‖²`. Let `z, w, z⁺ ∈ Z` where `w` and
`z⁺` satisfy the optimality conditions of the prox steps
`w = argmin_{u ∈ Z} {γ F(z) u + V_z(u)}` and `z⁺ = argmin_{u ∈ Z} {γ F(w) u + V_z(u)}`, and
let `γ ‖F(z) - F(w)‖_* ≤ α ‖z - w‖` (which holds when `F` is `L`-Lipschitz and `γ L ≤ α`).
Then for every `u ∈ Z`, `γ F(w) (w - u) ≤ V_z(u) - V_{z⁺}(u)`.
This is Lemma 3.1, (3.7.b)–(3.7.d), of A. Nemirovski, *Prox-method with rate of convergence
O(1/t) for variational inequalities with Lipschitz continuous monotone operators and smooth
convex-concave saddle point problems*, SIAM J. Optim. 15 (2004), with `U = Z`, `ξ = F(z)`,
`η = F(w)`, where `H_u(z) - H_u(z⁺) = V_z(u) - V_{z⁺}(u)`; the remainder term is bounded
directly by `γ ‖F(z) - F(w)‖_* ‖w - z⁺‖ - (α/2)(‖w - z‖² + ‖w - z⁺‖²) ≤ 0` instead of through
(3.7.a), which is why `γ L ≤ α` suffices here where the source takes `γ L ≤ α / √2`. -/
theorem mirror_prox_step_le (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α γ : ℝ} (hα : 0 < α)
    (hγ : 0 ≤ γ) {Z : Set E} (hsc : ∀ x ∈ Z, ∀ u ∈ Z, α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u)
    (F : E → E →L[ℝ] ℝ) {z w zplus : E} (hz : z ∈ Z) (hw : w ∈ Z) (hzplus : zplus ∈ Z)
    (hoptw : ∀ u ∈ Z, 0 ≤ (γ • F z - ω' z + ω' w) (u - w))
    (hoptz : ∀ u ∈ Z, 0 ≤ (γ • F w - ω' z + ω' zplus) (u - zplus))
    (hlip : γ * ‖F z - F w‖ ≤ α * ‖z - w‖) {u : E} (hu : u ∈ Z) :
    γ * F w (w - u) ≤ bregman ω ω' z u - bregman ω ω' zplus u := by
  -- Three-point identities.
  have h1 := bregman_three_point ω ω' z zplus u
  have h2 := bregman_three_point ω ω' z w zplus
  have hz' := hoptz u hu
  have hw' := hoptw zplus hzplus
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul] at hz' hw'
  -- `γ F(w) (w - u) = γ F(w) (w - z⁺) + γ F(w) (z⁺ - u)`.
  have hsplit : F w (w - u) = F w (w - zplus) + F w (zplus - u) := by
    rw [← map_add]; congr 1; abel
  have hneg1 : F w (zplus - u) = -F w (u - zplus) := by rw [← map_neg, neg_sub]
  have hneg2 : F z (w - zplus) = -F z (zplus - w) := by rw [← map_neg, neg_sub]
  have hdiff : F w (w - zplus) - F z (w - zplus) = (F w - F z) (w - zplus) := by
    rw [sub_apply]
  have hdual : (F w - F z) (w - zplus) ≤ ‖F z - F w‖ * ‖w - zplus‖ := by
    calc (F w - F z) (w - zplus) ≤ |(F w - F z) (w - zplus)| := le_abs_self _
      _ = ‖(F w - F z) (w - zplus)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖F w - F z‖ * ‖w - zplus‖ := (F w - F z).le_opNorm _
      _ = ‖F z - F w‖ * ‖w - zplus‖ := by rw [norm_sub_rev]
  have hsc1 := hsc z hz w hw
  have hsc2 := hsc w hw zplus hzplus
  have hdist : ‖zplus - w‖ = ‖w - zplus‖ := norm_sub_rev _ _
  have hdist2 : ‖w - z‖ = ‖z - w‖ := norm_sub_rev _ _
  rw [hdist] at hsc2
  rw [hdist2] at hsc1
  -- `γ ‖F z - F w‖ ‖w - z⁺‖ ≤ α ‖z - w‖ ‖w - z⁺‖ ≤ (α/2)(‖z - w‖² + ‖w - z⁺‖²)`.
  have hprod : γ * (‖F z - F w‖ * ‖w - zplus‖) ≤ α * ‖z - w‖ * ‖w - zplus‖ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
  have hamgm : α * ‖z - w‖ * ‖w - zplus‖ ≤ α / 2 * ‖z - w‖ ^ 2 + α / 2 * ‖w - zplus‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z - w‖ - ‖w - zplus‖)]
  have hγd := mul_le_mul_of_nonneg_left hdual hγ
  rw [hsplit, hneg1, mul_add]
  have hd' : γ * F w (w - zplus) - γ * F z (w - zplus) = γ * (F w - F z) (w - zplus) := by
    rw [← hdiff]; ring
  rw [hneg2] at hd'
  simp only [sub_apply] at h1 h2
  simp only [mul_neg, sub_neg_eq_add] at hd' ⊢
  linarith [hd', h1, h2, hz', hw', hγd, hprod, hamgm, hsc1, hsc2]

/-- **Ergodic rate of mirror-prox.** Let `α > 0`, `0 < γ`, `γ L ≤ α`, and let `ω` be
`α`-strongly convex on `Z` in the Bregman form `V_x(u) ≥ (α/2) ‖u - x‖²`. Let
`F : E → (E →L[ℝ] ℝ)` be monotone on `Z` (`(F a - F b) (a - b) ≥ 0`) and `L`-Lipschitz from
`‖·‖` to the dual norm on `Z`. Let `z t, w t ∈ Z` satisfy, for every `t`, the optimality
conditions of the prox steps `w_t = argmin_{u ∈ Z} {γ F(z_t) u + V_{z_t}(u)}` and
`z_{t+1} = argmin_{u ∈ Z} {γ F(w_t) u + V_{z_t}(u)}`. Then for `N ≥ 1` the average
`w̄_N = N⁻¹ ∑_{t<N} w_t` satisfies `F(u) (w̄_N - u) ≤ V_{z_0}(u) / (γ N)` for every `u ∈ Z`.
This is Proposition 2.2(ii), (2.13), of A. Nemirovski, *Prox-method with rate of convergence
O(1/t) for variational inequalities with Lipschitz continuous monotone operators and smooth
convex-concave saddle point problems*, SIAM J. Optim. 15 (2004), with `ε_t = 0` (guaranteed by
Lemma 3.1) and constant steps, for the iteration that always performs both prox steps (the
iteration (4.2) of Section 4, with a constant step), here for every `γ` with `γ L ≤ α`. -/
theorem mirror_prox_average_le (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α γ L : ℝ} (hα : 0 < α)
    (hγ : 0 < γ) (hγL : γ * L ≤ α) {Z : Set E}
    (hsc : ∀ x ∈ Z, ∀ u ∈ Z, α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u)
    (F : E → E →L[ℝ] ℝ) (hmono : ∀ a ∈ Z, ∀ b ∈ Z, 0 ≤ (F a - F b) (a - b))
    (hlip : ∀ a ∈ Z, ∀ b ∈ Z, ‖F a - F b‖ ≤ L * ‖a - b‖)
    {z w : ℕ → E} (hz : ∀ t, z t ∈ Z) (hw : ∀ t, w t ∈ Z)
    (hoptw : ∀ t, ∀ u ∈ Z, 0 ≤ (γ • F (z t) - ω' (z t) + ω' (w t)) (u - w t))
    (hoptz : ∀ t, ∀ u ∈ Z, 0 ≤ (γ • F (w t) - ω' (z t) + ω' (z (t + 1))) (u - z (t + 1)))
    {N : ℕ} (hN : 0 < N) {u : E} (hu : u ∈ Z) :
    F u ((N : ℝ)⁻¹ • ∑ t ∈ range N, w t - u) ≤ bregman ω ω' (z 0) u / (γ * N) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hstep : ∀ t, γ * F (w t) (w t - u) ≤ bregman ω ω' (z t) u - bregman ω ω' (z (t + 1)) u := by
    intro t
    refine mirror_prox_step_le ω ω' hα hγ.le hsc F (hz t) (hw t) (hz (t + 1)) (hoptw t)
      (hoptz t) ?_ hu
    calc γ * ‖F (z t) - F (w t)‖ ≤ γ * (L * ‖z t - w t‖) :=
          mul_le_mul_of_nonneg_left (hlip _ (hz t) _ (hw t)) hγ.le
      _ = (γ * L) * ‖z t - w t‖ := by ring
      _ ≤ α * ‖z t - w t‖ := mul_le_mul_of_nonneg_right hγL (norm_nonneg _)
  -- Monotonicity: `F(u) (w_t - u) ≤ F(w_t) (w_t - u)`.
  have hmon : ∀ t, F u (w t - u) ≤ F (w t) (w t - u) := by
    intro t
    have := hmono _ (hw t) _ hu
    rw [sub_apply] at this
    linarith
  have htel : ∀ n, γ * ∑ t ∈ range n, F u (w t - u) ≤
      bregman ω ω' (z 0) u - bregman ω ω' (z n) u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, mul_add]
      have := mul_le_mul_of_nonneg_left (hmon n) hγ.le
      linarith [hstep n]
  have hlast : 0 ≤ bregman ω ω' (z N) u := le_trans (by positivity) (hsc _ (hz N) _ hu)
  have hsum : ∑ t ∈ range N, F u (w t - u) = F u (∑ t ∈ range N, w t) - N * F u u := by
    rw [← map_sum (F u), sum_sub_distrib, map_sub, sum_const, card_range, map_nsmul,
      nsmul_eq_mul]
  have havg : F u ((N : ℝ)⁻¹ • ∑ t ∈ range N, w t - u) =
      (∑ t ∈ range N, F u (w t - u)) / N := by
    rw [hsum, map_sub, map_smul, smul_eq_mul]
    field_simp
  rw [havg, div_le_div_iff₀ hNr (by positivity)]
  nlinarith [htel N]

/-- **The `O(1/N)` rate of mirror-prox with the step `α / (√2 L)`.** In the setting of
`mirror_prox_average_le` with `L > 0` and the step `γ = α / (√2 L)`, if
`V_{z_0}(u) ≤ Θ` for all `u ∈ Z`, then the accuracy of the average `w̄_N` as a solution of the
variational inequality satisfies `max_{u ∈ Z} F(u) (w̄_N - u) ≤ √2 Θ L / (α N)`.
This is the efficiency estimate (3.9) of Theorem 3.2 in A. Nemirovski, *Prox-method with rate of
convergence O(1/t) for variational inequalities with Lipschitz continuous monotone operators and
smooth convex-concave saddle point problems*, SIAM J. Optim. 15 (2004), where `Θ = Θ(z_0)` and
the step is (3.2); the saddle-point form (3.10) is `mirror_prox_saddle_le_sqrt_two`. -/
theorem mirror_prox_average_le_sqrt_two (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α L Θ : ℝ}
    (hα : 0 < α) (hL : 0 < L) {Z : Set E}
    (hsc : ∀ x ∈ Z, ∀ u ∈ Z, α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u)
    (F : E → E →L[ℝ] ℝ) (hmono : ∀ a ∈ Z, ∀ b ∈ Z, 0 ≤ (F a - F b) (a - b))
    (hlip : ∀ a ∈ Z, ∀ b ∈ Z, ‖F a - F b‖ ≤ L * ‖a - b‖)
    {z w : ℕ → E} (hz : ∀ t, z t ∈ Z) (hw : ∀ t, w t ∈ Z)
    (hoptw : ∀ t, ∀ u ∈ Z,
      0 ≤ ((α / (√2 * L)) • F (z t) - ω' (z t) + ω' (w t)) (u - w t))
    (hoptz : ∀ t, ∀ u ∈ Z,
      0 ≤ ((α / (√2 * L)) • F (w t) - ω' (z t) + ω' (z (t + 1))) (u - z (t + 1)))
    (hΘ : ∀ u ∈ Z, bregman ω ω' (z 0) u ≤ Θ) {N : ℕ} (hN : 0 < N) {u : E} (hu : u ∈ Z) :
    F u ((N : ℝ)⁻¹ • ∑ t ∈ range N, w t - u) ≤ √2 * Θ * L / (α * N) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs2 : (1 : ℝ) ≤ √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < √2 := by positivity
  have hγ : 0 < α / (√2 * L) := by positivity
  have hγL : α / (√2 * L) * L ≤ α := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs2 (mul_pos hα hL).le]
  have h := mirror_prox_average_le ω ω' hα hγ hγL hsc F hmono hlip hz hw hoptw hoptz hN hu
  refine h.trans ?_
  have hval : Θ / (α / (√2 * L) * N) = √2 * Θ * L / (α * N) := by
    field_simp
  rw [← hval]
  exact div_le_div_of_nonneg_right (hΘ u hu) (by positivity)

end MathlibExt.Analysis.Convex.MirrorProx
