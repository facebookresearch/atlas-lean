/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Convex.OnlineGradientDescent
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Anytime online gradient descent

Projected online gradient descent with a per-round step-size schedule,
following Section 3.1 of Hazan's "Introduction to Online Convex
Optimization": with steps `η t = D / (G * √(t + 1))` the regret against
any comparator is at most `(3 / 2) * G * D * √T`. Rounds count from `t = 0`,
and the projection is abstracted as a nonexpansive map fixing the comparator.
-/

@[expose] public section

namespace Cslib.MachineLearning.OnlineGradientDescentAnytime

/-- Projected online gradient descent iterates with per-round step sizes:
`x (t + 1)` projects the gradient step from `x t` back with `proj`, using
step size `η t` at round `t`. Here `g t x` is the subgradient of the
round-`t` cost at `x`. Rounds are indexed from `t = 0`. -/
noncomputable def ogdIterVarying {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (g : ℕ → E → E) (η : ℕ → ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 => proj (ogdIterVarying proj g η x0 t - η t • g t (ogdIterVarying proj g η x0 t))

/-- Telescoping bound for weighted differences with nondecreasing weights. -/
theorem ogd_telescope_le (a w : ℕ → ℝ) (D : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (ha : ∀ t, a t ≤ D ^ 2) (hw0 : ∀ t, 0 ≤ w t)
    (hwmono : ∀ t, w t ≤ w (t + 1)) :
    ∑ t ∈ Finset.range T, (a t - a (t + 1)) * w t
      ≤ (D ^ 2 - a T) * w (T - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  clear hT
  induction n with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      apply mul_le_mul_of_nonneg_right _ (hw0 0)
      linarith [ha 0]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hmono : (D ^ 2 - a (n + 1)) * w n
          ≤ (D ^ 2 - a (n + 1)) * w (n + 1) :=
        mul_le_mul_of_nonneg_left (hwmono n) (by linarith [ha (n + 1)])
      have h1 : (D ^ 2 - a (n + 1)) * w n + (a (n + 1) - a (n + 1 + 1)) * w (n + 1)
          ≤ (D ^ 2 - a (n + 1 + 1)) * w (n + 1) := by
        linarith [hmono]
      linarith [ih, h1]

/-- Partial sums of inverse square roots are bounded by twice the root. -/
theorem ogd_inv_sqrt_sum_le (T : ℕ) :
    ∑ t ∈ Finset.range T, (1 : ℝ) / Real.sqrt ((t : ℝ) + 1)
      ≤ 2 * Real.sqrt (T : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ]
      push_cast
      have hT : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
      have hT1 : (0 : ℝ) < (T : ℝ) + 1 := by linarith
      have hsq1 : Real.sqrt ((T : ℝ) + 1) ^ 2 = (T : ℝ) + 1 :=
        Real.sq_sqrt (le_of_lt hT1)
      have hsq0 : Real.sqrt (T : ℝ) ^ 2 = (T : ℝ) := Real.sq_sqrt hT
      have hpos1 : (0 : ℝ) < Real.sqrt ((T : ℝ) + 1) := Real.sqrt_pos.mpr hT1
      have hkey : (1 : ℝ) / Real.sqrt ((T : ℝ) + 1)
          ≤ 2 * (Real.sqrt ((T : ℝ) + 1) - Real.sqrt (T : ℝ)) := by
        rw [div_le_iff₀ hpos1]
        nlinarith [hsq0, hsq1,
          sq_nonneg (Real.sqrt (T : ℝ) - Real.sqrt ((T : ℝ) + 1))]
      linarith [ih, hkey]

/-- Analytic assembly: the anytime schedule turns the varying-step
decomposition into the `(3 / 2) * G * D * √T` bound. -/
theorem ogd_anytime_assembly (D G : ℝ) (hD : 0 < D) (hG : 0 < G) (T : ℕ)
    (a c : ℕ → ℝ) (ha : ∀ t, a t ≤ D ^ 2) (ha0 : ∀ t, 0 ≤ a t)
    (hc : ∀ t, c t ≤ G ^ 2)
    (η : ℕ → ℝ) (hη : ∀ t, η t = D / (G * Real.sqrt ((t : ℝ) + 1))) :
    ∑ t ∈ Finset.range T, ((a t - a (t + 1)) / (2 * η t) + (η t / 2) * c t)
      ≤ (3 / 2) * G * D * Real.sqrt (T : ℝ) := by
  rcases eq_or_ne T 0 with rfl | hT0
  · simp
  · have hT : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT0
    have hηpos : ∀ t, 0 < η t := by
      intro t
      rw [hη t]
      have h1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr h1
      positivity
    have hηmono : ∀ t, η (t + 1) ≤ η t := by
      intro t
      rw [hη t, hη (t + 1)]
      have hsqrt : Real.sqrt ((t : ℝ) + 1)
          ≤ Real.sqrt (((t + 1 : ℕ) : ℝ) + 1) := by
        apply Real.sqrt_le_sqrt
        rw [Nat.cast_add, Nat.cast_one]
        linarith
      have h1 : (0 : ℝ) < G * Real.sqrt ((t : ℝ) + 1) := by
        have hs : (0 : ℝ) < Real.sqrt ((t : ℝ) + 1) :=
          Real.sqrt_pos.mpr (by positivity)
        positivity
      have h2 : (0 : ℝ) < G * Real.sqrt (((t + 1 : ℕ) : ℝ) + 1) := by
        have hs : (0 : ℝ) < Real.sqrt (((t + 1 : ℕ) : ℝ) + 1) :=
          Real.sqrt_pos.mpr (by positivity)
        positivity
      have hXY : G * Real.sqrt ((t : ℝ) + 1)
          ≤ G * Real.sqrt (((t + 1 : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hsqrt hG.le
      have hdiv : 1 / (G * Real.sqrt (((t + 1 : ℕ) : ℝ) + 1))
          ≤ 1 / (G * Real.sqrt ((t : ℝ) + 1)) :=
        one_div_le_one_div_of_le h1 hXY
      calc D / (G * Real.sqrt (((t + 1 : ℕ) : ℝ) + 1))
          = D * (1 / (G * Real.sqrt (((t + 1 : ℕ) : ℝ) + 1))) :=
            div_eq_mul_one_div _ _
        _ ≤ D * (1 / (G * Real.sqrt ((t : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hdiv hD.le
        _ = D / (G * Real.sqrt ((t : ℝ) + 1)) := (div_eq_mul_one_div _ _).symm
    set w : ℕ → ℝ := fun t => 1 / (2 * η t) with hw
    have hw0 : ∀ t, 0 ≤ w t := by
      intro t
      have h := hηpos t
      simp only [hw]
      positivity
    have hwmono : ∀ t, w t ≤ w (t + 1) := by
      intro t
      have hle : 2 * η (t + 1) ≤ 2 * η t := by
        have h := hηmono t
        linarith
      have hpos : (0 : ℝ) < 2 * η (t + 1) := by
        have h := hηpos (t + 1)
        linarith
      simp only [hw]
      exact one_div_le_one_div_of_le hpos hle
    have htel := ogd_telescope_le a w D T hT ha hw0 hwmono
    have hsplit : ∑ t ∈ Finset.range T, ((a t - a (t + 1)) / (2 * η t)
          + (η t / 2) * c t)
        = ∑ t ∈ Finset.range T, (a t - a (t + 1)) * w t
          + ∑ t ∈ Finset.range T, (η t / 2) * c t := by
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      simp only [hw]
      rw [div_eq_mul_one_div]
    have hpart2 : ∑ t ∈ Finset.range T, (η t / 2) * c t
        ≤ G * D * Real.sqrt (T : ℝ) := by
      have hle : ∀ t ∈ Finset.range T, (η t / 2) * c t
          ≤ (G * D / 2) * (1 / Real.sqrt ((t : ℝ) + 1)) := by
        intro t _
        have h1 : (η t / 2) * c t ≤ (η t / 2) * G ^ 2 :=
          mul_le_mul_of_nonneg_left (hc t) (by
            have h := hηpos t
            linarith)
        have h2 : (η t / 2) * G ^ 2
            = (G * D / 2) * (1 / Real.sqrt ((t : ℝ) + 1)) := by
          rw [hη t]
          have hGne : (G : ℝ) ≠ 0 := ne_of_gt hG
          have hsne : Real.sqrt ((t : ℝ) + 1) ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.mpr (by positivity))
          have hprod : G * Real.sqrt ((t : ℝ) + 1) ≠ 0 :=
            mul_ne_zero hGne hsne
          field_simp
        rw [← h2]
        exact h1
      calc ∑ t ∈ Finset.range T, (η t / 2) * c t
          ≤ ∑ t ∈ Finset.range T, (G * D / 2) * (1 / Real.sqrt ((t : ℝ) + 1)) :=
            Finset.sum_le_sum hle
        _ = (G * D / 2) * ∑ t ∈ Finset.range T, 1 / Real.sqrt ((t : ℝ) + 1) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (G * D / 2) * (2 * Real.sqrt (T : ℝ)) :=
            mul_le_mul_of_nonneg_left (ogd_inv_sqrt_sum_le T) (by positivity)
        _ = G * D * Real.sqrt (T : ℝ) := by ring
    have hTsub : ((T - 1 : ℕ) : ℝ) + 1 = (T : ℝ) := by
      rw [Nat.cast_sub hT, Nat.cast_one]
      ring
    have hwT : w (T - 1) = G * Real.sqrt (T : ℝ) / (2 * D) := by
      simp only [hw]
      rw [hη (T - 1), hTsub]
      have hDne : (D : ℝ) ≠ 0 := ne_of_gt hD
      have hGne : (G : ℝ) ≠ 0 := ne_of_gt hG
      have hsT : Real.sqrt (T : ℝ) ≠ 0 := by
        apply ne_of_gt
        apply Real.sqrt_pos.mpr
        have h0T : 0 < T := by omega
        have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast h0T
        linarith
      have hprod : G * Real.sqrt (T : ℝ) ≠ 0 := mul_ne_zero hGne hsT
      have hfrac : D / (G * Real.sqrt (T : ℝ)) ≠ 0 := div_ne_zero hDne hprod
      have hden : 2 * (D / (G * Real.sqrt (T : ℝ))) ≠ 0 :=
        mul_ne_zero two_ne_zero hfrac
      field_simp
    have hpart1 : ∑ t ∈ Finset.range T, (a t - a (t + 1)) * w t
        ≤ (G * D / 2) * Real.sqrt (T : ℝ) := by
      have h1 : (D ^ 2 - a T) * w (T - 1) ≤ D ^ 2 * w (T - 1) :=
        mul_le_mul_of_nonneg_right (by linarith [ha0 T]) (hw0 _)
      calc ∑ t ∈ Finset.range T, (a t - a (t + 1)) * w t
          ≤ (D ^ 2 - a T) * w (T - 1) := htel
        _ ≤ D ^ 2 * w (T - 1) := h1
        _ = (G * D / 2) * Real.sqrt (T : ℝ) := by
            have hDne : (D : ℝ) ≠ 0 := ne_of_gt hD
            have h2D : (2 : ℝ) * D ≠ 0 := mul_ne_zero two_ne_zero hDne
            rw [hwT]
            field_simp
    rw [hsplit]
    calc ∑ t ∈ Finset.range T, (a t - a (t + 1)) * w t
          + ∑ t ∈ Finset.range T, (η t / 2) * c t
        ≤ (G * D / 2) * Real.sqrt (T : ℝ) + G * D * Real.sqrt (T : ℝ) :=
          add_le_add hpart1 hpart2
      _ = (3 / 2) * G * D * Real.sqrt (T : ℝ) := by ring

/-- One-round descent: the subgradient inner product is bounded by the
telescoping potential drop plus a squared-norm term. -/
theorem ogd_descent_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (hproj : LipschitzWith 1 proj)
    (x xstar gt : E) (hprojstar : proj xstar = xstar)
    (ηt : ℝ) (hηt : 0 < ηt) :
    @inner ℝ E _ gt (x - xstar)
      ≤ (‖x - xstar‖ ^ 2 - ‖proj (x - ηt • gt) - xstar‖ ^ 2) / (2 * ηt)
        + (ηt / 2) * ‖gt‖ ^ 2 := by
  have hexp : ‖x - ηt • gt - xstar‖ ^ 2
      = ‖x - xstar‖ ^ 2 - 2 * ηt * @inner ℝ E _ gt (x - xstar)
        + ηt ^ 2 * ‖gt‖ ^ 2 := by
    have h1 : x - ηt • gt - xstar = (x - xstar) - ηt • gt := by abel
    rw [h1, norm_sub_sq_real]
    simp only [inner_sub_left, inner_smul_right, inner_sub_right,
      norm_smul, Real.norm_eq_abs, sq_abs, mul_pow,
      real_inner_comm x gt, real_inner_comm xstar gt]
    ring
  have hlip : ‖proj (x - ηt • gt) - xstar‖ ≤ ‖x - ηt • gt - xstar‖ := by
    have h := hproj.dist_le_mul (x - ηt • gt) xstar
    rw [hprojstar, dist_eq_norm, dist_eq_norm] at h
    simpa using h
  have hsq : ‖proj (x - ηt • gt) - xstar‖ ^ 2 ≤ ‖x - ηt • gt - xstar‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hlip 2
  have h2η : (0 : ℝ) < 2 * ηt := by linarith
  have hkey : 2 * ηt * @inner ℝ E _ gt (x - xstar)
      ≤ ‖x - xstar‖ ^ 2 - ‖proj (x - ηt • gt) - xstar‖ ^ 2
        + ηt ^ 2 * ‖gt‖ ^ 2 := by
    rw [hexp] at hsq
    linarith [hsq]
  have hne : (2 : ℝ) * ηt ≠ 0 := ne_of_gt h2η
  have heq : (‖x - xstar‖ ^ 2 - ‖proj (x - ηt • gt) - xstar‖ ^ 2) / (2 * ηt)
        + (ηt / 2) * ‖gt‖ ^ 2
      = (‖x - xstar‖ ^ 2 - ‖proj (x - ηt • gt) - xstar‖ ^ 2
        + ηt ^ 2 * ‖gt‖ ^ 2) / (2 * ηt) := by
    field_simp
  rw [heq, le_div_iff₀ h2η]
  linarith [hkey]

/-- Constant step-size schedules recover the fixed-step iterates. -/
theorem ogdIterVarying_const {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (g : ℕ → E → E) (η : ℝ) (x0 : E) :
    ogdIterVarying proj g (fun _ => η) x0 = ogdIter proj g η x0 := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => simp [ogdIterVarying, ogdIter, ih]

/-- Varying-step regret decomposition: the regret is bounded by the summed
per-round descent inequalities, before any schedule is chosen. -/
theorem ogd_regret_varying {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (f : ℕ → E → ℝ) (g : ℕ → E → E) (η : ℕ → ℝ)
    (hη : ∀ t, 0 < η t) (hproj : LipschitzWith 1 proj)
    (xstar : E) (hprojstar : proj xstar = xstar)
    (hsub : ∀ (t : ℕ) (x : E),
      f t x + @inner ℝ E _ (g t x) (xstar - x) ≤ f t xstar)
    (x0 : E) (T : ℕ) :
    ∑ t ∈ Finset.range T, (f t (ogdIterVarying proj g η x0 t) - f t xstar)
      ≤ ∑ t ∈ Finset.range T, ((‖ogdIterVarying proj g η x0 t - xstar‖ ^ 2
        - ‖ogdIterVarying proj g η x0 (t + 1) - xstar‖ ^ 2) / (2 * η t)
        + (η t / 2) * ‖g t (ogdIterVarying proj g η x0 t)‖ ^ 2) := by
  apply Finset.sum_le_sum
  intro t _
  have hsubt := hsub t (ogdIterVarying proj g η x0 t)
  have hdesc := ogd_descent_step proj hproj (ogdIterVarying proj g η x0 t)
    xstar (g t (ogdIterVarying proj g η x0 t)) hprojstar (η t) (hη t)
  have hstep : ogdIterVarying proj g η x0 (t + 1)
      = proj (ogdIterVarying proj g η x0 t
        - η t • g t (ogdIterVarying proj g η x0 t)) := by
    simp only [ogdIterVarying]
  rw [hstep]
  have hinner : @inner ℝ E _ (g t (ogdIterVarying proj g η x0 t))
      (xstar - ogdIterVarying proj g η x0 t)
      = - @inner ℝ E _ (g t (ogdIterVarying proj g η x0 t))
        (ogdIterVarying proj g η x0 t - xstar) := by
    have hns : xstar - ogdIterVarying proj g η x0 t
        = - (ogdIterVarying proj g η x0 t - xstar) := by abel
    rw [hns, inner_neg_right]
  have hle : f t (ogdIterVarying proj g η x0 t) - f t xstar
      ≤ @inner ℝ E _ (g t (ogdIterVarying proj g η x0 t))
        (ogdIterVarying proj g η x0 t - xstar) := by
    linarith [hsubt, hinner]
  exact hle.trans hdesc

/-- Anytime regret bound: with steps `η t = D / (G * √(t + 1))`, the regret
against `xstar` over `T` rounds is at most `(3 / 2) * G * D * √T`. -/
theorem ogd_regret_anytime {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (f : ℕ → E → ℝ) (g : ℕ → E → E)
    (D G : ℝ) (hD : 0 < D) (hG : 0 < G) (hproj : LipschitzWith 1 proj)
    (xstar : E) (hprojstar : proj xstar = xstar)
    (hsub : ∀ (t : ℕ) (x : E),
      f t x + @inner ℝ E _ (g t x) (xstar - x) ≤ f t xstar)
    (x0 : E) (T : ℕ)
    (hDiam : ∀ t, ‖ogdIterVarying proj g
      (fun t => D / (G * Real.sqrt ((t : ℝ) + 1))) x0 t - xstar‖ ≤ D)
    (hGrad : ∀ t, ‖g t (ogdIterVarying proj g
      (fun t => D / (G * Real.sqrt ((t : ℝ) + 1))) x0 t)‖ ≤ G) :
    ∑ t ∈ Finset.range T, (f t (ogdIterVarying proj g
      (fun t => D / (G * Real.sqrt ((t : ℝ) + 1))) x0 t) - f t xstar)
      ≤ (3 / 2) * G * D * Real.sqrt (T : ℝ) := by
  have hηpos : ∀ (t : ℕ), 0 < (fun (t : ℕ) =>
      D / (G * Real.sqrt ((t : ℝ) + 1))) t := by
    intro t
    have h1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr h1
    positivity
  have hvar := ogd_regret_varying proj f g
    (fun (t : ℕ) => D / (G * Real.sqrt ((t : ℝ) + 1))) hηpos hproj xstar
    hprojstar hsub x0 T
  have ha : ∀ (t : ℕ), (fun (t : ℕ) => ‖ogdIterVarying proj g
      (fun (t : ℕ) => D / (G * Real.sqrt ((t : ℝ) + 1))) x0 t - xstar‖ ^ 2) t
      ≤ D ^ 2 := by
    intro t
    exact pow_le_pow_left₀ (norm_nonneg _) (hDiam t) 2
  have ha0 : ∀ (t : ℕ), 0 ≤ (fun (t : ℕ) => ‖ogdIterVarying proj g
      (fun (t : ℕ) => D / (G * Real.sqrt ((t : ℝ) + 1))) x0 t - xstar‖ ^ 2)
      t := by
    intro t
    exact sq_nonneg _
  have hc : ∀ (t : ℕ), (fun (t : ℕ) => ‖g t (ogdIterVarying proj g
      (fun (t : ℕ) => D / (G * Real.sqrt ((t : ℝ) + 1))) x0 t)‖ ^ 2) t
      ≤ G ^ 2 := by
    intro t
    exact pow_le_pow_left₀ (norm_nonneg _) (hGrad t) 2
  have hasm := ogd_anytime_assembly D G hD hG T
    (fun (t : ℕ) => ‖ogdIterVarying proj g
      (fun (t : ℕ) => D / (G * Real.sqrt ((t : ℝ) + 1))) x0 t - xstar‖ ^ 2)
    (fun (t : ℕ) => ‖g t (ogdIterVarying proj g
      (fun (t : ℕ) => D / (G * Real.sqrt ((t : ℝ) + 1))) x0 t)‖ ^ 2)
    ha ha0 hc (fun (t : ℕ) => D / (G * Real.sqrt ((t : ℝ) + 1)))
    (fun t => rfl)
  exact hvar.trans hasm

end Cslib.MachineLearning.OnlineGradientDescentAnytime
