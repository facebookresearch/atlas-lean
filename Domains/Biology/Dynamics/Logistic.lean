/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The logistic growth equation

The logistic (Verhulst) equation `x' = r x (1 - x / K)` with growth rate `r`, carrying
capacity `K > 0` and initial size `x 0 = x₀` has the explicit solution
`x(t) = K x₀ e^{r t} / (K + x₀ (e^{r t} - 1))`. This file proves that this function solves the
equation wherever its denominator is nonzero (all real parameters), that it is the unique
solution on every interval `[0, T]` in the biological domain (`K > 0`, `x₀ > 0`, `r ≥ 0`), that
`x(t) → K` as `t → ∞` for `r > 0`, and that `x(t) → x₀ e^{r t}` (exponential growth) as
`K → ∞`.

For a frequency (`K = 1`) the log-odds grow linearly, `logit x(t) = logit x₀ + r t`, so the
deterministic transit time from `a` to `1 - a` is exactly `(2 / r) log((1 - a) / a)`; from
`1 / (2N)` to `1 - 1 / (2N)` it is `(2 / r) log(2N - 1)`. (The often quoted `(2 / s) log(2Ns)`
is a stochastic, establishment-conditioned approximation, not this deterministic time.)

Logistic growth is the model fitted to tumor-burden trajectories in Gruber et al. (2019).

## Main results

* `MathlibExt.Biology.Dynamics.Logistic.logistic`: the explicit solution.
* `hasDerivAt_logistic`, `logistic_zero`: it solves the initial value problem.
* `eqOn_logistic_of_hasDerivWithinAt`: uniqueness on `[0, T]`.
* `tendsto_logistic_atTop`: convergence to the carrying capacity.
* `tendsto_logistic_carryingCapacity_atTop`: the exponential limit `K → ∞`.
* `logit_logistic`, `logistic_transitTime`, `logistic_transitTime_twoN`: log-odds linearity
  and the exact transit times.

## References

* P.-F. Verhulst, *Notice sur la loi que la population suit dans son accroissement*,
  Correspondance mathématique et physique 10 (1838) 113–121.
* M. Gruber et al., *Growth dynamics in naturally progressing chronic lymphocytic leukaemia*,
  Nature 570 (2019) 474–479.
-/

@[expose] public section

open Real Filter Set
open scoped Topology

namespace MathlibExt.Biology.Dynamics.Logistic

/-- Explicit solution of the logistic equation `x' = r x (1 - x / K)` with `x 0 = x₀`:
`K x₀ e^{r t} / (K + x₀ (e^{r t} - 1))`. -/
noncomputable def logistic (r K x₀ t : ℝ) : ℝ :=
  K * x₀ * exp (r * t) / (K + x₀ * (exp (r * t) - 1))

/-- The logistic solution starts at `x₀` (for `K ≠ 0`). -/
theorem logistic_zero {r K : ℝ} (x₀ : ℝ) (hK : K ≠ 0) : logistic r K x₀ 0 = x₀ := by
  simp [logistic, hK]

/-- In the biological domain (`K > 0`, `x₀ > 0`, `r t ≥ 0`, or `x₀ ≤ K`) the denominator of the
logistic solution is positive. -/
theorem logistic_denom_pos {r K x₀ t : ℝ} (hK : 0 < K) (hx₀ : 0 < x₀)
    (h : 0 ≤ r * t ∨ x₀ ≤ K) : 0 < K + x₀ * (exp (r * t) - 1) := by
  rcases h with h | h
  · have : 0 ≤ exp (r * t) - 1 := by linarith [add_one_le_exp (r * t)]
    nlinarith
  · nlinarith [exp_pos (r * t)]

/-- **The explicit solution solves the logistic equation**: wherever the denominator
`K + x₀ (e^{r t} - 1)` is nonzero, `x' = r x (1 - x / K)` (all real parameters, `K ≠ 0`). -/
theorem hasDerivAt_logistic {r K x₀ t : ℝ} (hK : K ≠ 0)
    (hden : K + x₀ * (exp (r * t) - 1) ≠ 0) :
    HasDerivAt (logistic r K x₀)
      (r * logistic r K x₀ t * (1 - logistic r K x₀ t / K)) t := by
  have he : HasDerivAt (fun s => exp (r * s)) (exp (r * t) * r) t := by
    simpa using ((hasDerivAt_id t).const_mul r).exp
  have hnum : HasDerivAt (fun s => K * x₀ * exp (r * s)) (K * x₀ * (exp (r * t) * r)) t :=
    he.const_mul _
  have hd : HasDerivAt (fun s => K + x₀ * (exp (r * s) - 1)) (x₀ * (exp (r * t) * r)) t := by
    simpa using ((he.sub_const 1).const_mul x₀).const_add K
  refine (hnum.div hd hden).congr_deriv ?_
  simp only [logistic]
  field_simp

/-- **Uniqueness of the logistic solution** on `[0, T]`: in the biological domain
(`K > 0`, `x₀ > 0`, `r ≥ 0`), any function continuous on `[0, T]`, with right derivative
`r x (1 - x / K)` on `[0, T)` and `x 0 = x₀`, equals the explicit solution on `[0, T]`. -/
theorem eqOn_logistic_of_hasDerivWithinAt {r K x₀ T : ℝ} (hK : 0 < K) (hx₀ : 0 < x₀)
    (hr : 0 ≤ r) {x : ℝ → ℝ} (hc : ContinuousOn x (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (r * x t * (1 - x t / K)) (Ici t) t)
    (h0 : x 0 = x₀) : EqOn x (logistic r K x₀) (Icc 0 T) := by
  set g := logistic r K x₀ with hg
  have hden : ∀ t, 0 ≤ t → 0 < K + x₀ * (exp (r * t) - 1) := fun t ht =>
    logistic_denom_pos hK hx₀ (Or.inl (mul_nonneg hr ht))
  have hgd : ∀ t, 0 ≤ t → HasDerivAt g (r * g t * (1 - g t / K)) t := fun t ht =>
    hasDerivAt_logistic hK.ne' (hden t ht).ne'
  have hgc : ContinuousOn g (Icc 0 T) := fun t ht => (hgd t ht.1).continuousAt.continuousWithinAt
  obtain ⟨Cx, hCx⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  set M := max Cx Cg
  have hLip : ∀ t ∈ Ico (0 : ℝ) T, LipschitzOnWith (Real.toNNReal (|r| * (1 + 2 * M / K)))
      (fun y : ℝ => r * y * (1 - y / K)) (Metric.closedBall 0 M) := by
    intro _ _
    apply LipschitzOnWith.of_dist_le'
    intro y hy z hz
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hy hz
    rw [Real.dist_eq, Real.dist_eq]
    have hfac : r * y * (1 - y / K) - r * z * (1 - z / K) = r * (y - z) * (1 - (y + z) / K) := by
      ring
    rw [hfac, abs_mul, abs_mul]
    have h1 : |1 - (y + z) / K| ≤ 1 + 2 * M / K := by
      calc |1 - (y + z) / K| ≤ |1| + |(y + z) / K| := abs_sub _ _
        _ = 1 + |y + z| / K := by rw [abs_one, abs_div, abs_of_pos hK]
        _ ≤ 1 + 2 * M / K := by
          gcongr
          calc |y + z| ≤ |y| + |z| := abs_add_le _ _
            _ ≤ M + M := add_le_add hy hz
            _ = 2 * M := by ring
    calc |r| * |y - z| * |1 - (y + z) / K| ≤ |r| * |y - z| * (1 + 2 * M / K) := by gcongr
      _ = |r| * (1 + 2 * M / K) * |y - z| := by ring
  have hmem : ∀ (f : ℝ → ℝ) (C : ℝ), (∀ t ∈ Icc (0 : ℝ) T, ‖f t‖ ≤ C) → C ≤ M →
      ∀ t ∈ Ico (0 : ℝ) T, f t ∈ Metric.closedBall (0 : ℝ) M := by
    intro f C hC hCM t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hC t (Ico_subset_Icc_self ht)).trans hCM
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ y => r * y * (1 - y / K))
    (s := fun _ => Metric.closedBall 0 M) hLip hc hd
    (hmem x Cx hCx (le_max_left _ _)) hgc
    (fun t ht => (hgd t ht.1).hasDerivWithinAt)
    (hmem g Cg hCg (le_max_right _ _)) (by rw [h0, hg, logistic_zero _ hK.ne'])

/-- **Convergence to the carrying capacity**: for `r > 0` and `x₀ > 0`, `x(t) → K` as
`t → ∞` (the identity needs no sign condition on `K`; biologically `K > 0`). -/
theorem tendsto_logistic_atTop {r K x₀ : ℝ} (hr : 0 < r) (hx₀ : 0 < x₀) :
    Tendsto (logistic r K x₀) atTop (𝓝 K) := by
  have heq : logistic r K x₀ =
      fun t => K * x₀ / (K * exp (-(r * t)) + x₀ * (1 - exp (-(r * t)))) := by
    funext t
    simp only [logistic, exp_neg]
    have := exp_pos (r * t)
    field_simp
  rw [heq]
  have he : Tendsto (fun t => exp (-(r * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
  have hden : Tendsto (fun t => K * exp (-(r * t)) + x₀ * (1 - exp (-(r * t)))) atTop
      (𝓝 (K * 0 + x₀ * (1 - 0))) :=
    (he.const_mul K).add ((tendsto_const_nhds.sub he).const_mul x₀)
  have h := (tendsto_const_nhds (x := K * x₀)).div hden (by simp [hx₀.ne'])
  rwa [show K * x₀ / (K * 0 + x₀ * (1 - 0)) = K by
    rw [mul_zero, zero_add, sub_zero, mul_one]; field_simp] at h

/-- **Exponential limit**: for fixed `r`, `x₀`, `t`, the logistic solution tends to the
exponential-growth solution `x₀ e^{r t}` as the carrying capacity `K → ∞`. -/
theorem tendsto_logistic_carryingCapacity_atTop (r x₀ t : ℝ) :
    Tendsto (fun K => logistic r K x₀ t) atTop (𝓝 (x₀ * exp (r * t))) := by
  have heq : (fun K => logistic r K x₀ t) =ᶠ[atTop]
      fun K => x₀ * exp (r * t) / (1 + x₀ * (exp (r * t) - 1) * K⁻¹) := by
    filter_upwards [eventually_gt_atTop 0] with K hK
    simp only [logistic]
    field_simp
  rw [tendsto_congr' heq]
  have := (tendsto_const_nhds (x := x₀ * exp (r * t))).div
    (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul (x₀ * (exp (r * t) - 1))))
    (by simp : (1 : ℝ) + x₀ * (exp (r * t) - 1) * 0 ≠ 0)
  rwa [mul_zero, add_zero, div_one] at this

/-- **Log-odds grow linearly** for a frequency (`K = 1`): for `0 < x₀ < 1` and all `r`, `t`,
`log (x(t) / (1 - x(t))) = log (x₀ / (1 - x₀)) + r t`. -/
theorem logit_logistic {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₁ : x₀ < 1) (r t : ℝ) :
    log (logistic r 1 x₀ t / (1 - logistic r 1 x₀ t)) = log (x₀ / (1 - x₀)) + r * t := by
  have hD : 0 < 1 + x₀ * (exp (r * t) - 1) := by nlinarith [exp_pos (r * t)]
  have hq : logistic r 1 x₀ t / (1 - logistic r 1 x₀ t) = x₀ / (1 - x₀) * exp (r * t) := by
    simp only [logistic]
    have h1 : (1 : ℝ) - x₀ ≠ 0 := by linarith
    have h2 : 1 + x₀ * (exp (r * t) - 1) - 1 * x₀ * exp (r * t) = 1 - x₀ := by ring
    rw [one_sub_div hD.ne', h2]
    field_simp
  rw [hq, log_mul (div_pos hx₀ (by linarith)).ne' (exp_pos _).ne', log_exp]

/-- **Exact deterministic transit time**: starting from frequency `a ∈ (0, 1)` with `r ≠ 0`,
the logistic frequency reaches `1 - a` at time `(2 / r) log ((1 - a) / a)`. -/
theorem logistic_transitTime {a r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr : r ≠ 0) :
    logistic r 1 a (2 / r * log ((1 - a) / a)) = 1 - a := by
  set q := (1 - a) / a with hq
  have hqpos : 0 < q := div_pos (by linarith) ha
  have he : exp (r * (2 / r * log q)) = q ^ 2 := by
    rw [show r * (2 / r * log q) = 2 * log q by field_simp, two_mul, exp_add, exp_log hqpos, sq]
  simp only [logistic, he]
  rw [hq]
  have h1 : (1 : ℝ) - a ≠ 0 := by linarith
  have h2 : a ≠ 0 := ha.ne'
  have hden : 1 + a * (((1 - a) / a) ^ 2 - 1) = (1 - a) / a := by field_simp; ring
  rw [hden]
  field_simp

/-- The transit time from `1 / (2N)` to `1 - 1 / (2N)` is `(2 / r) log (2N - 1)`, for
`N ≥ 1` and `r ≠ 0`. -/
theorem logistic_transitTime_twoN {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : r ≠ 0) :
    logistic r 1 (1 / (2 * N)) (2 / r * log (2 * N - 1)) = 1 - 1 / (2 * N) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : (0 : ℝ) < 1 / (2 * N) := by positivity
  have ha1 : 1 / (2 * (N : ℝ)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have h := logistic_transitTime ha ha1 hr
  have hq : (1 - 1 / (2 * (N : ℝ))) / (1 / (2 * N)) = 2 * N - 1 := by
    field_simp
  rwa [hq] at h

/-- For `r > 0` and `0 < x₀ < K` the logistic solution is strictly increasing, so the transit
time of `logistic_transitTime` is the unique time at which `1 - a` is reached. -/
theorem strictMono_logistic {r K x₀ : ℝ} (hr : 0 < r) (hK : 0 < K) (hx₀ : 0 < x₀)
    (hx₀K : x₀ < K) : StrictMono (logistic r K x₀) := by
  have hden : ∀ t, 0 < K + x₀ * (exp (r * t) - 1) := fun t =>
    logistic_denom_pos hK hx₀ (Or.inr hx₀K.le)
  refine strictMono_of_hasDerivAt_pos (fun t => hasDerivAt_logistic hK.ne' (hden t).ne') ?_
  intro t
  have hpos : 0 < logistic r K x₀ t := by
    unfold logistic; have := hden t; positivity
  have hlt : logistic r K x₀ t < K := by
    unfold logistic
    rw [div_lt_iff₀ (hden t)]
    nlinarith [exp_pos (r * t)]
  have : 0 < 1 - logistic r K x₀ t / K := by
    rw [sub_pos, div_lt_one hK]; exact hlt
  positivity

end MathlibExt.Biology.Dynamics.Logistic
