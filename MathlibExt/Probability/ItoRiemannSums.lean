/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import MathlibExt.Probability.ElementaryItoIntegral
public import MathlibExt.Probability.OrnsteinUhlenbeck
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Itô–Riemann sums of deterministic integrands

For a deterministic integrand `g` of class `C¹`, the elementary Itô integrals of the left-point
step approximations `∑_{k < n} g (t k / n) 1_{(t k / n, t (k + 1) / n]}` of `g` on `[0, t]`
converge, path by path for every continuous driving path, to Wiener's integration-by-parts
expression `g t B t - g 0 B 0 - ∫_0^t g'(u) B u du`. Applied to `g u = e^{θ u}`, this identifies
the Itô form `e^{-θt} X₀ + σ e^{-θt} ∫_0^t e^{θ s} dB_s` of the Ornstein–Uhlenbeck solution
(read as the almost-sure limit of these Itô–Riemann sums) with the pathwise solution
`ProbabilityTheory.ouPathSolution`.

The convergence here is pathwise (for every `ω` whose path is continuous, hence almost surely
for a Brownian motion); the `L²` Itô integral of a general progressive integrand is not
constructed in this file.

## Main definitions

* `ProbabilityTheory.ElementaryIntegrand.riemann`: the left-point step approximation of a
  deterministic continuous `g` on the uniform partition of `[0, t]` into `n` cells.

## Main results

* `ProbabilityTheory.tendsto_sum_mul_sub_uniform`: Riemann–Stieltjes integration by parts along
  uniform partitions, for a `C¹` function against a continuous path.
* `ProbabilityTheory.ElementaryIntegrand.tendsto_itoIntegral_riemann`: the Itô–Riemann sums of a
  `C¹` integrand converge to `g t B t - g 0 B 0 - ∫_0^t g' B` along every continuous path.
* `ProbabilityTheory.IsBrownianReal.ae_tendsto_ou_itoIntegral_riemann`: the Itô–Riemann form of
  the Ornstein–Uhlenbeck solution converges almost surely to `ouPathSolution`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Section 3.2 (simple integrands) and Section 5.6 (linear equations, the
  Ornstein–Uhlenbeck process).
* B. Øksendal, *Stochastic Differential Equations*, 6th ed., Springer, 2003, Theorem 4.1.5
  (integration by parts for deterministic integrands) and Chapter 5 (the OU process).
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped NNReal ProbabilityTheory

namespace ProbabilityTheory

private theorem sum_mul_sub_eq (g w : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, g k * (w (k + 1) - w k) =
      g n * w n - g 0 * w 0 - ∑ k ∈ Finset.range n, (g (k + 1) - g k) * w (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- **Riemann–Stieltjes integration by parts, uniform partitions.** For a `C¹` function `g`, a
continuous path `w` and `t ≥ 0`, the left-point sums
`∑_{k < n} g (t k / n) (w (t (k + 1) / n) - w (t k / n))` converge, as `n → ∞`, to
`g t w t - g 0 w 0 - ∫_0^t g' w`. -/
theorem tendsto_sum_mul_sub_uniform {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {w : ℝ → ℝ}
    (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        g (t * k / n) * (w (t * (k + 1) / n) - w (t * k / n))) atTop
      (𝓝 (g t * w t - g 0 * w 0 - ∫ u in (0 : ℝ)..t, deriv g u * w u)) := by
  have hg' : Continuous (deriv g) := hg.continuous_deriv_one
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg'.continuousOn (s := Set.Icc 0 t))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous (hw.continuousOn (s := Set.Icc 0 t))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (K * t + 1) := by positivity
  obtain ⟨δ, hδ, hδw⟩ := Metric.uniformContinuousOn_iff.mp huc _ hε'
  obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_pos N).trans_le hn
  have hmesh : t / n < δ := by
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ] at hN
    calc t < N * δ := hN
      _ ≤ δ * n := by rw [mul_comm]; gcongr; exact_mod_cast (Nat.le_succ N).trans hn
  set s : ℕ → ℝ := fun k ↦ t * k / n with hs
  have hs0 : s 0 = 0 := by simp [s]
  have hsn : s n = t := by simp [s, hn0.ne']
  have hsucc : ∀ k : ℕ, s (k + 1) - s k = t / n := fun k ↦ by simp only [s]; push_cast; ring
  have hsmem : ∀ k ≤ n, s k ∈ Set.Icc 0 t := fun k hk ↦ ⟨by positivity, by
    simp only [s]; rw [div_le_iff₀ hn0]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) ht⟩
  have hsmono : ∀ k, s k ≤ s (k + 1) := fun k ↦ by
    have := hsucc k; have : 0 ≤ t / n := by positivity
    linarith
  have hc : Continuous fun u ↦ deriv g u * w u := hg'.mul hw
  have hrw : ∀ k : ℕ, t * ((k : ℝ) + 1) / n = s (k + 1) := fun k ↦ by simp [s]
  simp_rw [hrw]
  rw [sum_mul_sub_eq (fun k ↦ g (s k)) (fun k ↦ w (s k)) n, hs0, hsn]
  have hcell : ∀ k ∈ Finset.range n, (g (s (k + 1)) - g (s k)) * w (s (k + 1)) =
      ∫ u in s k..s (k + 1), deriv g u * w (s (k + 1)) := by
    intro k _
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hgd x) (hg'.intervalIntegrable _ _)]
  have hsum : ∫ u in (0 : ℝ)..t, deriv g u * w u =
      ∑ k ∈ Finset.range n, ∫ u in s k..s (k + 1), deriv g u * w u := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ ↦ hc.intervalIntegrable _ _), hs0, hsn]
  rw [Finset.sum_congr rfl hcell, hsum, Real.dist_eq]
  have hdiff : (g t * w t - g 0 * w 0 -
        ∑ k ∈ Finset.range n, ∫ u in s k..s (k + 1), deriv g u * w (s (k + 1))) -
      (g t * w t - g 0 * w 0 - ∑ k ∈ Finset.range n, ∫ u in s k..s (k + 1), deriv g u * w u) =
      ∑ k ∈ Finset.range n, ∫ u in s k..s (k + 1), deriv g u * (w u - w (s (k + 1))) := by
    rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
      ((show Continuous fun u ↦ deriv g u * w (s (k + 1)) from
        hg'.mul continuous_const).intervalIntegrable _ _)]
    congr 1
    funext u
    ring
  rw [hdiff]
  have hcellb : ∀ k ∈ Finset.range n,
      ‖∫ u in s k..s (k + 1), deriv g u * (w u - w (s (k + 1)))‖ ≤
        K * (ε / (K * t + 1)) * (t / n) := by
    intro k hk
    have hk' : k + 1 ≤ n := Finset.mem_range.mp hk
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K * (ε / (K * t + 1)))
      fun u hu ↦ ?_).trans_eq ?_
    · rw [Set.uIoc_of_le (hsmono k)] at hu
      have hu' : u ∈ Set.Icc 0 t :=
        ⟨(hsmem k (by omega)).1.trans hu.1.le, hu.2.trans (hsmem (k + 1) hk').2⟩
      rw [norm_mul]
      refine mul_le_mul (hK u hu') ?_ (norm_nonneg _) hK0
      rw [Real.norm_eq_abs, ← Real.dist_eq]
      refine (hδw u hu' (s (k + 1)) (hsmem (k + 1) hk') ?_).le
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hu.2])]
      linarith [hu.1, hsucc k]
    · rw [hsucc k, abs_of_nonneg (by positivity)]
  calc |∑ k ∈ Finset.range n, ∫ u in s k..s (k + 1), deriv g u * (w u - w (s (k + 1)))|
      ≤ ∑ k ∈ Finset.range n, K * (ε / (K * t + 1)) * (t / n) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hcellb)
    _ = K * t * (ε / (K * t + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg hK0 ht]

namespace ElementaryIntegrand

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The left-point step approximation `∑_{k < n} g (t k / n) 1_{(t k / n, t (k + 1) / n]}` of a
deterministic `g` on the uniform partition of `[0, t]` into `n` cells, as an
elementary integrand for any filtration `F` (deterministic coefficients are measurable for every
σ-algebra). -/
noncomputable def riemann (F : Filtration ℝ≥0 mΩ) (g : ℝ → ℝ) (t : ℝ≥0) (n : ℕ) :
    ElementaryIntegrand F where
  n := n
  time := fun k ↦ t * k / n
  monotone_time := fun i j hij ↦ by
    have : ((i : ℕ) : ℝ≥0) ≤ (j : ℕ) := by exact_mod_cast hij
    dsimp only
    gcongr
  coeff := fun k _ ↦ g ((t * (k.castSucc : ℕ) / n : ℝ≥0) : ℝ)
  measurable_coeff := fun _ ↦ measurable_const
  bound := ∑ k : Fin n, |g ((t * (k.castSucc : ℕ) / n : ℝ≥0) : ℝ)|
  abs_coeff_le := fun k _ ↦
    Finset.single_le_sum (f := fun k : Fin n ↦ |g ((t * (k.castSucc : ℕ) / n : ℝ≥0) : ℝ)|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ k)

private theorem time_le {t : ℝ≥0} {n k : ℕ} (hk : k ≤ n) : t * k / n ≤ t := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · rw [div_le_iff₀ (by exact_mod_cast hn)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) bot_le

private theorem coe_time (t : ℝ≥0) (n k : ℕ) :
    ((t * k / n : ℝ≥0) : ℝ) = (t : ℝ) * k / n := by
  push_cast
  rfl

/-- The elementary Itô integral of `riemann F g t n` at time `t` is the Itô–Riemann sum
`∑_{k < n} g (t k / n) (B (t (k + 1) / n) - B (t k / n))`. -/
theorem itoIntegral_riemann (F : Filtration ℝ≥0 mΩ) (g : ℝ → ℝ) (t : ℝ≥0) (n : ℕ)
    (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (riemann F g t n).itoIntegral B t ω = ∑ k ∈ Finset.range n,
      g (t * k / n) *
        (B (Real.toNNReal (t * (k + 1) / n)) ω - B (Real.toNNReal (t * k / n)) ω) := by
  refine (Fin.sum_univ_eq_sum_range (fun k ↦ g ((t * (k : ℕ) / n : ℝ≥0) : ℝ) *
    (B (min (t * ((k + 1 : ℕ) : ℝ≥0) / n) t) ω - B (min (t * (k : ℕ) / n) t) ω)) n).trans ?_
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < n := Finset.mem_range.mp hk
  rw [min_eq_left (time_le hk'), min_eq_left (time_le hk'.le), coe_time,
    show (t : ℝ) * (k + 1) / n = ((t * ((k + 1 : ℕ) : ℝ≥0) / n : ℝ≥0) : ℝ) by
      rw [coe_time]; push_cast; ring,
    ← coe_time, Real.toNNReal_coe, Real.toNNReal_coe]

/-- **Itô–Riemann sums of a deterministic `C¹` integrand.** Along every continuous path of `B`,
the elementary Itô integrals at time `t` of the left-point approximations of `g` converge to
Wiener's integration-by-parts expression `g t B t - g 0 B 0 - ∫_0^t g'(u) B u du`. -/
theorem tendsto_itoIntegral_riemann (F : Filtration ℝ≥0 mΩ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : Continuous (B · ω)) (t : ℝ≥0) :
    Tendsto (fun n ↦ (riemann F g t n).itoIntegral B t ω) atTop
      (𝓝 (g t * B t ω - g 0 * B 0 ω - ∫ u in (0 : ℝ)..t, deriv g u * B u.toNNReal ω)) := by
  simp_rw [itoIntegral_riemann]
  have h := tendsto_sum_mul_sub_uniform hg (w := fun u ↦ B u.toNNReal ω)
    (hω.comp continuous_real_toNNReal) t.2
  simpa [Real.toNNReal_coe] using h

end ElementaryIntegrand

/-- The pathwise Ornstein–Uhlenbeck solution in integration-by-parts form: with `g u = e^{θu}`,
`ouPathSolution θ σ x₀ w t = e^{-θt} x₀ + σ e^{-θt} (g t w t - g 0 w 0 - ∫_0^t g'(u) w u du)`,
for any path `w` and any real `θ`, `σ`, `x₀`, `t`. -/
theorem ouPathSolution_eq_integration_by_parts (θ σ x₀ : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    ouPathSolution θ σ x₀ w t = exp (-θ * t) * x₀ + σ * exp (-θ * t) *
      (exp (θ * t) * w t - exp (θ * 0) * w 0 -
        ∫ u in (0 : ℝ)..t, deriv (fun u ↦ exp (θ * u)) u * w u) := by
  have hd : deriv (fun u : ℝ ↦ exp (θ * u)) = fun u ↦ θ * exp (θ * u) := by
    funext u
    rw [((hasDerivAt_id' u).const_mul θ).exp.deriv]
    ring
  have hk : (∫ u in (0 : ℝ)..t, exp (-θ * (t - u)) * w u) =
      exp (-θ * t) * ∫ u in (0 : ℝ)..t, exp (θ * u) * w u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    rw [show -θ * (t - u) = -θ * t + θ * u by ring, Real.exp_add]
    ring
  have hθ : (∫ u in (0 : ℝ)..t, θ * exp (θ * u) * w u) =
      θ * ∫ u in (0 : ℝ)..t, exp (θ * u) * w u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    ring
  have he : exp (-θ * t) * exp (θ * t) = 1 := by
    rw [← Real.exp_add]; simp
  rw [hd, hθ, ouPathSolution, hk]
  simp only [mul_zero, Real.exp_zero]
  linear_combination (-σ * w t) * he

/-- **The Itô form of the Ornstein–Uhlenbeck solution.** For a Brownian motion `B`, almost surely,
for every `t ≥ 0` and every initial value `X₀`, the Itô–Riemann sums
`e^{-θt} X₀ + σ e^{-θt} ∑_{k < n} e^{θ t k / n} (B (t (k + 1) / n) - B (t k / n))` of
`e^{-θt} X₀ + σ ∫_0^t e^{-θ(t-s)} dB_s` converge to the pathwise solution `ouPathSolution`
(any real `θ`, `σ`). -/
theorem IsBrownianReal.ae_tendsto_ou_itoIntegral_riemann {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (F : Filtration ℝ≥0 mΩ)
    (θ σ : ℝ) (X₀ : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto (fun n ↦ exp (-θ * t) * X₀ ω + σ * exp (-θ * t) *
        (ElementaryIntegrand.riemann F (fun u ↦ exp (θ * u)) t n).itoIntegral B t ω)
      atTop (𝓝 (ouPathSolution θ σ (X₀ ω) (fun u ↦ B u.toNNReal ω) t)) := by
  filter_upwards [hB.cont] with ω hω t
  have hg : ContDiff ℝ 1 (fun u : ℝ ↦ exp (θ * u)) := by fun_prop
  have h := (ElementaryIntegrand.tendsto_itoIntegral_riemann F hg hω t).const_mul
    (σ * exp (-θ * t)) |>.const_add (exp (-θ * t) * X₀ ω)
  convert h using 2
  rw [ouPathSolution_eq_integration_by_parts, Real.toNNReal_coe, Real.toNNReal_zero]

end ProbabilityTheory
