/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Minimizing movements: the metric skeleton of the JKO scheme

Jordan, Kinderlehrer and Otto (1998) discretize the Fokker–Planck equation in time by the
implicit variational scheme (their equation (13)): given the previous state `ρ⁽ᵏ⁻¹⁾` and a time
step `h > 0`, the new state `ρ⁽ᵏ⁾` minimizes

`½ d(ρ⁽ᵏ⁻¹⁾, ρ)² + h F(ρ)`

where `d` is the quadratic Wasserstein distance and `F` the free energy. The a priori estimates
that drive their convergence proof (Section 5, the summed inequality before (46) and the second
and third lines of (46)) use only that `d` is a metric: comparing the minimizer with the previous
state gives
`½ d(ρ⁽ᵏ⁻¹⁾, ρ⁽ᵏ⁾)² + h F(ρ⁽ᵏ⁾) ≤ h F(ρ⁽ᵏ⁻¹⁾)`, which sums to a discrete energy inequality, and
the triangle and Cauchy–Schwarz inequalities turn it into a `½`-Hölder bound in time.

This file formalizes that skeleton on an arbitrary (pseudo)metric space, for an arbitrary
real-valued functional `F`. Existence and uniqueness of the minimizer on probability densities
(Proposition 4.1) are proved in `MathlibExt/Probability/Diffusion/JKOStep.lean`. Convergence
to the Fokker–Planck equation (Theorem 5.1) is stated in
`WantedExt/MeasureTheory/JKOSchemeWanted.lean`.

## Main results

* `IsMinimizingMovementStep`, `IsMinimizingMovement`: one step, and a whole sequence, of the
  scheme.
* `IsMinimizingMovementStep.energy_le`: the one-step energy inequality.
* `IsMinimizingMovement.energy_sum_le`: the discrete energy inequality
  `(1 / 2h) ∑ d(ρₖ, ρₖ₊₁)² + F(ρ_N) ≤ F(ρ₀)`.
* `IsMinimizingMovement.antitone`: the functional decreases along the scheme.
* `IsMinimizingMovement.dist_sq_le`: `d(ρⱼ, ρⱼ₊ₙ)² ≤ 2hn (F(ρⱼ) - F(ρⱼ₊ₙ))`.
* `IsMinimizingMovement.dist_sq_le_of_le`: with `F ≥ m`, `d(ρⱼ, ρₖ)² ≤ 2 (k - j) h (F(ρ₀) - m)`.
* `exists_isMinimizingMovementStep`, `exists_isMinimizingMovement`: on a proper metric space, a
  lower semicontinuous functional bounded below admits the scheme from every starting point.

## References

* R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck
  equation*, SIAM J. Math. Anal. 29 (1998), 1–17, scheme (13) and the proof of Theorem 5.1.
-/

@[expose] public section

open Finset

namespace MathlibExt.Analysis.Variational.MinimizingMovement

variable {X : Type*} [PseudoMetricSpace X]

/-- **Minimizing-movement (JKO) step.** For a functional `F : X → ℝ` on a metric space and a time
step `h`, the point `y` is a step of the scheme from `x` if it minimizes
`z ↦ ½ d(x, z)² + h F(z)`. This is the scheme (13) of R. Jordan, D. Kinderlehrer and F. Otto,
*The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998),
1–17, where `X` is the space of probability densities with finite second moment, `d` the
quadratic Wasserstein distance and `F` the free energy. -/
def IsMinimizingMovementStep (F : X → ℝ) (h : ℝ) (x y : X) : Prop :=
  ∀ z, dist x y ^ 2 / 2 + h * F y ≤ dist x z ^ 2 / 2 + h * F z

/-- **Minimizing-movement (JKO) sequence.** A sequence `ρ : ℕ → X` solves the scheme for `F` with
time step `h` if each `ρ (k + 1)` is a minimizing-movement step from `ρ k`
(Jordan, Kinderlehrer and Otto, SIAM J. Math. Anal. 29 (1998), scheme (13), with `ρ 0 = ρ⁰`). -/
def IsMinimizingMovement (F : X → ℝ) (h : ℝ) (ρ : ℕ → X) : Prop :=
  ∀ k, IsMinimizingMovementStep F h (ρ k) (ρ (k + 1))

/-- **One-step energy inequality of the JKO scheme.** If `y` is a minimizing-movement step from
`x`, then `½ d(x, y)² + h F(y) ≤ h F(x)`: compare the minimizer with the competitor `z = x`
(Jordan, Kinderlehrer and Otto, SIAM J. Math. Anal. 29 (1998), proof of Theorem 5.1, the
inequality preceding (46)). -/
theorem IsMinimizingMovementStep.energy_le {F : X → ℝ} {h : ℝ} {x y : X}
    (hy : IsMinimizingMovementStep F h x y) :
    dist x y ^ 2 / 2 + h * F y ≤ h * F x := by
  simpa using hy x

/-- **The JKO step decreases the functional.** For a positive time step, a minimizing-movement
step `y` from `x` satisfies `F(y) ≤ F(x)`; the free energy is a Lyapunov function of the
discrete scheme (Jordan, Kinderlehrer and Otto, SIAM J. Math. Anal. 29 (1998), proof of
Theorem 5.1). -/
theorem IsMinimizingMovementStep.le {F : X → ℝ} {h : ℝ} (hh : 0 < h) {x y : X}
    (hy : IsMinimizingMovementStep F h x y) : F y ≤ F x := by
  have := hy.energy_le
  have h2 : 0 ≤ dist x y ^ 2 / 2 := by positivity
  nlinarith

/-- **Tails of a minimizing-movement sequence.** If `ρ` solves the minimizing-movement scheme,
so does `k ↦ ρ (j + k)` for every `j`. -/
theorem IsMinimizingMovement.shift {F : X → ℝ} {h : ℝ} {ρ : ℕ → X}
    (hρ : IsMinimizingMovement F h ρ) (j : ℕ) :
    IsMinimizingMovement F h (fun k => ρ (j + k)) := fun k => by
  simpa [Nat.add_assoc] using hρ (j + k)

/-- **Discrete energy inequality, multiplied form.** Along a minimizing-movement sequence,
`½ ∑_{k < N} d(ρₖ, ρₖ₊₁)² + h F(ρ_N) ≤ h F(ρ₀)` for every `N`. -/
theorem IsMinimizingMovement.sum_add_le {F : X → ℝ} {h : ℝ} {ρ : ℕ → X}
    (hρ : IsMinimizingMovement F h ρ) (N : ℕ) :
    (∑ k ∈ range N, dist (ρ k) (ρ (k + 1)) ^ 2) / 2 + h * F (ρ N) ≤ h * F (ρ 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have := (hρ N).energy_le
    rw [sum_range_succ]
    linarith

/-- **Discrete energy inequality of the JKO scheme.** For a time step `h > 0`, along a
minimizing-movement sequence `(1 / 2h) ∑_{k < N} d(ρₖ, ρₖ₊₁)² + F(ρ_N) ≤ F(ρ₀)`
(R. Jordan, D. Kinderlehrer and F. Otto, *The variational formulation of the Fokker–Planck
equation*, SIAM J. Math. Anal. 29 (1998), proof of Theorem 5.1: the summed inequality preceding
(46)). -/
theorem IsMinimizingMovement.energy_sum_le {F : X → ℝ} {h : ℝ} (hh : 0 < h) {ρ : ℕ → X}
    (hρ : IsMinimizingMovement F h ρ) (N : ℕ) :
    (∑ k ∈ range N, dist (ρ k) (ρ (k + 1)) ^ 2) / (2 * h) + F (ρ N) ≤ F (ρ 0) := by
  have key := hρ.sum_add_le N
  have e : (∑ k ∈ range N, dist (ρ k) (ρ (k + 1)) ^ 2) / (2 * h) =
      ((∑ k ∈ range N, dist (ρ k) (ρ (k + 1)) ^ 2) / 2) / h := by
    rw [div_div, mul_comm]
  rw [e, div_add' _ _ _ hh.ne', div_le_iff₀ hh]
  linarith

/-- **The functional decreases along the JKO scheme.** For a time step `h > 0`, `k ↦ F(ρₖ)` is
antitone along a minimizing-movement sequence (the discrete H-theorem; Jordan, Kinderlehrer and
Otto, SIAM J. Math. Anal. 29 (1998), proof of Theorem 5.1). -/
theorem IsMinimizingMovement.antitone {F : X → ℝ} {h : ℝ} (hh : 0 < h) {ρ : ℕ → X}
    (hρ : IsMinimizingMovement F h ρ) : Antitone (fun k => F (ρ k)) :=
  antitone_nat_of_succ_le fun k => (hρ k).le hh

/-- **Hölder-½ estimate of the JKO scheme.** Along a minimizing-movement sequence with any time
step `h`, `d(ρⱼ, ρⱼ₊ₙ)² ≤ 2hn (F(ρⱼ) - F(ρⱼ₊ₙ))`: the triangle inequality and the
Cauchy–Schwarz inequality give `d(ρⱼ, ρⱼ₊ₙ)² ≤ n ∑ d(ρₖ, ρₖ₊₁)²`, and the discrete energy
inequality bounds the sum (R. Jordan, D. Kinderlehrer and F. Otto, *The variational formulation
of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), proof of Theorem 5.1, the
second and third lines of (46)). In the time variable `t = kh` this reads
`d(ρⱼ, ρₖ) ≤ √(2 (tₖ - tⱼ) (F(ρⱼ) - F(ρₖ)))`. -/
theorem IsMinimizingMovement.dist_sq_le {F : X → ℝ} {h : ℝ} {ρ : ℕ → X}
    (hρ : IsMinimizingMovement F h ρ) (j n : ℕ) :
    dist (ρ j) (ρ (j + n)) ^ 2 ≤ 2 * h * n * (F (ρ j) - F (ρ (j + n))) := by
  set σ : ℕ → X := fun k => ρ (j + k) with hσ
  have hσm : IsMinimizingMovement F h σ := hρ.shift j
  have tri : dist (σ 0) (σ n) ≤ ∑ k ∈ range n, dist (σ k) (σ (k + 1)) :=
    dist_le_range_sum_dist σ n
  have cs : (∑ k ∈ range n, dist (σ k) (σ (k + 1))) ^ 2 ≤
      n * ∑ k ∈ range n, dist (σ k) (σ (k + 1)) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := range n) (f := fun k => dist (σ k) (σ (k + 1)))
  have en := hσm.sum_add_le n
  have h0 : 0 ≤ dist (σ 0) (σ n) := dist_nonneg
  have sq : dist (σ 0) (σ n) ^ 2 ≤ (∑ k ∈ range n, dist (σ k) (σ (k + 1))) ^ 2 :=
    pow_le_pow_left₀ h0 tri 2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : dist (σ 0) (σ n) ^ 2 ≤ n * (2 * (h * F (σ 0) - h * F (σ n))) := by
    have : ∑ k ∈ range n, dist (σ k) (σ (k + 1)) ^ 2 ≤ 2 * (h * F (σ 0) - h * F (σ n)) := by
      linarith
    calc dist (σ 0) (σ n) ^ 2 ≤ n * ∑ k ∈ range n, dist (σ k) (σ (k + 1)) ^ 2 := sq.trans cs
      _ ≤ n * (2 * (h * F (σ 0) - h * F (σ n))) := mul_le_mul_of_nonneg_left this hn
  simp only [hσ, Nat.add_zero] at this
  linarith

/-- **Uniform Hölder-½ bound of the JKO scheme.** If `F ≥ m` everywhere and `h > 0`, then along a
minimizing-movement sequence `d(ρⱼ, ρₖ)² ≤ 2 (k - j) h (F(ρ₀) - m)` for `j ≤ k`, i.e.
`d(ρⱼ, ρₖ) ≤ √(2 (tₖ - tⱼ) (F(ρ₀) - m))` with `t = kh`: the discrete trajectories are
equicontinuous in time, uniformly in `h` (Jordan, Kinderlehrer and Otto, SIAM J. Math. Anal. 29
(1998), proof of Theorem 5.1, where `F` is not bounded below and the bound is obtained from
(46) and the moment estimate (14) instead). -/
theorem IsMinimizingMovement.dist_sq_le_of_le {F : X → ℝ} {h m : ℝ} (hh : 0 < h)
    (hm : ∀ x, m ≤ F x) {ρ : ℕ → X} (hρ : IsMinimizingMovement F h ρ) {j k : ℕ} (hjk : j ≤ k) :
    dist (ρ j) (ρ k) ^ 2 ≤ 2 * ((k : ℝ) - j) * h * (F (ρ 0) - m) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have key := hρ.dist_sq_le j n
  have hj : F (ρ j) ≤ F (ρ 0) := hρ.antitone hh (Nat.zero_le j)
  have hmn := hm (ρ (j + n))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : F (ρ j) - F (ρ (j + n)) ≤ F (ρ 0) - m := by linarith
  have e : ((j + n : ℕ) : ℝ) - j = n := by push_cast; ring
  rw [e]
  calc dist (ρ j) (ρ (j + n)) ^ 2 ≤ 2 * h * n * (F (ρ j) - F (ρ (j + n))) := key
    _ ≤ 2 * h * n * (F (ρ 0) - m) := by
      apply mul_le_mul_of_nonneg_left this; positivity
    _ = 2 * n * h * (F (ρ 0) - m) := by ring

/-- **Existence of a JKO step on a proper metric space.** If `X` is a proper metric space,
`F : X → ℝ` is lower semicontinuous and bounded below, and `h > 0`, then from every `x` there is
a minimizing-movement step: `z ↦ ½ d(x, z)² + h F(z)` attains its minimum, because its sublevel
set at level `h F(x)` lies in a closed ball, which is compact. (The space of probability
densities with the Wasserstein distance is not proper; JKO prove existence there separately,
Proposition 4.1.) -/
theorem exists_isMinimizingMovementStep [ProperSpace X] {F : X → ℝ}
    (hF : LowerSemicontinuous F) (hbdd : BddBelow (Set.range F)) {h : ℝ} (hh : 0 < h) (x : X) :
    ∃ y, IsMinimizingMovementStep F h x y := by
  obtain ⟨m, hm⟩ := hbdd
  have hm' : ∀ z, m ≤ F z := fun z => hm ⟨z, rfl⟩
  set G : X → ℝ := fun z => dist x z ^ 2 / 2 + h * F z with hG
  set r : ℝ := Real.sqrt (2 * h * (F x - m)) with hr
  have hGx : G x = h * F x := by simp [hG]
  -- every `z` with `G z ≤ G x` lies in the closed ball of radius `r`
  have hsub : ∀ z, G z ≤ G x → z ∈ Metric.closedBall x r := by
    intro z hz
    rw [Metric.mem_closedBall, dist_comm, hr]
    apply Real.le_sqrt_of_sq_le
    have := hm' z
    have : h * m ≤ h * F z := mul_le_mul_of_nonneg_left this hh.le
    simp only [hG, dist_self] at hz
    nlinarith
  have hcpt : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
  have hxmem : x ∈ Metric.closedBall x r :=
    Metric.mem_closedBall_self (Real.sqrt_nonneg _)
  have hGlsc : LowerSemicontinuous G := by
    have h1 : LowerSemicontinuous (fun z : X => dist x z ^ 2 / 2) :=
      ((continuous_const.dist continuous_id).pow 2).div_const 2 |>.lowerSemicontinuous
    have h2 : LowerSemicontinuous (fun z : X => h * F z) := by
      intro z c hc
      have hc' : c / h < F z := by rw [div_lt_iff₀ hh]; linarith
      filter_upwards [hF z (c / h) hc'] with w hw
      have hw' : c / h < F w := hw
      rw [div_lt_iff₀ hh] at hw'
      change c < h * F w
      linarith
    exact h1.add h2
  obtain ⟨y, hy, hmin⟩ := (hGlsc.lowerSemicontinuousOn _).exists_isMinOn ⟨x, hxmem⟩ hcpt
  refine ⟨y, fun z => ?_⟩
  by_cases hz : G z ≤ G x
  · exact hmin (hsub z hz)
  · have := hmin hxmem
    have hz' : G x < G z := lt_of_not_ge hz
    have hy' : G y ≤ G x := this
    change G y ≤ G z
    linarith

/-- **Existence of a JKO sequence on a proper metric space.** Under the hypotheses of
`exists_isMinimizingMovementStep`, every starting point `x₀` admits a minimizing-movement
sequence `ρ` with `ρ 0 = x₀`. -/
theorem exists_isMinimizingMovement [ProperSpace X] {F : X → ℝ}
    (hF : LowerSemicontinuous F) (hbdd : BddBelow (Set.range F)) {h : ℝ} (hh : 0 < h) (x₀ : X) :
    ∃ ρ : ℕ → X, ρ 0 = x₀ ∧ IsMinimizingMovement F h ρ := by
  choose next hnext using exists_isMinimizingMovementStep hF hbdd hh
  exact ⟨fun k => next^[k] x₀, rfl, fun k => by
    simpa [Function.iterate_succ_apply'] using hnext (next^[k] x₀)⟩

end MathlibExt.Analysis.Variational.MinimizingMovement
