/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ViscositySolution.Basic
public import MathlibExt.Analysis.ViscositySolution.Comparison
public import MathlibExt.Analysis.ViscositySolution.Stability
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

open Filter Topology Set Metric MathlibExt.Analysis.ViscositySolution

namespace MathlibExtTest.Analysis.ViscositySolution

/-- Non-vacuity of the consistency theorem: `u(x) = x` is a viscosity solution of the eikonal
equation `(u')² - 1 = 0` on `ℝ`, since it is a `C¹` classical solution. -/
example : IsViscositySolution eikonal univ (fun x : ℝ => x) := by
  refine (isViscositySolution_iff_of_contDiff isOpen_univ contDiff_id).2 fun x _ => ?_
  simp [eikonal]

/-- `|x|` is a viscosity *subsolution* of the eikonal equation (no `C¹` function touches it from
above at `0`), so `not_isViscositySupersolution_abs` fails only on the supersolution side. -/
example : ¬ IsViscositySolution eikonal univ (|·|) := fun h =>
  not_isViscositySupersolution_abs h.2

/-- The model comparison principle applies with jointly satisfiable hypotheses: on the unit ball
of `ℝ²`, for `u + ‖Du‖ = 0`, the constant `0` is a solution and the constant `1` a
supersolution, with `0 ≤ 1` on the boundary. -/
example (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ ball 0 1) : (fun _ => (0 : ℝ)) x ≤ 1 := by
  refine le_of_isViscositySubsolution_of_isViscositySupersolution (u := fun _ => 0)
    (v := fun _ => 1) (f := fun _ => 0) isOpen_ball isBounded_ball one_pos (fun p => ‖p‖)
    continuousOn_const continuousOn_const continuousOn_const ?_ ?_ (fun _ _ => zero_le_one) x hx
  · exact isViscositySubsolution_of_classical isOpen_ball (fun _ _ => differentiableAt_const _)
      fun _ _ => by simp
  · exact isViscositySupersolution_of_classical isOpen_ball (fun _ _ => differentiableAt_const _)
      fun _ _ => by simp

/-- Uniqueness for the model Dirichlet problem, instantiated: two `C¹` classical solutions of
`u + ‖Du‖ = 0` on the unit ball of `ℝ²` with equal boundary values (here both `0`) agree. -/
example : EqOn (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) (fun _ => 0) (ball 0 1) := by
  have h : IsViscositySolution (fun x r p => 1 * r + ‖p‖ - (fun _ => (0 : ℝ)) x) (ball 0 1)
      (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) :=
    isViscositySolution_of_classical isOpen_ball (fun _ _ => differentiableAt_const _)
      fun _ _ => by simp
  exact eqOn_of_isViscositySolution isOpen_ball isBounded_ball one_pos (fun p => ‖p‖)
    continuousOn_const continuousOn_const continuousOn_const h h (fun _ _ => rfl)

/-- Non-vacuity of stability: the classical solutions `uₙ(x) = x + 1/(n+1)` of the eikonal
equation converge locally uniformly to `x`, which the theorem certifies is a viscosity
solution. -/
example : IsViscositySolution eikonal univ (fun x : ℝ => x) := by
  have hF : Continuous fun q : ℝ × ℝ × (ℝ →L[ℝ] ℝ) => eikonal q.1 q.2.1 q.2.2 := by
    unfold eikonal
    fun_prop
  refine IsViscositySolution.of_tendstoLocallyUniformlyOn hF isOpen_univ
    (u := fun n x => x + 1 / ((n : ℝ) + 1)) (fun n => ?_) (fun n => by fun_prop) ?_
  · refine (isViscositySolution_iff_of_contDiff isOpen_univ (by fun_prop)).2 fun x _ => ?_
    simp [eikonal]
  · rw [tendstoLocallyUniformlyOn_univ]
    refine TendstoUniformly.tendstoLocallyUniformly ?_
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn x
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    rw [Real.dist_eq, show x - (x + 1 / ((n : ℝ) + 1)) = -(1 / ((n : ℝ) + 1)) by ring, abs_neg,
      abs_of_pos (by positivity)]
    linarith

/-- The general comparison principle applies with an `x`-dependent equation: for
`u - ‖x‖ = 0` on the unit ball of `ℝ²` (`γ = 1`, structure condition with `ω = id` because
`‖x‖ - ‖y‖ ≤ ‖x - y‖`), the constant `-1` is a subsolution and `1` a supersolution. -/
example (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ ball 0 1) : (fun _ => (-1 : ℝ)) x ≤ 1 := by
  refine le_of_isViscositySubsolution_of_isViscositySupersolution_of_proper (u := fun _ => -1)
    (v := fun _ => 1) isOpen_ball isBounded_ball (fun x r _ => r - ‖x‖) one_pos
    (fun _ _ r s _ _ => by simp) id (tendsto_nhdsWithin_of_tendsto_nhds (by
      simpa using (continuous_id.tendsto (0 : ℝ))))
    (fun x _ y _ r α hα => ?_) continuousOn_const continuousOn_const ?_ ?_
    (fun _ _ => by norm_num) x hx
  · have h1 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
    have h2 : 0 ≤ α * ‖x - y‖ ^ 2 := by positivity
    simp only [id]
    linarith
  · exact isViscositySubsolution_of_classical isOpen_ball (fun _ _ => differentiableAt_const _)
      fun y _ => show (-1 : ℝ) - ‖y‖ ≤ 0 by linarith [norm_nonneg y]
  · exact isViscositySupersolution_of_classical isOpen_ball (fun _ _ => differentiableAt_const _)
      fun y hy => by
        have : ‖y‖ < 1 := by simpa using hy
        show (0 : ℝ) ≤ 1 - ‖y‖
        linarith

/-- The hypotheses of the wanted comparison principle
(`WantedExt.Analysis.ViscositySolution.ComparisonHopfLaxWanted`) are jointly satisfiable:
`F(x, r, p) = r` is proper with `γ = 1` and satisfies the structure condition with `ω = id`. -/
example : ∀ (x y : EuclideanSpace ℝ (Fin 2)) (r α : ℝ), 0 < α →
    (fun _ (r : ℝ) (_ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) => r) y r (α • innerSL ℝ (x - y)) -
      (fun _ (r : ℝ) (_ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) => r) x r (α • innerSL ℝ (x - y)) ≤
      id (α * ‖x - y‖ ^ 2 + ‖x - y‖) := by
  intro x y r α hα
  simp only [sub_self, id]
  positivity

/-- The hypotheses of the wanted Hopf–Lax theorem are jointly satisfiable: `H(p) = ‖p‖²` is
convex and superlinear on the dual of `ℝ²`, and `g = 0` is bounded and Lipschitz. -/
example : ConvexOn ℝ univ (fun p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => ‖p‖ ^ 2) ∧
    Tendsto (fun p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => ‖p‖ ^ 2 / ‖p‖)
      (cocompact _) atTop ∧
    (∃ K, LipschitzWith K (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ))) := by
  refine ⟨(convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2, ?_,
    ⟨0, LipschitzWith.const 0⟩⟩
  refine tendsto_norm_cocompact_atTop.congr' ?_
  filter_upwards [(hasBasis_cocompact.mem_iff).2 ⟨closedBall 0 1, isCompact_closedBall 0 1,
    subset_refl _⟩] with p hp
  have hp0 : ‖p‖ ≠ 0 := by
    intro h
    exact hp (by simp [h])
  field_simp

end MathlibExtTest.Analysis.ViscositySolution
