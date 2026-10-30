/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.MetricSpace.Antilipschitz

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Tikhonov regularization in Hilbert spaces

For a bounded linear operator `A : H →L[𝕜] K` between Hilbert spaces, a
right-hand side `b : K`, and a regularization parameter `Λ > 0`, the
*Tikhonov functional* is

  `J(x) = ‖A x - b‖ ^ 2 + Λ * ‖x‖ ^ 2`.

Minimizing `J` is the standard way to stabilize an ill-posed inverse
problem: the penalty term `Λ * ‖x‖ ^ 2` selects, among all approximate
solutions of `A x = b`, one of controlled norm. This file proves:

* The *normal equations*: the minimizer is characterized by
  `(A† ∘L A + Λ • 1) x = A† b`, where the normal operator
  `A† ∘L A + Λ • 1` is self-adjoint and bounded below by `Λ`.
* The normal operator is a unit, so the normal equations are always
  solvable, and the solution is the unique minimizer of `J`.
* A stability bound `‖x‖ ≤ ‖A‖ * ‖b‖ / Λ` for the minimizer, and the
  consequence that minimizers tend to `0` as `Λ → ∞`.

This is a companion to the Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`
(projection and adjoint material). It is not one of the 72 v1 targets.
It is distinct from batch 124's representer theorem, which concerns a
minimizer of a general functional of finitely many linear measurements
and gives no normal operator, no inverse formula, and no `Λ → ∞`
behaviour; and from Mathlib's Lax–Milgram theorem, which is stated for
real bilinear forms, while the argument here works over any `RCLike`
field (in particular `ℂ`) via adjoints.

## References

* A. N. Tikhonov, "Regularization of incorrectly posed problems",
  *Doklady Akademii Nauk SSSR* **153** (1963).
* A. N. Tikhonov and V. Y. Arsenin, *Solutions of Ill-Posed Problems*,
  John Wiley & Sons, 1977.

Tikhonov's paper is the original regularization source. Tikhonov and
Arsenin's monograph treats the quadratic regularization method and its
normal-equation formulation. The bounded-operator Hilbert-space results
proved here are the normal operator's invertibility for `Λ > 0`, the
unique minimizer, and the elementary stability estimate
`‖x‖ ≤ ‖A‖ * ‖b‖ / Λ`. The `Λ → ∞` limit is a direct consequence of
that estimate, proved here by comparison with `‖A‖ * ‖b‖ / Λ → 0`.
The v1 Hilbert-space file supplies projection and adjoint background;
it contains no Tikhonov regularization statement.

## Main declarations

* `tikhonovFunctional` : the Tikhonov functional `J`.
* `tikhonovOperator` : the normal operator `A† ∘L A + Λ • 1`.
* `isSelfAdjoint_tikhonovOperator` : the normal operator is self-adjoint.
* `tikhonovOperator_le_norm` : the normal operator is bounded below by `Λ`.
* `isUnit_tikhonovOperator` : the normal operator is a unit for `Λ > 0`.
* `tikhonovFunctional_add_of_normal_equations` : the quadratic identity
  `J(x) = J(x₀) + ‖A (x - x₀)‖ ^ 2 + Λ * ‖x - x₀‖ ^ 2` when `x₀`
  solves the normal equations.
* `existsUnique_tikhonov_minimizer` : `J` has a unique minimizer.
* `norm_le_of_tikhonov_normal_equations` : the stability bound
  `‖x‖ ≤ ‖A‖ * ‖b‖ / Λ`.
* `tendsto_tikhonov_solution_zero` : solutions tend to `0` as `Λ → ∞`.
-/

@[expose] public section

open Filter Metric Set Topology
open scoped InnerProduct InnerProductSpace

namespace MathlibExt.Analysis.FunctionalAnalysis.TikhonovRegularization

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- The Tikhonov (ridge) functional `J(x) = ‖A x - b‖ ^ 2 + Λ * ‖x‖ ^ 2`. -/
noncomputable def tikhonovFunctional (A : H →L[𝕜] K) (b : K) (Λ : ℝ) (x : H) : ℝ :=
  ‖A x - b‖ ^ 2 + Λ * ‖x‖ ^ 2

/-- The normal operator `A† ∘L A + Λ • 1` of the Tikhonov problem. -/
noncomputable def tikhonovOperator (A : H →L[𝕜] K) (Λ : ℝ) : H →L[𝕜] H :=
  A† ∘L A + (Λ : 𝕜) • (1 : H →L[𝕜] H)

@[simp]
theorem tikhonovOperator_apply (A : H →L[𝕜] K) (Λ : ℝ) (x : H) :
    tikhonovOperator A Λ x = (A†) (A x) + (Λ : 𝕜) • x := by
  simp [tikhonovOperator]

/-- The inner product of the normal operator applied to `x` with `x` itself. -/
theorem tikhonovOperator_inner_self (A : H →L[𝕜] K) (Λ : ℝ) (x : H) :
    ⟪tikhonovOperator A Λ x, x⟫_𝕜 = ((‖A x‖ ^ 2 + Λ * ‖x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [tikhonovOperator_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    inner_smul_real_left, RCLike.real_smul_eq_coe_mul, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]
  push_cast
  ring

/-- The real part of the inner product of the normal operator applied to `x`
with `x` itself. -/
theorem re_inner_tikhonovOperator_self (A : H →L[𝕜] K) (Λ : ℝ) (x : H) :
    RCLike.re ⟪tikhonovOperator A Λ x, x⟫_𝕜 = ‖A x‖ ^ 2 + Λ * ‖x‖ ^ 2 := by
  rw [tikhonovOperator_inner_self, RCLike.ofReal_re]

/-- The normal operator is self-adjoint, for every real `Λ`. -/
theorem isSelfAdjoint_tikhonovOperator (A : H →L[𝕜] K) (Λ : ℝ) :
    IsSelfAdjoint (tikhonovOperator A Λ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, tikhonovOperator_apply, inner_add_left,
    inner_add_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right, inner_smul_real_left, inner_smul_real_right]

/-- The normal operator is bounded below by `Λ`, for every real `Λ`. -/
theorem tikhonovOperator_le_norm (A : H →L[𝕜] K) (Λ : ℝ) (x : H) :
    Λ * ‖x‖ ≤ ‖tikhonovOperator A Λ x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 : Λ * ‖x‖ ^ 2 ≤ RCLike.re ⟪tikhonovOperator A Λ x, x⟫_𝕜 := by
      rw [re_inner_tikhonovOperator_self]
      linarith [sq_nonneg ‖A x‖]
    have h2 : RCLike.re ⟪tikhonovOperator A Λ x, x⟫_𝕜
        ≤ ‖tikhonovOperator A Λ x‖ * ‖x‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h1r : (Λ * ‖x‖) * ‖x‖ ≤ ‖tikhonovOperator A Λ x‖ * ‖x‖ := by
      rw [mul_assoc, ← pow_two]
      exact h1.trans h2
    exact le_of_mul_le_mul_right h1r hnorm

/-- The normal operator has trivial kernel when `Λ > 0`. -/
theorem ker_tikhonovOperator_eq_bot (A : H →L[𝕜] K) (Λ : ℝ) (hΛ : 0 < Λ) :
    (tikhonovOperator A Λ : H →ₗ[𝕜] H).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h0 : tikhonovOperator A Λ x = 0 := hx
  have h := tikhonovOperator_le_norm A Λ x
  rw [h0, norm_zero] at h
  have hx0 : ‖x‖ = 0 := by nlinarith [norm_nonneg x, hΛ]
  exact norm_eq_zero.mp hx0

/-- The normal operator has closed range when `Λ > 0`, since it is bounded below. -/
theorem isClosed_range_tikhonovOperator (A : H →L[𝕜] K) (Λ : ℝ) (hΛ : 0 < Λ) :
    IsClosed (Set.range (tikhonovOperator A Λ)) := by
  have hanti : AntilipschitzWith ⟨Λ⁻¹, inv_nonneg.mpr hΛ.le⟩ (tikhonovOperator A Λ) := by
    apply ContinuousLinearMap.antilipschitz_of_bound
    intro x
    show ‖x‖ ≤ Λ⁻¹ * ‖tikhonovOperator A Λ x‖
    rw [le_inv_mul_iff₀ hΛ]
    exact tikhonovOperator_le_norm A Λ x
  exact hanti.isClosed_range (tikhonovOperator A Λ).uniformContinuous

/-- The normal operator is surjective when `Λ > 0`: its range is closed and
its orthogonal complement is its kernel, which is trivial since the operator
is self-adjoint. -/
theorem range_tikhonovOperator_eq_top (A : H →L[𝕜] K) (Λ : ℝ) (hΛ : 0 < Λ) :
    (tikhonovOperator A Λ : H →ₗ[𝕜] H).range = ⊤ := by
  have hclosed : IsClosed ((tikhonovOperator A Λ : H →ₗ[𝕜] H).range : Set H) := by
    rw [LinearMap.coe_range]
    exact isClosed_range_tikhonovOperator A Λ hΛ
  have horth : (tikhonovOperator A Λ : H →ₗ[𝕜] H).rangeᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range,
      IsSelfAdjoint.adjoint_eq (isSelfAdjoint_tikhonovOperator A Λ)]
    exact ker_tikhonovOperator_eq_bot A Λ hΛ
  have htop : (tikhonovOperator A Λ : H →ₗ[𝕜] H).range.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, horth,
      Submodule.bot_orthogonal_eq_top]
  rwa [IsClosed.submodule_topologicalClosure_eq hclosed] at htop

/-- The normal operator is bijective when `Λ > 0`. -/
theorem bijective_tikhonovOperator (A : H →L[𝕜] K) (Λ : ℝ) (hΛ : 0 < Λ) :
    Function.Bijective (tikhonovOperator A Λ) := by
  refine ⟨?_, ?_⟩
  · exact LinearMap.ker_eq_bot.mp (ker_tikhonovOperator_eq_bot A Λ hΛ)
  · intro y
    have hymem : y ∈ (tikhonovOperator A Λ : H →ₗ[𝕜] H).range := by
      rw [range_tikhonovOperator_eq_top A Λ hΛ]
      exact trivial
    obtain ⟨x, hx⟩ := hymem
    exact ⟨x, hx⟩

/-- The normal operator is a unit when `Λ > 0`. -/
theorem isUnit_tikhonovOperator (A : H →L[𝕜] K) (Λ : ℝ) (hΛ : 0 < Λ) :
    IsUnit (tikhonovOperator A Λ) :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr (bijective_tikhonovOperator A Λ hΛ)

/-- The normal equations are solvable when `Λ > 0`. -/
theorem exists_tikhonov_normal_equations (A : H →L[𝕜] K) (b : K) (Λ : ℝ)
    (hΛ : 0 < Λ) : ∃ x, tikhonovOperator A Λ x = (A†) b :=
  (bijective_tikhonovOperator A Λ hΛ).surjective ((A†) b)

/-- The quadratic identity for the Tikhonov functional around a solution of
the normal equations: the cross term vanishes by the normal equations. -/
theorem tikhonovFunctional_add_of_normal_equations (A : H →L[𝕜] K) (b : K) (Λ : ℝ)
    {x₀ : H} (h₀ : tikhonovOperator A Λ x₀ = (A†) b) (x : H) :
    tikhonovFunctional A b Λ x
      = tikhonovFunctional A b Λ x₀ + ‖A (x - x₀)‖ ^ 2 + Λ * ‖x - x₀‖ ^ 2 := by
  set d := x - x₀ with hd
  have h1 : ‖A x - b‖ ^ 2
      = ‖A x₀ - b‖ ^ 2 + 2 * RCLike.re ⟪A x₀ - b, A d⟫_𝕜 + ‖A d‖ ^ 2 := by
    have hA : A x - b = (A x₀ - b) + A d := by
      rw [hd, map_sub]
      abel
    rw [hA]
    exact norm_add_sq _ _
  have h2 : ‖x‖ ^ 2 = ‖x₀‖ ^ 2 + 2 * RCLike.re ⟪x₀, d⟫_𝕜 + ‖d‖ ^ 2 := by
    have hx : x = x₀ + d := by
      rw [hd]
      abel
    conv_lhs => rw [hx]
    exact norm_add_sq _ _
  have hcross : RCLike.re ⟪A x₀ - b, A d⟫_𝕜 + Λ * RCLike.re ⟪x₀, d⟫_𝕜 = 0 := by
    have hc1 : ⟪A x₀ - b, A d⟫_𝕜 = ⟪(A†) (A x₀ - b), d⟫_𝕜 :=
      (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    have hc2 : (A†) (A x₀ - b) = ((-Λ : ℝ) : 𝕜) • x₀ := by
      have hS := tikhonovOperator_apply A Λ x₀
      rw [map_sub, ← h₀, hS]
      module
    rw [hc1, hc2, inner_smul_real_left, RCLike.smul_re, neg_mul]
    exact neg_add_cancel _
  unfold tikhonovFunctional
  rw [h1, h2]
  linarith [hcross]

/-- A solution of the normal equations minimizes the Tikhonov functional. -/
theorem isMinOn_tikhonovFunctional_of_normal_equations (A : H →L[𝕜] K) (b : K) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) {x₀ : H} (h₀ : tikhonovOperator A Λ x₀ = (A†) b) :
    IsMinOn (tikhonovFunctional A b Λ) univ x₀ := by
  intro x _
  show tikhonovFunctional A b Λ x₀ ≤ tikhonovFunctional A b Λ x
  rw [tikhonovFunctional_add_of_normal_equations A b Λ h₀ x]
  have h1 : 0 ≤ ‖A (x - x₀)‖ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ Λ * ‖x - x₀‖ ^ 2 := mul_nonneg hΛ (sq_nonneg _)
  linarith

/-- A minimizer of the Tikhonov functional equals a solution of the normal
equations, when `Λ > 0`. -/
theorem eq_of_isMinOn_tikhonovFunctional (A : H →L[𝕜] K) (b : K) (Λ : ℝ)
    (hΛ : 0 < Λ) {x₀ x : H} (h₀ : tikhonovOperator A Λ x₀ = (A†) b)
    (hmin : IsMinOn (tikhonovFunctional A b Λ) univ x) : x = x₀ := by
  have hle : tikhonovFunctional A b Λ x₀ + ‖A (x - x₀)‖ ^ 2 + Λ * ‖x - x₀‖ ^ 2
      ≤ tikhonovFunctional A b Λ x₀ := by
    have h := hmin (mem_univ x₀)
    rwa [tikhonovFunctional_add_of_normal_equations A b Λ h₀ x] at h
  have h1 : Λ * ‖x - x₀‖ ^ 2 ≤ 0 := by linarith [sq_nonneg ‖A (x - x₀)‖]
  have h3 : ‖x - x₀‖ ^ 2 ≤ 0 :=
    le_of_mul_le_mul_left (by simpa using h1) hΛ
  have hnorm : ‖x - x₀‖ = 0 := by
    have h4 : ‖x - x₀‖ ^ 2 = 0 := le_antisymm h3 (sq_nonneg _)
    exact (pow_eq_zero_iff two_ne_zero).mp h4
  exact sub_eq_zero.1 (norm_eq_zero.mp hnorm)

/-- The Tikhonov functional has a unique minimizer when `Λ > 0`. -/
theorem existsUnique_tikhonov_minimizer (A : H →L[𝕜] K) (b : K) (Λ : ℝ)
    (hΛ : 0 < Λ) : ∃! x, ∀ y, tikhonovFunctional A b Λ x ≤ tikhonovFunctional A b Λ y := by
  obtain ⟨x₀, h₀⟩ := exists_tikhonov_normal_equations A b Λ hΛ
  refine ⟨x₀, ?_, ?_⟩
  · intro y
    exact isMinOn_tikhonovFunctional_of_normal_equations A b Λ hΛ.le h₀ (mem_univ y)
  · intro x hxmin
    exact eq_of_isMinOn_tikhonovFunctional A b Λ hΛ h₀ (fun y _ => hxmin y)

/-- Stability bound for a solution of the normal equations. -/
theorem norm_le_of_tikhonov_normal_equations (A : H →L[𝕜] K) (b : K) (Λ : ℝ)
    (hΛ : 0 < Λ) {x : H} (h : tikhonovOperator A Λ x = (A†) b) :
    ‖x‖ ≤ ‖A‖ * ‖b‖ / Λ := by
  by_cases hx : x = 0
  · subst hx
    simp only [norm_zero]
    exact div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hΛ.le
  · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have key : Λ * ‖x‖ ^ 2 ≤ ‖A‖ * ‖b‖ * ‖x‖ := by
      have h1 : Λ * ‖x‖ ^ 2 ≤ RCLike.re ⟪tikhonovOperator A Λ x, x⟫_𝕜 := by
        rw [re_inner_tikhonovOperator_self]
        nlinarith [sq_nonneg ‖A x‖]
      have h2 : RCLike.re ⟪tikhonovOperator A Λ x, x⟫_𝕜 = RCLike.re ⟪b, A x⟫_𝕜 := by
        rw [h, ContinuousLinearMap.adjoint_inner_left]
      have h3 : RCLike.re ⟪b, A x⟫_𝕜 ≤ ‖b‖ * ‖A x‖ :=
        (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      have h4 : ‖A x‖ ≤ ‖A‖ * ‖x‖ := ContinuousLinearMap.le_opNorm A x
      calc Λ * ‖x‖ ^ 2 ≤ RCLike.re ⟪tikhonovOperator A Λ x, x⟫_𝕜 := h1
        _ = RCLike.re ⟪b, A x⟫_𝕜 := h2
        _ ≤ ‖b‖ * ‖A x‖ := h3
        _ ≤ ‖b‖ * (‖A‖ * ‖x‖) := by gcongr
        _ = ‖A‖ * ‖b‖ * ‖x‖ := by ring
    have key2 : Λ * ‖x‖ ≤ ‖A‖ * ‖b‖ := by
      have key' : (Λ * ‖x‖) * ‖x‖ ≤ (‖A‖ * ‖b‖) * ‖x‖ := by
        rw [mul_assoc, ← pow_two]
        exact key
      exact le_of_mul_le_mul_right key' hnorm
    rw [le_div_iff₀ hΛ, mul_comm]
    exact key2

/-- Solutions of the Tikhonov normal equations tend to `0` as `Λ → ∞`. -/
theorem tendsto_tikhonov_solution_zero (A : H →L[𝕜] K) (b : K) (Λ : ℕ → ℝ)
    (hΛ : ∀ n, 0 < Λ n) (hΛtop : Tendsto Λ atTop atTop) (x : ℕ → H)
    (hx : ∀ n, tikhonovOperator A (Λ n) (x n) = (A†) b) :
    Tendsto x atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hgtop : Tendsto (fun n => ‖A‖ * ‖b‖ / Λ n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (Λ n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hΛtop
    have h2 := h1.const_mul (‖A‖ * ‖b‖)
    simpa [div_eq_mul_inv] using h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgtop
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n =>
      norm_le_of_tikhonov_normal_equations A b (Λ n) (hΛ n) (hx n)

end MathlibExt.Analysis.FunctionalAnalysis.TikhonovRegularization
