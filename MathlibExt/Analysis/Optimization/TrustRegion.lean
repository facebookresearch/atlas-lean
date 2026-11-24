/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The trust-region subproblem

At an iterate with gradient `g` and Hessian approximation `B`, a trust-region method minimises the
quadratic model `q(s) = ⟪g, s⟫ + ½ ⟪B s, s⟫` over the ball `‖s‖ ≤ Δ` (the standard trust-region
subproblem (2.3)-(2.4) of Y. Yuan, *Recent advances in trust region algorithms*, Math. Program.
151 (2015), 249-281). The predicted reduction of a trial step `s` is `q(0) - q(s) = -q(s)`.

This file proves

* Powell's sufficient model decrease (Yuan 2015, inequality (2.5)): a step along `-g` inside the
  trust region, and hence any exact solution of the subproblem, achieves
  `-q(s) ≥ ½ ‖g‖ min (Δ, ‖g‖ / M)` whenever `⟪B v, v⟫ ≤ M ‖v‖²` (for instance `M ≥ ‖B‖`);
* the sufficiency half of the Gay / Moré–Sorensen characterisation of global solutions: if
  `(B + μ I) s = -g`, `B + μ I` is positive semidefinite, `μ ≥ 0`, `‖s‖ ≤ Δ` and
  `μ (Δ - ‖s‖) = 0`, then `s` is a global minimiser of the model on the ball.
-/

@[expose] public section

namespace MathlibExt.Analysis.Optimization.TrustRegion

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Quadratic trust-region model.** For a gradient `g` and a linear operator `B` (a Hessian
approximation), `q(s) = ⟪g, s⟫ + ½ ⟪B s, s⟫`; the constant term `f(x)` is dropped, so the predicted
reduction of a step `s` is `-q(s)` (Yuan, Math. Program. 151 (2015), model (2.3)). -/
noncomputable def trustRegionModel (g : E) (B : E →L[ℝ] E) (s : E) : ℝ :=
  ⟪g, s⟫ + 1 / 2 * ⟪B s, s⟫

@[simp] theorem trustRegionModel_zero (g : E) (B : E →L[ℝ] E) : trustRegionModel g B 0 = 0 := by
  simp [trustRegionModel]

/-- **Curvature bound from an operator-norm bound.** If `‖B‖ ≤ M`, then `⟪B v, v⟫ ≤ M ‖v‖²` for
every `v`, by the Cauchy–Schwarz inequality. -/
theorem inner_apply_self_le_of_opNorm_le {B : E →L[ℝ] E} {M : ℝ} (hB : ‖B‖ ≤ M) (v : E) :
    ⟪B v, v⟫ ≤ M * ‖v‖ ^ 2 := by
  calc ⟪B v, v⟫ ≤ ‖B v‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ ‖B‖ * ‖v‖ * ‖v‖ := by gcongr; exact B.le_opNorm v
    _ ≤ M * ‖v‖ * ‖v‖ := by gcongr
    _ = M * ‖v‖ ^ 2 := by ring

/-- **Cauchy decrease of the trust-region model.** Let `Δ ≥ 0`, `M > 0` and
`⟪B v, v⟫ ≤ M ‖v‖²` for all `v`. Then some step `s = -t • g` along the steepest-descent direction,
with `t ≥ 0` and `‖s‖ ≤ Δ`, has predicted reduction `-q(s) ≥ ½ ‖g‖ min (Δ, ‖g‖ / M)`.

This is the sufficient model decrease (2.5) of Y. Yuan, Math. Program. 151 (2015), there credited
to Powell and stated with `M = ‖B‖`; the source notes that the minimiser of the model along the
steepest-descent direction inside the trust region satisfies it. The step used here is
`t = min (Δ / ‖g‖, 1 / M)`. -/
theorem exists_cauchy_step {g : E} {B : E →L[ℝ] E} {Δ M : ℝ} (hΔ : 0 ≤ Δ) (hM : 0 < M)
    (hB : ∀ v, ⟪B v, v⟫ ≤ M * ‖v‖ ^ 2) :
    ∃ t : ℝ, 0 ≤ t ∧ ‖t • g‖ ≤ Δ ∧
      1 / 2 * ‖g‖ * min Δ (‖g‖ / M) ≤ -trustRegionModel g B (-(t • g)) := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact ⟨0, le_rfl, by simpa using hΔ, by simp⟩
  have hG : 0 < ‖g‖ := norm_pos_iff.mpr hg
  set t := min (Δ / ‖g‖) (1 / M) with ht
  have ht0 : 0 ≤ t := le_min (by positivity) (by positivity)
  have htM : t * M ≤ 1 := by
    calc t * M ≤ 1 / M * M := by gcongr; exact min_le_right _ _
      _ = 1 := by field_simp
  have htg : t * ‖g‖ = min Δ (‖g‖ / M) := by
    rw [ht, min_mul_of_nonneg _ _ hG.le]
    congr 1 <;> field_simp
  refine ⟨t, ht0, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, htg]
    exact min_le_left _ _
  · have hq : trustRegionModel g B (-(t • g)) = -t * ‖g‖ ^ 2 + 1 / 2 * t ^ 2 * ⟪B g, g⟫ := by
      simp only [trustRegionModel, map_neg, map_smul, inner_neg_right, inner_neg_left,
        real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, neg_neg]
      ring
    have h1 : t ^ 2 * ⟪B g, g⟫ ≤ t ^ 2 * (M * ‖g‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hB g) (sq_nonneg t)
    have h2 : t ^ 2 * (M * ‖g‖ ^ 2) ≤ t * ‖g‖ ^ 2 := by
      have : t * (t * M) * ‖g‖ ^ 2 ≤ t * 1 * ‖g‖ ^ 2 := by gcongr
      nlinarith
    rw [hq, ← htg]
    nlinarith

/-- **Sufficient decrease of an exact trust-region step.** If `s` minimises the model over the
ball `‖s‖ ≤ Δ`, `M > 0` and `⟪B v, v⟫ ≤ M ‖v‖²` for all `v`, then the predicted reduction satisfies
`-q(s) ≥ ½ ‖g‖ min (Δ, ‖g‖ / M)` (Y. Yuan, Math. Program. 151 (2015), inequality (2.5), credited
there to Powell; take `M = ‖B‖` when `B ≠ 0`, see `inner_apply_self_le_of_opNorm_le`). -/
theorem pred_ge_of_isMinOn {g s : E} {B : E →L[ℝ] E} {Δ M : ℝ} (hM : 0 < M)
    (hB : ∀ v, ⟪B v, v⟫ ≤ M * ‖v‖ ^ 2) (hs : ‖s‖ ≤ Δ)
    (hmin : ∀ p : E, ‖p‖ ≤ Δ → trustRegionModel g B s ≤ trustRegionModel g B p) :
    1 / 2 * ‖g‖ * min Δ (‖g‖ / M) ≤ -trustRegionModel g B s := by
  obtain ⟨t, -, htΔ, hdec⟩ := exists_cauchy_step ((norm_nonneg s).trans hs) hM hB
  have := hmin (-(t • g)) (by rwa [norm_neg])
  linarith

/-- **Sufficient optimality condition for the trust-region subproblem.** Let `B` be symmetric,
`μ ≥ 0`, `B s + μ • s = -g`, `⟪B v + μ • v, v⟫ ≥ 0` for all `v` and `μ (Δ - ‖s‖) = 0`.
Then `q(s) ≤ q(p)` for every `p` with `‖p‖ ≤ Δ`, where `q(p) = ⟪g, p⟫ + ½ ⟪B p, p⟫`; so if moreover
`‖s‖ ≤ Δ`, then `s` is a global minimiser of the model on the trust region. (Feasibility of `s` is
not needed for the inequality itself.)

This is the sufficiency half of the characterisation of global solutions of the trust-region
subproblem, due to Gay and to Moré and Sorensen as stated in Theorem 2.1 (the necessity half) of
N. I. M. Gould, D. P. Robinson and H. S. Thorne, *On solving trust-region and other regularised
subproblems in optimization*, Math. Program. Comput. 2 (2010) (with `M = I`). The proof is the
identity `q(p) - q(s) = ½ ⟪(B + μ I)(p - s), p - s⟫ + ½ μ (‖s‖² - ‖p‖²)`. -/
theorem trustRegionModel_le_of_optimality {g s : E} {B : E →L[ℝ] E} {Δ μ : ℝ}
    (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (hμ : 0 ≤ μ) (heq : B s + μ • s = -g)
    (hpsd : ∀ v, 0 ≤ ⟪B v + μ • v, v⟫) (hcompl : μ * (Δ - ‖s‖) = 0) :
    ∀ p : E, ‖p‖ ≤ Δ → trustRegionModel g B s ≤ trustRegionModel g B p := by
  intro p hp
  have hg : g = -(B s + μ • s) := by rw [heq, neg_neg]
  have hw := hpsd (p - s)
  simp only [map_sub, inner_sub_left, inner_sub_right, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hw
  have hBps : ⟪B p, s⟫ = ⟪B s, p⟫ := by rw [hsymm, real_inner_comm]
  have hsp : ⟪s, p⟫ = ⟪p, s⟫ := real_inner_comm _ _
  have hss : μ * ‖s‖ ^ 2 = μ * Δ ^ 2 := by
    have h : μ * ‖s‖ ^ 2 - μ * Δ ^ 2 = -(μ * (Δ - ‖s‖)) * (‖s‖ + Δ) := by ring
    rw [hcompl] at h
    linarith
  have hpp : μ * ‖p‖ ^ 2 ≤ μ * Δ ^ 2 := by
    have := (norm_nonneg p)
    gcongr
  simp only [trustRegionModel, hg, inner_neg_left, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  nlinarith

end MathlibExt.Analysis.Optimization.TrustRegion
