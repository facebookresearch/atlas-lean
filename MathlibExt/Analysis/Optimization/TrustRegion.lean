/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
  `μ (Δ - ‖s‖) = 0`, then `s` is a global minimiser of the model on the ball;
* the converse: every global minimiser for positive radius has such a multiplier.
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

section

open Filter Set
open scoped Topology

private theorem model_expand {g s : E} {B : E →L[ℝ] E}
    (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (v : E) (t : ℝ) :
    2 * (trustRegionModel g B (s + t • v) - trustRegionModel g B s) =
      2 * t * ⟪g + B s, v⟫ + t ^ 2 * ⟪B v, v⟫ := by
  have heq : ⟪B v, s⟫ = ⟪B s, v⟫ := (hsymm v s).trans (real_inner_comm _ _)
  simp only [trustRegionModel, map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, heq]
  ring

private theorem support {g s : E} {B : E →L[ℝ] E} {Δ : ℝ}
    (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (hs : ‖s‖ ≤ Δ)
    (hmin : ∀ p : E, ‖p‖ ≤ Δ → trustRegionModel g B s ≤ trustRegionModel g B p)
    (p : E) (hp : ‖p‖ ≤ Δ) : 0 ≤ ⟪g + B s, p - s⟫ := by
  have hs' : s ∈ Metric.closedBall (0 : E) Δ := by simpa [Metric.mem_closedBall] using hs
  have hp' : p ∈ Metric.closedBall (0 : E) Δ := by simpa [Metric.mem_closedBall] using hp
  have hc : Continuous fun t : ℝ => 2 * ⟪g + B s, p - s⟫ + t * ⟪B (p - s), p - s⟫ := by
    fun_prop
  have hl : Tendsto (fun t : ℝ => 2 * ⟪g + B s, p - s⟫ + t * ⟪B (p - s), p - s⟫)
      (𝓝[>] 0) (𝓝 (2 * ⟪g + B s, p - s⟫)) := by
    simpa using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hh := ge_of_tendsto hl (show ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 ≤ 2 * ⟪g + B s, p - s⟫ + t * ⟪B (p - s), p - s⟫ from by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hm := (convex_closedBall (0 : E) Δ).add_smul_sub_mem hs' hp' ⟨ht.1.le, ht.2⟩
    have hh := hmin (s + t • (p - s)) (by simpa [Metric.mem_closedBall] using hm)
    have hn : 0 ≤ t * (2 * ⟪g + B s, p - s⟫ + t * ⟪B (p - s), p - s⟫) := by
      rw [show t * (2 * ⟪g + B s, p - s⟫ + t * ⟪B (p - s), p - s⟫) =
        2 * t * ⟪g + B s, p - s⟫ + t ^ 2 * ⟪B (p - s), p - s⟫ by ring,
        ← model_expand hsymm]
      linarith
    exact nonneg_of_mul_nonneg_right hn ht.1)
  linarith

private theorem multiplier {g s : E} {B : E →L[ℝ] E} {Δ : ℝ}
    (hΔ : 0 < Δ) (hs : ‖s‖ ≤ Δ)
    (hsupport : ∀ p : E, ‖p‖ ≤ Δ → 0 ≤ ⟪g + B s, p - s⟫) :
    ∃ μ : ℝ, 0 ≤ μ ∧ B s + μ • s = -g ∧ μ * (‖s‖ - Δ) = 0 := by
  let G := g + B s
  by_cases hG : G = 0
  · refine ⟨0, le_rfl, ?_, by simp⟩
    have h : g + B s = 0 := hG
    simpa using (eq_neg_of_add_eq_zero_right h : B s = -g)
  have hGn : 0 < ‖G‖ := norm_pos_iff.mpr hG
  let p : E := (-Δ / ‖G‖) • G
  have hp : ‖p‖ ≤ Δ := by
    dsimp [p]
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hΔ, abs_of_pos hGn]
    exact le_of_eq (div_mul_cancel₀ _ hGn.ne')
  have hIp : ⟪G, p⟫ = -(Δ * ‖G‖) := by
    simp only [p, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h1 := hsupport p hp
  change 0 ≤ ⟪G, p - s⟫ at h1
  rw [inner_sub_right, hIp] at h1
  have h2 := real_inner_le_norm G (-s)
  rw [inner_neg_right, norm_neg] at h2
  have h3 := mul_le_mul_of_nonneg_left hs hGn.le
  have hIs : ⟪G, s⟫ = -(Δ * ‖G‖) := by linarith
  have hsΔ : ‖s‖ = Δ := by
    refine le_antisymm hs ?_
    have hc : ‖G‖ * Δ ≤ ‖G‖ * ‖s‖ := by linarith
    exact le_of_mul_le_mul_left hc hGn
  let μ : ℝ := ‖G‖ / Δ
  have hμ : 0 ≤ μ := div_nonneg hGn.le hΔ.le
  have hμΔ : μ * Δ = ‖G‖ := div_mul_cancel₀ _ hΔ.ne'
  have hnorm : ‖G + μ • s‖ ^ 2 = 0 := by
    rw [norm_add_sq_real, real_inner_smul_right, hIs, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hμ, hsΔ, hμΔ]
    calc ‖G‖ ^ 2 + 2 * (μ * -(Δ * ‖G‖)) + ‖G‖ ^ 2 =
        ‖G‖ ^ 2 - 2 * ‖G‖ * (μ * Δ) + ‖G‖ ^ 2 := by ring
      _ = 0 := by rw [hμΔ]; ring
  have hvec : G + μ • s = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (G + μ • s)]
  refine ⟨μ, hμ, ?_, by simp [hsΔ]⟩
  have hz : g + (B s + μ • s) = 0 := by simpa only [G, add_assoc] using hvec
  exact eq_neg_of_add_eq_zero_right hz

private theorem shifted_expand {g s : E} {B : E →L[ℝ] E} {μ : ℝ}
    (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (heq : B s + μ • s = -g) (v : E) (t : ℝ) :
    2 * (trustRegionModel g B (s + t • v) - trustRegionModel g B s) =
      t ^ 2 * ⟪B v + μ • v, v⟫ + μ * (‖s‖ ^ 2 - ‖s + t • v‖ ^ 2) := by
  have hG : g + B s = -(μ • s) := by
    calc g + B s = -(B s + μ • s) + B s := by rw [heq, neg_neg]
      _ = -(μ • s) := by abel
  rw [model_expand hsymm, hG, norm_add_sq_real]
  simp only [inner_neg_left, inner_add_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private theorem shifted_nonneg {g s : E} {B : E →L[ℝ] E} {μ Δ : ℝ}
    (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (heq : B s + μ • s = -g)
    (hmin : ∀ p : E, ‖p‖ ≤ Δ → trustRegionModel g B s ≤ trustRegionModel g B p)
    (v : E) {t : ℝ} (ht : t ≠ 0) (hp : ‖s + t • v‖ ≤ Δ)
    (hzero : μ * (‖s‖ ^ 2 - ‖s + t • v‖ ^ 2) = 0) : 0 ≤ ⟪B v + μ • v, v⟫ := by
  have hm := hmin _ hp
  have h := shifted_expand hsymm heq v t
  rw [hzero, add_zero] at h
  have hx : 0 ≤ t ^ 2 * ⟪B v + μ • v, v⟫ := by rw [← h]; linarith
  exact nonneg_of_mul_nonneg_right hx (sq_pos_of_ne_zero ht)

private theorem shifted_psd {g s : E} {B : E →L[ℝ] E} {Δ μ : ℝ}
    (hΔ : 0 < Δ) (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (hs : ‖s‖ ≤ Δ)
    (hmin : ∀ p : E, ‖p‖ ≤ Δ → trustRegionModel g B s ≤ trustRegionModel g B p)
    (heq : B s + μ • s = -g) (hcompl : μ * (‖s‖ - Δ) = 0) (v : E) :
    0 ≤ ⟪B v + μ • v, v⟫ := by
  rcases hs.lt_or_eq with hi | hb
  · have hμ : μ = 0 := (mul_eq_zero.mp hcompl).resolve_right (sub_ne_zero.mpr hi.ne)
    let t : ℝ := (Δ - ‖s‖) / (‖v‖ + 1)
    have ht : 0 < t := div_pos (sub_pos.mpr hi) (by positivity)
    have htm : t * (‖v‖ + 1) = Δ - ‖s‖ := div_mul_cancel₀ _ (by positivity)
    have hp : ‖s + t • v‖ ≤ Δ := by
      calc ‖s + t • v‖ ≤ ‖s‖ + ‖t • v‖ := norm_add_le _ _
        _ = ‖s‖ + t * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        _ ≤ Δ := by nlinarith
    exact shifted_nonneg hsymm heq hmin v ht.ne' hp (by simp [hμ])
  have hn (w : E) (hw : ⟪s, w⟫ ≠ 0) : 0 ≤ ⟪B w + μ • w, w⟫ := by
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hw (inner_zero_right _)
    let t : ℝ := -(2 * ⟪s, w⟫) / ‖w‖ ^ 2
    have ht : t ≠ 0 := div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hw))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hw0))
    have htm : t * ‖w‖ ^ 2 = -(2 * ⟪s, w⟫) :=
      div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hw0))
    have hnorm : ‖s + t • w‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      calc ‖s‖ ^ 2 + 2 * (t * ⟪s, w⟫) + t ^ 2 * ‖w‖ ^ 2 =
          ‖s‖ ^ 2 + t * (2 * ⟪s, w⟫ + t * ‖w‖ ^ 2) := by ring
        _ = ‖s‖ ^ 2 := by rw [htm, add_neg_cancel, mul_zero, add_zero]
    have hp : ‖s + t • w‖ ≤ Δ := by
      rw [← hb]
      nlinarith [norm_nonneg (s + t • w), norm_nonneg s]
    exact shifted_nonneg hsymm heq hmin w ht hp (by rw [hnorm, sub_self, mul_zero])
  by_cases hv : ⟪s, v⟫ = 0
  · have hc : Continuous fun t : ℝ => v + t • s := by fun_prop
    have hf : Continuous fun t : ℝ => ⟪B (v + t • s) + μ • (v + t • s), v + t • s⟫ :=
      ((B.continuous.comp hc).add (hc.const_smul μ)).inner hc
    have ht : Tendsto (fun t : ℝ => ⟪B (v + t • s) + μ • (v + t • s), v + t • s⟫)
        (𝓝[>] (0 : ℝ)) (𝓝 ⟪B v + μ • v, v⟫) := by
      simpa using hf.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    refine ge_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t htp
    apply hn
    rw [inner_add_right, hv, zero_add, real_inner_smul_right, real_inner_self_eq_norm_sq, hb]
    exact mul_ne_zero htp.ne' (pow_ne_zero _ hΔ.ne')
  · exact hn v hv

/-- **Necessary optimality conditions for the trust-region subproblem.** Let `E` be a
finite-dimensional real inner product space, `B` a symmetric operator and `Δ > 0`. If `s` with
`‖s‖ ≤ Δ` minimises the model `q(p) = ⟪g, p⟫ + ½ ⟪B p, p⟫` over the ball `‖p‖ ≤ Δ`, then there is
`μ ≥ 0` with `B s + μ • s = -g`, `B + μ I` positive semidefinite and `μ (‖s‖ - Δ) = 0`.

This is Theorem 2.1 of N. I. M. Gould, D. P. Robinson and H. S. Thorne, *On solving trust-region
and other regularised subproblems in optimization*, Math. Program. Comput. 2 (2010), with the
identity as the norm matrix `M`; that source credits the result to Gay (1981) and to Moré and
Sorensen (1983). The converse is `trustRegionModel_le_of_optimality`. -/
public theorem exists_optimality_of_isMinOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {g s : E} {B : E →L[ℝ] E} {Δ : ℝ}
    (hΔ : 0 < Δ) (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (hs : ‖s‖ ≤ Δ)
    (hmin : ∀ p : E, ‖p‖ ≤ Δ → trustRegionModel g B s ≤ trustRegionModel g B p) :
    ∃ μ : ℝ, 0 ≤ μ ∧ B s + μ • s = -g ∧ (∀ v, 0 ≤ ⟪B v + μ • v, v⟫) ∧ μ * (‖s‖ - Δ) = 0 := by
  obtain ⟨μ, hμ, heq, hc⟩ := multiplier hΔ hs (support hsymm hs hmin)
  exact ⟨μ, hμ, heq, shifted_psd hΔ hsymm hs hmin heq hc, hc⟩

end

end MathlibExt.Analysis.Optimization.TrustRegion
