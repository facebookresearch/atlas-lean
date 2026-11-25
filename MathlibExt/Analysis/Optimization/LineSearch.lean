/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Line searches and the Zoutendijk condition

A line-search method for minimising a function `f` on a real Hilbert space iterates
`x (k + 1) = x k + α k • d k` along search directions `d k` with step lengths `α k > 0`.
This file defines the Armijo (sufficient decrease) condition and the standard and strong Wolfe
conditions on a step length, and proves the Zoutendijk condition
`∑ k, ⟪∇f(x k), d k⟫² / ‖d k‖² < ∞` for any method using descent directions and standard Wolfe
steps (Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global
convergence property*, SIAM J. Optim. 10 (1999), 177-182, Lemma 3.2).

The step lower bound and the per-step decrease are those of the source's proof, equations
(3.3)-(3.6).
-/

@[expose] public section

namespace MathlibExt.Analysis.Optimization.LineSearch

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Armijo sufficient decrease condition.** The step length `α` along `d` from `x` satisfies
`f (x + α • d) ≤ f x + δ α ⟪∇f(x), d⟫` (Dai and Yuan, SIAM J. Optim. 10 (1999), condition (1.7)). -/
def ArmijoCondition (f : E → ℝ) (δ : ℝ) (x d : E) (α : ℝ) : Prop :=
  f (x + α • d) ≤ f x + δ * α * ⟪gradient f x, d⟫

/-- **Wolfe curvature condition.** The step length `α` along `d` from `x` satisfies
`⟪∇f(x + α • d), d⟫ ≥ σ ⟪∇f(x), d⟫`: the directional derivative has increased by the factor
`σ` (Dai and Yuan, SIAM J. Optim. 10 (1999), condition (1.10), stated there with a strict
inequality; the non-strict form used here is weaker). -/
def CurvatureCondition (f : E → ℝ) (σ : ℝ) (x d : E) (α : ℝ) : Prop :=
  σ * ⟪gradient f x, d⟫ ≤ ⟪gradient f (x + α • d), d⟫

/-- **Standard Wolfe conditions.** The step length `α` satisfies both the Armijo condition with
constant `δ` and the curvature condition with constant `σ` (Dai and Yuan, SIAM J. Optim. 10
(1999), conditions (1.7) and (1.10), where `0 < δ < σ < 1`). -/
def WolfeConditions (f : E → ℝ) (δ σ : ℝ) (x d : E) (α : ℝ) : Prop :=
  ArmijoCondition f δ x d α ∧ CurvatureCondition f σ x d α

/-- **Strong Wolfe conditions.** The step length `α` satisfies the Armijo condition with constant
`δ` and `|⟪∇f(x + α • d), d⟫| ≤ -σ ⟪∇f(x), d⟫` (Dai and Yuan, SIAM J. Optim. 10 (1999),
conditions (1.7) and (1.8), where `0 < δ < σ < 1`). -/
def StrongWolfeConditions (f : E → ℝ) (δ σ : ℝ) (x d : E) (α : ℝ) : Prop :=
  ArmijoCondition f δ x d α ∧ |⟪gradient f (x + α • d), d⟫| ≤ -σ * ⟪gradient f x, d⟫

/-- **Strong Wolfe steps are standard Wolfe steps.** A step length satisfying the strong Wolfe
conditions with constants `δ, σ` satisfies the standard Wolfe conditions with the same constants
(compare conditions (1.8) and (1.10) of Dai and Yuan, SIAM J. Optim. 10 (1999)). -/
theorem StrongWolfeConditions.toWolfeConditions {f : E → ℝ} {δ σ : ℝ} {x d : E} {α : ℝ}
    (h : StrongWolfeConditions f δ σ x d α) : WolfeConditions f δ σ x d α := by
  refine ⟨h.1, ?_⟩
  have := neg_abs_le ⟪gradient f (x + α • d), d⟫
  unfold CurvatureCondition
  linarith [h.2]

/-- One step of a line search: the step lower bound of the curvature condition turned into
objective decrease by the Armijo condition (Dai and Yuan 1999, equations (3.3)-(3.6)). -/
private theorem decrease_of_wolfe {f : E → ℝ} {δ σ L : ℝ} (hδ : 0 < δ) (hσ : σ < 1) (hL : 0 < L)
    {x d : E} {α : ℝ} (hα : 0 < α) (hdesc : ⟪gradient f x, d⟫ < 0)
    (hwolfe : WolfeConditions f δ σ x d α)
    (hlip : ‖gradient f (x + α • d) - gradient f x‖ ≤ L * ‖(x + α • d) - x‖) :
    δ * (1 - σ) / L * (⟪gradient f x, d⟫ ^ 2 / ‖d‖ ^ 2) ≤ f x - f (x + α • d) := by
  obtain ⟨harm, hcurv⟩ := hwolfe
  unfold ArmijoCondition at harm
  unfold CurvatureCondition at hcurv
  set s := ⟪gradient f x, d⟫ with hs
  have hd : d ≠ 0 := by
    rintro rfl
    simp [hs] at hdesc
  have hD : 0 < ‖d‖ ^ 2 := by positivity
  -- (3.3)-(3.4): `(σ - 1) s ≤ ⟪g⁺ - g, d⟫ ≤ α L ‖d‖²`.
  have hupper : ⟪gradient f (x + α • d) - gradient f x, d⟫ ≤ L * α * ‖d‖ ^ 2 := by
    calc ⟪gradient f (x + α • d) - gradient f x, d⟫
        ≤ ‖gradient f (x + α • d) - gradient f x‖ * ‖d‖ := real_inner_le_norm _ _
      _ ≤ L * ‖(x + α • d) - x‖ * ‖d‖ := by gcongr
      _ = L * α * ‖d‖ ^ 2 := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hα]; ring
  have hlower : (1 - σ) * (-s) ≤ L * α * ‖d‖ ^ 2 := by
    rw [inner_sub_left] at hupper
    linarith
  -- (3.5)-(3.6).
  have hstep : (1 - σ) * (-s) / (L * ‖d‖ ^ 2) ≤ α := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have key : δ * (1 - σ) / L * (s ^ 2 / ‖d‖ ^ 2) = δ * (-s) * ((1 - σ) * (-s) / (L * ‖d‖ ^ 2)) := by
    field_simp
  rw [key]
  have hnegs : 0 ≤ δ * (-s) := by nlinarith
  calc δ * (-s) * ((1 - σ) * (-s) / (L * ‖d‖ ^ 2)) ≤ δ * (-s) * α :=
        mul_le_mul_of_nonneg_left hstep hnegs
    _ ≤ f x - f (x + α • d) := by linarith

/-- **Zoutendijk condition.** Let `f` be bounded below along the iterates of a line-search method
`x (k + 1) = x k + α k • d k` with `α k > 0`, descent directions `⟪∇f(x k), d k⟫ < 0`, and step
lengths satisfying the standard Wolfe conditions with constants `δ > 0` and `σ < 1`. If
`‖∇f(x (k + 1)) - ∇f(x k)‖ ≤ L ‖x (k + 1) - x k‖` for some `L > 0`, then
`∑ k, ⟪∇f(x k), d k⟫² / ‖d k‖² < ∞`.

This is Lemma 3.2 of Y. H. Dai and Y. Yuan, SIAM J. Optim. 10 (1999), 177-182, essentially due to
Zoutendijk and Wolfe. The source assumes that `f` is bounded below on `ℝⁿ` and that `∇f` is
`L`-Lipschitz on a neighbourhood of the level set `{x | f x ≤ f x₀}` (its Assumption 3.1); the
Armijo condition keeps the iterates in that level set, so those hypotheses imply the two used here
(bounded below along the iterates, Lipschitz between consecutive iterates), which are exactly the
ones its proof uses. Since `⟪∇f(x k), d k⟫² / ‖d k‖² = cos² θₖ ‖∇f(x k)‖²`, where `θₖ` is the
angle between `d k` and `-∇f(x k)`, this is the classical form `∑ cos² θₖ ‖gₖ‖² < ∞`. -/
theorem zoutendijk {f : E → ℝ} {δ σ L : ℝ} (hδ : 0 < δ) (hσ : σ < 1) (hL : 0 < L)
    {x d : ℕ → E} {α : ℕ → ℝ}
    (hx : ∀ k, x (k + 1) = x k + α k • d k) (hα : ∀ k, 0 < α k)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫ < 0)
    (hwolfe : ∀ k, WolfeConditions f δ σ (x k) (d k) (α k))
    (hlip : ∀ k, ‖gradient f (x (k + 1)) - gradient f (x k)‖ ≤ L * ‖x (k + 1) - x k‖)
    (hbdd : BddBelow (Set.range fun k => f (x k))) :
    Summable fun k => ⟪gradient f (x k), d k⟫ ^ 2 / ‖d k‖ ^ 2 := by
  obtain ⟨m, hm⟩ := hbdd
  have hm' : ∀ k, m ≤ f (x k) := fun k => hm ⟨k, rfl⟩
  set c := δ * (1 - σ) / L with hc
  have hcpos : 0 < c := by
    have : 0 < 1 - σ := by linarith
    positivity
  have hstep : ∀ k, c * (⟪gradient f (x k), d k⟫ ^ 2 / ‖d k‖ ^ 2) ≤ f (x k) - f (x (k + 1)) := by
    intro k
    have h := decrease_of_wolfe (f := f) hδ hσ hL (hα k) (hdesc k) (hwolfe k)
      (by rw [← hx k]; exact hlip k)
    rwa [← hx k] at h
  refine summable_of_sum_range_le (c := (f (x 0) - m) / c) (fun k => by positivity) ?_
  intro n
  rw [le_div_iff₀ hcpos, Finset.sum_mul]
  calc ∑ i ∈ Finset.range n, ⟪gradient f (x i), d i⟫ ^ 2 / ‖d i‖ ^ 2 * c
      ≤ ∑ i ∈ Finset.range n, (f (x i) - f (x (i + 1))) :=
        Finset.sum_le_sum fun i _ => by linarith [hstep i]
    _ = f (x 0) - f (x n) := Finset.sum_range_sub' (fun i => f (x i)) n
    _ ≤ f (x 0) - m := by linarith [hm' n]

end MathlibExt.Analysis.Optimization.LineSearch
