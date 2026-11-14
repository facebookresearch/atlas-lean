/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Probability.Statistics.GLM.IRLS

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Local convergence of Newton–Raphson / IRLS for canonical GLMs

For a generalized linear model with canonical link, the observed information equals the Fisher
information, so Newton–Raphson on the score, Fisher scoring, and iteratively reweighted least
squares (IRLS) produce the same iterates. This file proves the local convergence of that
iteration by the classical contraction argument, with the score `U` and its derivative `H`
(the Hessian of the log-likelihood, `H = -I` for the Fisher information `I`) taken as explicit
hypotheses.

The model-specific identities (the canonical score `Xᵀ (y - μ(β))`, the Hessian `-Xᵀ W X`, and
`newtonStep = irlsStep`) are not restated here; they are the subject of `GLM/Basic.lean`,
`GLM/Canonical.lean` and `GLM/IRLS.lean`. In the convergence theorems the iteration map `T` is
arbitrary and enters only through the Newton equations `H z (T z - z) = -U z` near the root (for
IRLS, the weighted normal equations). The last section proves that the IRLS step `irlsStep` of
`GLM/IRLS.lean` satisfies these equations at every `β` where the IRLS weights are nonzero and the
weighted Gram matrix is invertible, with its `Matrix` statements on `k → ℝ` transported to
`(k → ℝ) →L[ℝ] (k → ℝ)` by `Matrix.toLin'` (`irlsStep_fisherScoring_eq`, `irlsStep_newton_eq`).
Without those two assumptions `irlsStep` is a junk value of Mathlib's total matrix inverse and
need not satisfy them (see the tests).

## Source receipt

* J. E. Dennis Jr. and R. B. Schnabel, *Numerical Methods for Unconstrained Optimization and
  Nonlinear Equations*, SIAM Classics in Applied Mathematics 16, 1996 (reprint of Prentice-Hall,
  1983):
  * **Lemma 4.1.12**: if `J = F'` is `γ`-Lipschitz on an open convex set containing `x` and
    `x + p`, then `‖F(x + p) - F(x) - J(x) p‖ ≤ γ/2 ‖p‖²` (`norm_sub_sub_fderiv_le`).
  * **Theorem 3.1.4** (perturbation lemma), in the form used in the proof of Theorem 5.2.1:
    `‖J(x*)⁻¹‖ ≤ β` and `‖J(x*) - J(x)‖ ≤ 1/(2β)` give `‖J(x)⁻¹‖ ≤ 2β`. Here it appears as the
    lower bound `‖v‖ ≤ 2β ‖J(x) v‖` (`norm_le_two_mul_norm_apply`), which needs no completeness.
  * **Theorem 5.2.1** (local quadratic convergence of Newton's method): with `F(x*) = 0`,
    `J(x*)` nonsingular with `‖J(x*)⁻¹‖ ≤ β`, `J` `γ`-Lipschitz on `N(x*, r)` and
    `ε = min(r, 1/(2βγ))`, every start `x₀ ∈ N(x*, ε)` gives a well-defined sequence
    (`exists_newton_map`) converging to `x*` with `‖x_{k+1} - x*‖ ≤ βγ ‖x_k - x*‖²`
    (`newton_local_convergence`).
* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd ed., Chapman & Hall, 1989,
  §2.5 (Fisher scoring as IRLS; for the canonical link it coincides with Newton–Raphson).
  `fisherScoring_local_convergence` is Theorem 5.2.1 rewritten with `J = U' = -I`.

## Fidelity notes

* Dennis–Schnabel work in `ℝⁿ` with an induced operator norm. Here `E` is any real normed space
  and `‖·‖` on `E →L[ℝ] E` is the operator norm; finite dimension is used only in
  `exists_newton_map`.
* Theorem 5.2.1 writes the step as `x_{k+1} = x_k - J(x_k)⁻¹ F(x_k)`. Here it is the linear
  system `J(x) (x⁺ - x) = -F(x)`, which agrees with that formula whenever `J(x)` is invertible
  (as it is on `ball b ε` in finite dimension, see `exists_newton_map`). Only the inverse of
  `J(x*)` is used, as a left inverse with a norm bound.
* Instead of `ε = min(r, 1/(2βγ))` we allow any `ε ≤ r` with `2 β γ ε ≤ 1`. This contains the
  book's choice and avoids `1 / 0 = 0` when `γ = 0` (e.g. the Gaussian linear model).
* The per-step linear rate `‖x_{k+1} - x*‖ ≤ ½ ‖x_k - x*‖` and its cumulative form
  `‖x_k - x*‖ ≤ (1/2)^k ‖x₀ - x*‖` are both conclusions.

## Main results

* `norm_sub_sub_fderiv_le`: quadratic Taylor remainder under a Lipschitz derivative.
* `norm_le_two_mul_norm_apply`: the perturbation bound.
* `newton_step_error_le`: one Newton step squares the error, `‖z' - b‖ ≤ M L ‖z - b‖²`.
* `newton_local_convergence`: iterates stay in `ball b ε`, the error is squared up to the factor
  `M L` and at least halves at each step, and the iterates converge to the root `b`.
* `exists_newton_map`: in finite dimension the Newton system is solvable on `ball b ε`.
* `eq_of_score_eq_zero`: the root is the only score zero in `ball b ε`.
* `fisherScoring_local_convergence`: the same convergence statement for the Fisher-scoring /
  IRLS equations `I x (T x - x) = U x` with `U' = -I`.
* `irlsStep_fisherScoring_eq`, `irlsStep_newton_eq`: with nonzero IRLS weights and an invertible
  weighted Gram matrix at `β`, `irlsStep` solves the Fisher-scoring equations
  `Xᵀ W(β) X (T β - β) = Xᵀ (y - μ(β))` and, under the canonical-link hypotheses
  `IsCanonicalScoreHessian`, the Newton equations `hess β (T β - β) = -score β`, as equations
  between continuous linear maps on `k → ℝ`.
-/

@[expose] public section

open Filter Metric Set Topology

namespace MathlibExt.Probability.Statistics.GLM.IRLSConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lipschitz-derivative Taylor bound** (Dennis–Schnabel, Lemma 4.1.12). If `U` has derivative
`H z` at every point `z` of a convex set `s`, and `‖H z - H x‖ ≤ L ‖z - x‖` on `s`, then
`‖U y - U x - H x (y - x)‖ ≤ L/2 ‖y - x‖²` for `x, y ∈ s`. -/
theorem norm_sub_sub_fderiv_le {U : E → E} {H : E → E →L[ℝ] E} {s : Set E} (hs : Convex ℝ s)
    {L : ℝ} {x y : E} (hU : ∀ z ∈ s, HasFDerivAt U (H z) z)
    (hH : ∀ z ∈ s, ‖H z - H x‖ ≤ L * ‖z - x‖) (hx : x ∈ s) (hy : y ∈ s) :
    ‖U y - U x - H x (y - x)‖ ≤ L / 2 * ‖y - x‖ ^ 2 := by
  set e := y - x with he
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • e ∈ s := fun t ht =>
    hs.add_smul_sub_mem hx hy ht
  set g : ℝ → E := fun t => U (x + t • e) - U x - t • H x e with hg_def
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (H (x + t • e) e - H x e) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => x + t • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add x
    have h2 := (hU _ (hseg t ht)).comp_hasDerivAt t h1
    have h3 := (h2.sub_const (U x)).sub ((hasDerivAt_id t).smul_const (H x e))
    rw [one_smul] at h3
    exact h3
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => L / 2 * ‖e‖ ^ 2 * t ^ 2) (L * ‖e‖ ^ 2 * t) t := by
    intro t
    have := (hasDerivAt_pow 2 t).const_mul (L / 2 * ‖e‖ ^ 2)
    convert this using 1
    push_cast
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := g) (a := 0) (b := 1)
    (f' := fun t => H (x + t • e) e - H x e)
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [g]) hB
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      calc ‖H (x + t • e) e - H x e‖ = ‖(H (x + t • e) - H x) e‖ := by
            rfl
        _ ≤ ‖H (x + t • e) - H x‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖x + t • e - x‖ * ‖e‖ :=
            mul_le_mul_of_nonneg_right (hH _ (hseg t ht')) (norm_nonneg _)
        _ = L * ‖e‖ ^ 2 * t := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
            ring)
    (right_mem_Icc.2 zero_le_one)
  have hxe : x + e = y := by rw [he, add_sub_cancel]
  simpa [g, hxe] using key

/-- **Perturbation bound** (the step of Dennis–Schnabel, Theorem 3.1.4, used in Theorem 5.2.1).
If `A₀inv` is a left inverse of `A₀` with `‖A₀inv‖ ≤ M`, and `‖A₀ - A‖ ≤ δ` with `M δ ≤ 1/2`,
then `A` is bounded below: `‖v‖ ≤ 2 M ‖A v‖`. -/
theorem norm_le_two_mul_norm_apply {A A₀ A₀inv : E →L[ℝ] E} {M δ : ℝ}
    (hleft : ∀ v, A₀inv (A₀ v) = v) (hM : ‖A₀inv‖ ≤ M) (hδ : ‖A₀ - A‖ ≤ δ)
    (hMδ : M * δ ≤ 1 / 2) (v : E) :
    ‖v‖ ≤ 2 * M * ‖A v‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have h1 : ‖v‖ ≤ M * ‖A₀ v‖ := by
    calc ‖v‖ = ‖A₀inv (A₀ v)‖ := by rw [hleft]
      _ ≤ ‖A₀inv‖ * ‖A₀ v‖ := A₀inv.le_opNorm _
      _ ≤ M * ‖A₀ v‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg _)
  have h2 : ‖A₀ v‖ ≤ ‖A v‖ + δ * ‖v‖ := by
    calc ‖A₀ v‖ = ‖A v + (A₀ - A) v‖ := by
          congr 1
          change A₀ v = A v + (A₀ v - A v)
          abel
      _ ≤ ‖A v‖ + ‖(A₀ - A) v‖ := norm_add_le _ _
      _ ≤ ‖A v‖ + δ * ‖v‖ := by
          gcongr
          exact (A₀ - A).le_of_opNorm_le hδ v
  have h3 : ‖v‖ ≤ M * ‖A v‖ + M * δ * ‖v‖ := by
    calc ‖v‖ ≤ M * ‖A₀ v‖ := h1
      _ ≤ M * (‖A v‖ + δ * ‖v‖) := mul_le_mul_of_nonneg_left h2 hM0
      _ = M * ‖A v‖ + M * δ * ‖v‖ := by ring
  nlinarith [norm_nonneg v]

/-- The Newton step `H z (z' - z) = -U z` turns the error `z' - b` into the Taylor remainder
at the root: `H z (z' - b) = U b - U z - H z (b - z)`. -/
private theorem newton_apply_sub_root_eq {U : E → E} {H : E → E →L[ℝ] E} {b z z' : E}
    (hb : U b = 0) (hstep : H z (z' - z) = -U z) :
    H z (z' - b) = U b - U z - H z (b - z) := by
  have : z' - b = (z' - z) - (b - z) := by abel
  rw [this, map_sub, hstep, hb]
  abel

/-- **One Newton step squares the error.** Let `b` be a root of `U`, let `U` have derivative
`H x` on `ball b r` with `H` `L`-Lipschitz there, and let `H₀inv` be a left inverse of `H b` with
`‖H₀inv‖ ≤ M`. If `z ∈ ball b r`, `2 M L ‖z - b‖ ≤ 1` and `z'` solves the Newton system
`H z (z' - z) = -U z`, then `‖z' - b‖ ≤ M L ‖z - b‖²`. -/
theorem newton_step_error_le {U : E → E} {H : E → E →L[ℝ] E} {H₀inv : E →L[ℝ] E} {b z z' : E}
    {r M L : ℝ} (hb : U b = 0) (hU : ∀ x ∈ ball b r, HasFDerivAt U (H x) x)
    (hH : ∀ x ∈ ball b r, ∀ y ∈ ball b r, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hleft : ∀ v, H₀inv (H b v) = v) (hM : ‖H₀inv‖ ≤ M) (hz : z ∈ ball b r)
    (hzε : 2 * M * L * ‖z - b‖ ≤ 1) (hstep : H z (z' - z) = -U z) :
    ‖z' - b‖ ≤ M * L * ‖z - b‖ ^ 2 := by
  have hbb : b ∈ ball b r := mem_ball_self (pos_of_mem_ball hz)
  have hδ : ‖H b - H z‖ ≤ L * ‖z - b‖ := by
    simpa [norm_sub_rev b z] using hH b hbb z hz
  have hlow := norm_le_two_mul_norm_apply hleft hM hδ (by linarith) (z' - b)
  have htaylor := norm_sub_sub_fderiv_le (convex_ball b r) hU
    (fun x hx => hH x hx z hz) hz hbb
  rw [newton_apply_sub_root_eq hb hstep] at hlow
  calc ‖z' - b‖ ≤ 2 * M * ‖U b - U z - H z (b - z)‖ := hlow
    _ ≤ 2 * M * (L / 2 * ‖b - z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left htaylor (by linarith [(norm_nonneg _).trans hM])
    _ = M * L * ‖z - b‖ ^ 2 := by rw [norm_sub_rev]; ring

/-- `2 M L ε ≤ 1` and `‖z - b‖ < ε` give `2 M L ‖z - b‖ ≤ 1`, for any sign of `L`. -/
private theorem two_mul_mul_norm_le_one {M L ε d : ℝ} (hM0 : 0 ≤ M) (hd0 : 0 ≤ d) (hdε : d ≤ ε)
    (hMLε : 2 * M * L * ε ≤ 1) : 2 * M * L * d ≤ 1 := by
  rcases le_total 0 L with hL | hL
  · calc 2 * M * L * d ≤ 2 * M * L * ε := by
          apply mul_le_mul_of_nonneg_left hdε; positivity
      _ ≤ 1 := hMLε
  · have : M * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM0 hL
    nlinarith

/-- The contraction step: with `ε ≤ r` and `2 M L ε ≤ 1`, a Newton step from `z ∈ ball b ε`
squares the error, at least halves it, and stays in `ball b ε`. -/
private theorem newton_step_contract {U : E → E} {H : E → E →L[ℝ] E} {H₀inv : E →L[ℝ] E}
    {T : E → E} {b z : E} {r ε M L : ℝ} (hb : U b = 0)
    (hU : ∀ x ∈ ball b r, HasFDerivAt U (H x) x)
    (hH : ∀ x ∈ ball b r, ∀ y ∈ ball b r, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hleft : ∀ v, H₀inv (H b v) = v) (hM : ‖H₀inv‖ ≤ M)
    (hT : ∀ x ∈ ball b ε, H x (T x - x) = -U x)
    (hεr : ε ≤ r) (hMLε : 2 * M * L * ε ≤ 1) (hz : z ∈ ball b ε) :
    ‖T z - b‖ ≤ M * L * ‖z - b‖ ^ 2 ∧ ‖T z - b‖ ≤ 1 / 2 * ‖z - b‖ ∧ T z ∈ ball b ε := by
  have hzr : z ∈ ball b r := ball_subset_ball hεr hz
  have hzb : ‖z - b‖ < ε := mem_ball_iff_norm.1 hz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hn0 := norm_nonneg (z - b)
  have hzε := two_mul_mul_norm_le_one hM0 hn0 hzb.le hMLε
  have hq : ‖T z - b‖ ≤ M * L * ‖z - b‖ ^ 2 :=
    newton_step_error_le hb hU hH hleft hM hzr hzε (hT z hz)
  have hhalf : ‖T z - b‖ ≤ 1 / 2 * ‖z - b‖ := by
    have : M * L * ‖z - b‖ ^ 2 ≤ 1 / 2 * ‖z - b‖ := by
      have : M * L * ‖z - b‖ ^ 2 = (2 * M * L * ‖z - b‖) * (1 / 2 * ‖z - b‖) := by ring
      rw [this]
      exact mul_le_of_le_one_left (by positivity) hzε
    linarith
  refine ⟨hq, hhalf, mem_ball_iff_norm.2 ?_⟩
  have hε0 : 0 < ε := hn0.trans_lt hzb
  rcases eq_or_lt_of_le hn0 with h0 | h0
  · rw [← h0] at hhalf
    linarith
  · linarith

/-- **Local convergence of Newton–Raphson** (Dennis–Schnabel, Theorem 5.2.1). Let `b` be a root
of `U`, let `U` have derivative `H x` at every `x ∈ ball b r` with `H` `L`-Lipschitz there, and let
`H₀inv` be a left inverse of `H b` with `‖H₀inv‖ ≤ M`. Let `T` take Newton steps on `ball b ε`,
i.e. `H x (T x - x) = -U x`. If `ε ≤ r` and `2 M L ε ≤ 1`, then from every `β₀ ∈ ball b ε` the
iterates `T^[n] β₀`

* stay in `ball b ε`,
* satisfy the quadratic bound `‖T^[n+1] β₀ - b‖ ≤ M L ‖T^[n] β₀ - b‖²`,
* satisfy the per-step bound `‖T^[n+1] β₀ - b‖ ≤ 1/2 ‖T^[n] β₀ - b‖`,
* satisfy the linear bound `‖T^[n] β₀ - b‖ ≤ (1/2)^n ‖β₀ - b‖`, and
* converge to `b`.

Such a `T` exists when `E` is finite-dimensional (`exists_newton_map`). -/
theorem newton_local_convergence {U : E → E} {H : E → E →L[ℝ] E} {H₀inv : E →L[ℝ] E}
    {T : E → E} {b β₀ : E} {r ε M L : ℝ} (hb : U b = 0)
    (hU : ∀ x ∈ ball b r, HasFDerivAt U (H x) x)
    (hH : ∀ x ∈ ball b r, ∀ y ∈ ball b r, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hleft : ∀ v, H₀inv (H b v) = v) (hM : ‖H₀inv‖ ≤ M)
    (hT : ∀ x ∈ ball b ε, H x (T x - x) = -U x)
    (hεr : ε ≤ r) (hMLε : 2 * M * L * ε ≤ 1) (hβ₀ : β₀ ∈ ball b ε) :
    (∀ n, T^[n] β₀ ∈ ball b ε) ∧
      (∀ n, ‖T^[n + 1] β₀ - b‖ ≤ M * L * ‖T^[n] β₀ - b‖ ^ 2) ∧
      (∀ n, ‖T^[n + 1] β₀ - b‖ ≤ 1 / 2 * ‖T^[n] β₀ - b‖) ∧
      (∀ n, ‖T^[n] β₀ - b‖ ≤ (1 / 2) ^ n * ‖β₀ - b‖) ∧
      Tendsto (fun n => T^[n] β₀) atTop (𝓝 b) := by
  have step := fun z (hz : z ∈ ball b ε) =>
    newton_step_contract hb hU hH hleft hM hT hεr hMLε hz
  have hmem : ∀ n, T^[n] β₀ ∈ ball b ε := by
    intro n
    induction n with
    | zero => simpa using hβ₀
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (step _ ih).2.2
  have hquad : ∀ n, ‖T^[n + 1] β₀ - b‖ ≤ M * L * ‖T^[n] β₀ - b‖ ^ 2 := by
    intro n
    rw [Function.iterate_succ_apply']
    exact (step _ (hmem n)).1
  have hlin : ∀ n, ‖T^[n] β₀ - b‖ ≤ (1 / 2) ^ n * ‖β₀ - b‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        calc ‖T (T^[n] β₀) - b‖ ≤ 1 / 2 * ‖T^[n] β₀ - b‖ := (step _ (hmem n)).2.1
          _ ≤ 1 / 2 * ((1 / 2) ^ n * ‖β₀ - b‖) := by gcongr
          _ = (1 / 2) ^ (n + 1) * ‖β₀ - b‖ := by ring
  have hhalf : ∀ n, ‖T^[n + 1] β₀ - b‖ ≤ 1 / 2 * ‖T^[n] β₀ - b‖ := by
    intro n
    rw [Function.iterate_succ_apply']
    exact (step _ (hmem n)).2.1
  refine ⟨hmem, hquad, hhalf, hlin, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * ‖β₀ - b‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_const ‖β₀ - b‖
  exact squeeze_zero (fun n => norm_nonneg _) hlin hlim

/-- **The Newton iteration is well defined** in finite dimension (the "well defined" clause of
Dennis–Schnabel, Theorem 5.2.1). Under the hypotheses of `newton_local_convergence`, `H x` is
invertible for every `x ∈ ball b ε`, so some map `T` takes Newton steps there. -/
theorem exists_newton_map [FiniteDimensional ℝ E] {U : E → E} {H : E → E →L[ℝ] E}
    {H₀inv : E →L[ℝ] E} {b : E} {r ε M L : ℝ}
    (hH : ∀ x ∈ ball b r, ∀ y ∈ ball b r, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hleft : ∀ v, H₀inv (H b v) = v) (hM : ‖H₀inv‖ ≤ M)
    (hεr : ε ≤ r) (hMLε : 2 * M * L * ε ≤ 1) :
    ∃ T : E → E, ∀ x ∈ ball b ε, H x (T x - x) = -U x := by
  have hsurj : ∀ x ∈ ball b ε, Function.Surjective (H x) := by
    intro x hx
    have hxr : x ∈ ball b r := ball_subset_ball hεr hx
    have hbb : b ∈ ball b r := mem_ball_self (pos_of_mem_ball hxr)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
    have hxε := two_mul_mul_norm_le_one hM0 (norm_nonneg _) (mem_ball_iff_norm.1 hx).le hMLε
    have hδ : ‖H b - H x‖ ≤ L * ‖x - b‖ := by
      simpa [norm_sub_rev b x] using hH b hbb x hxr
    have hinj : Function.Injective (H x : E →ₗ[ℝ] E) := by
      intro v w hvw
      have hlow := norm_le_two_mul_norm_apply hleft hM hδ (by linarith) (v - w)
      have h0 : (H x) (v - w) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.2 hvw
      rw [h0, norm_zero, mul_zero] at hlow
      exact sub_eq_zero.1 (norm_le_zero_iff.1 hlow)
    exact LinearMap.injective_iff_surjective.1 hinj
  classical
  refine ⟨fun x => if hx : x ∈ ball b ε then x + (hsurj x hx (-U x)).choose else x, ?_⟩
  intro x hx
  simp only [hx, ↓reduceDIte, add_sub_cancel_left]
  exact (hsurj x hx (-U x)).choose_spec

/-- **Uniqueness of the root near `b`.** Under the hypotheses of `newton_local_convergence`,
`b` is the only zero of `U` in `ball b ε`. -/
theorem eq_of_score_eq_zero {U : E → E} {H : E → E →L[ℝ] E} {H₀inv : E →L[ℝ] E} {b β : E}
    {r ε M L : ℝ} (hb : U b = 0) (hU : ∀ x ∈ ball b r, HasFDerivAt U (H x) x)
    (hH : ∀ x ∈ ball b r, ∀ y ∈ ball b r, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hleft : ∀ v, H₀inv (H b v) = v) (hM : ‖H₀inv‖ ≤ M)
    (hεr : ε ≤ r) (hMLε : 2 * M * L * ε ≤ 1) (hβ : β ∈ ball b ε) (hUβ : U β = 0) :
    β = b := by
  have hβr : β ∈ ball b r := ball_subset_ball hεr hβ
  have hbb : b ∈ ball b r := mem_ball_self (pos_of_mem_ball hβr)
  have hβb : ‖β - b‖ < ε := mem_ball_iff_norm.1 hβ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have htaylor := norm_sub_sub_fderiv_le (convex_ball b r) hU
    (fun x hx => hH x hx b hbb) hbb hβr
  rw [hUβ, hb, sub_zero, zero_sub, norm_neg] at htaylor
  have hlow : ‖β - b‖ ≤ M * ‖H b (β - b)‖ := by
    calc ‖β - b‖ = ‖H₀inv (H b (β - b))‖ := by rw [hleft]
      _ ≤ ‖H₀inv‖ * ‖H b (β - b)‖ := H₀inv.le_opNorm _
      _ ≤ M * ‖H b (β - b)‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg _)
  set e := ‖β - b‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have hkey : e ≤ M * L / 2 * e ^ 2 := by
    calc e ≤ M * ‖H b (β - b)‖ := hlow
      _ ≤ M * (L / 2 * e ^ 2) := mul_le_mul_of_nonneg_left htaylor hM0
      _ = M * L / 2 * e ^ 2 := by ring
  have hsmall : 2 * M * L * e ≤ 1 := two_mul_mul_norm_le_one hM0 he0 hβb.le hMLε
  have : e = 0 := by nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **Local convergence of Fisher scoring / IRLS for a canonical GLM.** For a canonical link the
derivative of the score `U` is minus the Fisher information, `U' = -I`, so the Fisher-scoring
equations `I x (T x - x) = U x` (for IRLS: the weighted normal equations
`Xᵀ W X (β' - β) = Xᵀ (y - μ)`) are the Newton equations. Let `b` be a root of `U`, let `I` be
`L`-Lipschitz on `ball b r`, and let `I₀inv` be a left inverse of `I b` with `‖I₀inv‖ ≤ M`. If
`ε ≤ r`, `2 M L ε ≤ 1` and `T` solves the Fisher-scoring equations on `ball b ε`, then from every
`β₀ ∈ ball b ε` the iterates stay in `ball b ε`, satisfy
`‖T^[n+1] β₀ - b‖ ≤ M L ‖T^[n] β₀ - b‖²`, `‖T^[n+1] β₀ - b‖ ≤ 1/2 ‖T^[n] β₀ - b‖` and
`‖T^[n] β₀ - b‖ ≤ (1/2)^n ‖β₀ - b‖`, and converge to `b`. -/
theorem fisherScoring_local_convergence {U : E → E} {I : E → E →L[ℝ] E} {I₀inv : E →L[ℝ] E}
    {T : E → E} {b β₀ : E} {r ε M L : ℝ} (hb : U b = 0)
    (hU : ∀ x ∈ ball b r, HasFDerivAt U (-I x) x)
    (hI : ∀ x ∈ ball b r, ∀ y ∈ ball b r, ‖I x - I y‖ ≤ L * ‖x - y‖)
    (hleft : ∀ v, I₀inv (I b v) = v) (hM : ‖I₀inv‖ ≤ M)
    (hT : ∀ x ∈ ball b ε, I x (T x - x) = U x)
    (hεr : ε ≤ r) (hMLε : 2 * M * L * ε ≤ 1) (hβ₀ : β₀ ∈ ball b ε) :
    (∀ n, T^[n] β₀ ∈ ball b ε) ∧
      (∀ n, ‖T^[n + 1] β₀ - b‖ ≤ M * L * ‖T^[n] β₀ - b‖ ^ 2) ∧
      (∀ n, ‖T^[n + 1] β₀ - b‖ ≤ 1 / 2 * ‖T^[n] β₀ - b‖) ∧
      (∀ n, ‖T^[n] β₀ - b‖ ≤ (1 / 2) ^ n * ‖β₀ - b‖) ∧
      Tendsto (fun n => T^[n] β₀) atTop (𝓝 b) := by
  refine newton_local_convergence (H := fun x => -I x) (H₀inv := -I₀inv) hb hU
    (fun x hx y hy => ?_) (fun v => ?_) (by simpa using hM) (fun x hx => ?_) hεr hMLε hβ₀
  · rw [← neg_sub', norm_neg]
    exact hI x hx y hy
  · simp [hleft]
  · simp [hT x hx]

/-! ### The IRLS step satisfies the Newton equations -/

section IRLSNewton

open Matrix
open MathlibExt.Probability.Statistics.GLM.IRLS

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
  {X : Matrix m k ℝ} {y : m → ℝ} {mean weight : ℝ → ℝ}

/-- **The IRLS step solves the Fisher-scoring equations.** With nonzero IRLS weights and an
invertible weighted Gram matrix at `β`, the IRLS step `T = irlsStep X y mean weight` solves
`I β (T β - β) = U β`, where the Fisher information `I β = Xᵀ W(β) X` acts on `k → ℝ` as a
continuous linear map and `U β = Xᵀ (y - μ(β))` is the canonical score. At every point of a ball
where the two assumptions hold, this is the hypothesis `hT` of `fisherScoring_local_convergence`
for `T = irlsStep X y mean weight`. -/
theorem irlsStep_fisherScoring_eq (β : k → ℝ) (hw : ∀ i, irlsWeights weight X β i ≠ 0)
    (hG : IsUnit (weightedGram X (irlsWeights weight X β))) :
    LinearMap.toContinuousLinearMap (Matrix.toLin' (weightedGram X (irlsWeights weight X β)))
        (irlsStep X y mean weight β - β) =
      Xᵀ *ᵥ (y - fun i => mean ((X *ᵥ β) i)) := by
  have hdet := (isUnit_iff_isUnit_det _).mp hG
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
  rw [irlsStep_eq β hw hG, add_sub_cancel_left, mulVec_mulVec, mul_nonsing_inv _ hdet,
    one_mulVec]

/-- **The IRLS step solves the Newton equations.** Under the canonical-link score and Hessian
identities, with nonzero IRLS weights and an invertible weighted Gram matrix at `β`, the IRLS
step `T = irlsStep X y mean weight` solves `H β (T β - β) = -score β`, where `H β` is `hess β`
acting on `k → ℝ` as a continuous linear map. When `mean' = weight`, `H β` is the derivative of
`score` at `β` (`IsCanonicalScoreHessian.hasFDerivAt`), so at every point of a ball where the two
assumptions hold this is the hypothesis `hT` of `newton_local_convergence` for
`U = score` and `T = irlsStep X y mean weight`. -/
theorem irlsStep_newton_eq {score : (k → ℝ) → k → ℝ} {hess : (k → ℝ) → Matrix k k ℝ}
    (h : IsCanonicalScoreHessian X y mean weight score hess) (β : k → ℝ)
    (hw : ∀ i, irlsWeights weight X β i ≠ 0)
    (hG : IsUnit (weightedGram X (irlsWeights weight X β))) :
    LinearMap.toContinuousLinearMap (Matrix.toLin' (hess β)) (irlsStep X y mean weight β - β) =
      -score β := by
  have h₁ := irlsStep_fisherScoring_eq (y := y) (mean := mean) β hw hG
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply] at h₁ ⊢
  rw [h.hess_eq, neg_mulVec, h₁, h.score_eq]

end IRLSNewton

end MathlibExt.Probability.Statistics.GLM.IRLSConvergence
