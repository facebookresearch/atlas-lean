/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.SEIRGlobalStability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Tests for the Lyapunov global stability of the SEIR endemic equilibrium

Concrete model `β = 8`, `σ = 1`, `γ = 1`, `μ = 1`, `N = 1`:

* `R₀ = 8 · 1 / ((1 + 1)(1 + 1)) = 2 > 1`, computed from the definition of `R0`;
* the endemic equilibrium `(S*, E*, I*) = (1/2, 1/4, 1/8)` from the definitions, and the
  vector field vanishing there, computed directly from the right-hand sides of the ODE;
* the Lyapunov derivative at the state `(1/4, 1/4, 1/8)`: `lyapunovDeriv = -1/2`, computed
  from its definition, agrees with the chain-rule value `Σ (1 - x*/x) x'` computed from the
  vector field; so any trajectory through that state has `V̇ = -1/2 < 0` there (this state
  has `E = E*`, `I = I*`, so only the `S` term is nonzero);
* the same check at `(1, 1, 1)`, where all three chain-rule terms are nonzero: `V̇ = -5/4`;
* a point `(S*, 2E*, 2I*)` where `V̇ = 0` although it is not an equilibrium (`S' = -1/2`):
  `V̇ ≤ 0` alone does not give convergence, which is why the invariance step is needed;
* non-vacuity: the constant endemic solution satisfies every hypothesis of the main theorems;
* boundaries: at `R₀ = 1` (`β = 4`) the equilibrium degenerates to `S* = N`, `E* = 0`, and at
  `μ = 0` (closed model) `E* = 0`, so the endemic equilibrium leaves the open orthant.

Disease-free equilibrium `(N, 0, 0)` and the removed class:

* `R₀ ≤ 1` (`β = 2`, `R₀ = 1/2`): `V̇₀` at a concrete state from the definition of
  `dfeLyapunovDeriv` agrees with the chain-rule value; at `R₀ = 1` (`β = 4`) a state with
  `S = N`, `I > 0` has `V̇₀ = 0`, so the invariance step is needed there too;
* an explicit trajectory with `R₀ = 0 ≤ 1` (`β = 0`): `S = 1 + e^{-t}`, `E = e^{-2t}`,
  `I = (t + 1) e^{-2t}`, `R = 2 e^{-t} - (t + 2) e^{-2t}`, checked to be a solution from the
  ODE, starts in the open orthant, and converges to `(1, 0, 0)` with `R → 0`; `S → 1` and
  `E → 0` are also checked directly;
* `R₀ > 1` (`β = 8`, `R₀ = 2`): the hypothesis `R₀ ≤ 1` fails, `V̇₀ = 4 > 0` at `(1, 1, 1)`, and
  the constant endemic solution starts in the open orthant but does not converge to `(1, 0, 0)`;
* `R → R*`: for `β = 12, σ = 1, γ = 2, μ = 1, N = 1` (`R₀ = 2`), `R* = γ I* / μ = 1/6` from the
  definitions, `S* + E* + I* + R* = N`, and the constant endemic solution has `R → R*`.

Existence (`exists_isSolution`, `exists_isSolution_of_nonneg`):

* concrete parameters `β = 1`, `σ = 1`, `γ = 1`, `μ = 0.1`, `N = 1` with initial data
  `(0.9, 0.05, 0.05, 0)`: a solution exists, its initial values are the given ones, and its initial
  derivatives `(-0.035, -0.01, -0.005, 0.05)` are computed from the right-hand sides in the
  definition of `IsSolution`; its total stays `≤ 1 = N`;
* the existence theorem discharges the `IsSolution` hypothesis of the stability theorem: for the
  `R₀ = 2` model a non-constant solution from `(0.9, 0.05, 0.05, 0)` converges to `(S*, E*, I*)`;
* `μ = 0`: `exists_isSolution` does not apply (it assumes `μ > 0`); existence there is proved
  separately by `exists_isSolution_of_nonneg` (which assumes only `μ ≥ 0`), and the solution is
  one of the closed SEIR model via `isSolution_zero_iff`;
* negative initial data (`S₀ = -1`): the hypothesis `0 ≤ S₀` fails and no solution with these
  initial values lies in the feasible region, checked at `t = 0` from the initial value alone.
-/

open Real Filter Set
open scoped Topology

namespace MathlibExtTest.Biology.Epidemiology.SEIRGlobalStability

open MathlibExt.Biology.Epidemiology.SEIRVital

/-! ### The threshold `R₀ > 1`, from the definitions -/

example : R0 8 1 1 1 = 2 := by norm_num [R0]

/-- The threshold hypothesis of the main theorems, verified numerically. -/
theorem hR : 1 < R0 8 1 1 1 := by norm_num [R0]

example : endemicS 8 1 1 1 1 = 1 / 2 := by norm_num [endemicS]
example : endemicE 8 1 1 1 1 = 1 / 4 := by norm_num [endemicE, endemicS]
example : endemicI 8 1 1 1 1 = 1 / 8 := by norm_num [endemicI, endemicE, endemicS]

/-- The vector field `(S', E', I')` vanishes at `(1/2, 1/4, 1/8)`, computed from the ODE. -/
example : (1 : ℝ) * 1 - 8 * (1 / 2) * (1 / 8) / 1 - 1 * (1 / 2) = 0 ∧
    (8 : ℝ) * (1 / 2) * (1 / 8) / 1 - (1 + 1) * (1 / 4) = 0 ∧
    (1 : ℝ) * (1 / 4) - (1 + 1) * (1 / 8) = 0 := by norm_num

/-! ### The Lyapunov function and its decrease at a concrete state -/

example : lyapunov 8 1 1 1 1 (1 / 2) (1 / 4) (1 / 8) = 0 := by
  norm_num [lyapunov, volterra, endemicI, endemicE, endemicS]

/-- `V̇` at `(S, E, I) = (1/4, 1/4, 1/8)` from the definition of `lyapunovDeriv`:
`-(1/16)/(1/4) - (1/2)(2 + 1/2 + 1 - 3) = -1/2`. -/
theorem lyapunovDeriv_val : lyapunovDeriv 8 1 1 1 1 (1 / 4) (1 / 4) (1 / 8) = -1 / 2 := by
  norm_num [lyapunovDeriv, endemicI, endemicE, endemicS]

/-- The chain-rule value `(1 - S*/S) S' + (1 - E*/E) E' + ((μ + σ)/σ)(1 - I*/I) I'` at the same
state, with `S' = 1/2`, `E' = -1/4`, `I' = 0` computed from the vector field, is also `-1/2`. -/
example :
    (1 - (1 / 2) / (1 / 4)) * ((1 : ℝ) * 1 - 8 * (1 / 4) * (1 / 8) / 1 - 1 * (1 / 4)) +
      (1 - (1 / 4) / (1 / 4)) * ((8 : ℝ) * (1 / 4) * (1 / 8) / 1 - (1 + 1) * (1 / 4)) +
      (1 + 1) / 1 * ((1 - (1 / 8) / (1 / 8)) * ((1 : ℝ) * (1 / 4) - (1 + 1) * (1 / 8))) =
    -1 / 2 := by
  norm_num

example : lyapunovDeriv 8 1 1 1 1 (1 / 4) (1 / 4) (1 / 8) < 0 := by
  rw [lyapunovDeriv_val]; norm_num

/-- **The Lyapunov decrease on a trajectory**: any solution of the concrete model passing
through `(1/4, 1/4, 1/8)` at a time `t ≥ 0` has `d/dt V = -1/2 < 0` there. -/
example {S E I R : ℝ → ℝ} (h : IsSolution 8 1 1 1 1 S E I R) {t : ℝ} (ht : 0 ≤ t)
    (hS : S t = 1 / 4) (hE : E t = 1 / 4) (hI : I t = 1 / 8) :
    HasDerivAt (fun s => lyapunov 8 1 1 1 1 (S s) (E s) (I s)) (-1 / 2) t := by
  have := h.hasDerivAt_lyapunov one_pos zero_le_one one_pos one_pos hR ht
    (by rw [hS]; norm_num) (by rw [hE]; norm_num) (by rw [hI]; norm_num)
  rwa [hS, hE, hI, lyapunovDeriv_val] at this

/-- The general bound `V̇ ≤ 0` agrees at that state. -/
example : lyapunovDeriv 8 1 1 1 1 (1 / 4) (1 / 4) (1 / 8) ≤ 0 :=
  lyapunovDeriv_nonpos one_pos zero_le_one one_pos one_pos hR (by norm_num) (by norm_num)
    (by norm_num)

/-- At `(S, E, I) = (1, 1, 1)`, where all three chain-rule terms are nonzero, `V̇` from the
definition of `lyapunovDeriv` is `-(1/4) - (1/2)(1/2 + 4 + 1/2 - 3) = -5/4`. -/
theorem lyapunovDeriv_val_one : lyapunovDeriv 8 1 1 1 1 1 1 1 = -5 / 4 := by
  norm_num [lyapunovDeriv, endemicI, endemicE, endemicS]

/-- The chain-rule value at `(1, 1, 1)`, with `S' = -8`, `E' = 6`, `I' = -1` computed from the
vector field: `(1/2)(-8) + (3/4)(6) + 2 (7/8)(-1) = -4 + 9/2 - 7/4 = -5/4`. -/
example :
    (1 - (1 / 2) / 1) * ((1 : ℝ) * 1 - 8 * 1 * 1 / 1 - 1 * 1) +
      (1 - (1 / 4) / 1) * ((8 : ℝ) * 1 * 1 / 1 - (1 + 1) * 1) +
      (1 + 1) / 1 * ((1 - (1 / 8) / 1) * ((1 : ℝ) * 1 - (1 + 1) * 1)) =
    -5 / 4 := by
  norm_num

/-- Any solution through `(1, 1, 1)` at a time `t ≥ 0` has `d/dt V = -5/4` there. -/
example {S E I R : ℝ → ℝ} (h : IsSolution 8 1 1 1 1 S E I R) {t : ℝ} (ht : 0 ≤ t)
    (hS : S t = 1) (hE : E t = 1) (hI : I t = 1) :
    HasDerivAt (fun s => lyapunov 8 1 1 1 1 (S s) (E s) (I s)) (-5 / 4) t := by
  have := h.hasDerivAt_lyapunov one_pos zero_le_one one_pos one_pos hR ht
    (by rw [hS]; norm_num) (by rw [hE]; norm_num) (by rw [hI]; norm_num)
  rwa [hS, hE, hI, lyapunovDeriv_val_one] at this

/-! ### `V̇ = 0` off the equilibrium: the invariance step is needed -/

/-- At `(S*, 2E*, 2I*) = (1/2, 1/2, 1/4)`, `V̇ = 0` from the definition. -/
example : lyapunovDeriv 8 1 1 1 1 (1 / 2) (1 / 2) (1 / 4) = 0 := by
  norm_num [lyapunovDeriv, endemicI, endemicE, endemicS]

/-- ... and `lyapunovDeriv_eq_zero_iff` describes it (`S = S*`, `E I* = E* I`). -/
example : lyapunovDeriv 8 1 1 1 1 (1 / 2) (1 / 2) (1 / 4) = 0 :=
  (lyapunovDeriv_eq_zero_iff one_pos zero_le_one one_pos one_pos hR (by norm_num) (by norm_num)
    (by norm_num)).2 ⟨by norm_num [endemicS], by norm_num [endemicI, endemicE, endemicS]⟩

/-- ... but it is not an equilibrium: `S' = 1 - 8 (1/2)(1/4) - 1/2 = -1/2 ≠ 0`. -/
example : (1 : ℝ) * 1 - 8 * (1 / 2) * (1 / 4) / 1 - 1 * (1 / 2) = -1 / 2 := by norm_num

/-! ### Non-vacuity: the constant endemic solution -/

/-- The constant solution at `(S*, E*, I*, R*) = (1/2, 1/4, 1/8, 1/8)` (`R* = γ I* / μ`). -/
theorem isSolution_const :
    IsSolution 8 1 1 1 1 (fun _ => 1 / 2) (fun _ => 1 / 4) (fun _ => 1 / 8) (fun _ => 1 / 8) :=
  ⟨fun t _ => (hasDerivAt_const t _).congr_deriv (by norm_num),
    fun t _ => (hasDerivAt_const t _).congr_deriv (by norm_num),
    fun t _ => (hasDerivAt_const t _).congr_deriv (by norm_num),
    fun t _ => (hasDerivAt_const t _).congr_deriv (by norm_num)⟩

/-- Every hypothesis of `IsSolution.tendsto_endemic` is satisfiable. -/
example : Tendsto (fun _ : ℝ => ((1 / 2 : ℝ), (1 / 4 : ℝ), (1 / 8 : ℝ))) atTop
    (𝓝 (endemicS 8 1 1 1 1, endemicE 8 1 1 1 1, endemicI 8 1 1 1 1)) :=
  isSolution_const.tendsto_endemic one_pos zero_le_one one_pos one_pos hR (by norm_num)
    (by norm_num) (by norm_num)

/-- Lyapunov stability (`ε = 1`) applied to the constant solution. -/
example (t : ℝ) (ht : 0 ≤ t) : ∃ δ > 0,
    dist ((1 / 2 : ℝ), (1 / 4 : ℝ), (1 / 8 : ℝ))
        (endemicS 8 1 1 1 1, endemicE 8 1 1 1 1, endemicI 8 1 1 1 1) < δ →
      dist ((1 / 2 : ℝ), (1 / 4 : ℝ), (1 / 8 : ℝ))
        (endemicS 8 1 1 1 1, endemicE 8 1 1 1 1, endemicI 8 1 1 1 1) < 1 := by
  obtain ⟨δ, hδ, hst⟩ := endemic_lyapunovStable one_pos zero_le_one one_pos one_pos hR 1 one_pos
  exact ⟨δ, hδ, fun hd => hst _ _ _ _ isSolution_const (by norm_num) (by norm_num) (by norm_num)
    hd t ht⟩

/-- The global asymptotic stability theorem, attractivity half, on the constant solution. -/
example : Tendsto (fun _ : ℝ => ((1 / 2 : ℝ), (1 / 4 : ℝ), (1 / 8 : ℝ))) atTop
    (𝓝 (endemicS 8 1 1 1 1, endemicE 8 1 1 1 1, endemicI 8 1 1 1 1)) :=
  (endemic_globallyAsymptoticallyStable one_pos zero_le_one one_pos one_pos hR).2 _ _ _ _
    isSolution_const (by norm_num) (by norm_num) (by norm_num)

/-- `V(0) = 0` along the constant solution, so `lyapunov_le_initial` is tight there. -/
example : lyapunov 8 1 1 1 1 (1 / 2) (1 / 4) (1 / 8) ≤ 0 := by
  norm_num [lyapunov, volterra, endemicI, endemicE, endemicS]

/-! ### The `μ = 0` link and the boundaries -/

/-- At `μ = 0`, `R₀` is the closed-model `β / γ`. -/
example : R0 8 1 2 0 = 4 := by norm_num [R0]
example : R0 8 1 2 0 = 8 / 2 := R0_zero one_ne_zero

/-- At `μ = 0` (closed model) the endemic exposed level is `0`: no endemic equilibrium. -/
example : endemicE 8 1 1 0 1 = 0 := by norm_num [endemicE]

/-- At the threshold `R₀ = 1` (`β = 4`): `S* = N = 1`, `E* = I* = 0`, outside the open orthant. -/
example : R0 4 1 1 1 = 1 := by norm_num [R0]
example : endemicS 4 1 1 1 1 = 1 := by norm_num [endemicS]
example : endemicE 4 1 1 1 1 = 0 := by norm_num [endemicE, endemicS]
example : endemicI 4 1 1 1 1 = 0 := by norm_num [endemicI, endemicE, endemicS]

/-- Below the threshold (`β = 2`, `R₀ = 1/2`): `S* = 2 > N` and `E* < 0`. -/
example : R0 2 1 1 1 = 1 / 2 := by norm_num [R0]
example : endemicE 2 1 1 1 1 < 0 := by norm_num [endemicE, endemicS]

/-! ### The disease-free equilibrium, `R₀ ≤ 1` -/

/-- `R₀ = 2 · 1 / ((1 + 1)(1 + 1)) = 1/2 ≤ 1`, from the definition. -/
theorem hR_half : R0 2 1 1 1 ≤ 1 := by norm_num [R0]

example : R0 2 1 1 1 = 1 / 2 := by norm_num [R0]

/-- `V₀` vanishes at `(N, 0, 0)`, from the definition. -/
example : dfeLyapunov 1 1 1 1 0 0 = 0 := by norm_num [dfeLyapunov, volterra]

/-- `V̇₀` at `(S, E, I) = (2, 1, 1)` for `β = 2`, from the definition of `dfeLyapunovDeriv`:
`-(1 · 1²)/2 + (2 - 4) · 1 = -5/2`. -/
theorem dfeLyapunovDeriv_val : dfeLyapunovDeriv 2 1 1 1 1 2 1 = -5 / 2 := by
  norm_num [dfeLyapunovDeriv]

/-- The chain-rule value `(1 - N/S) S' + E' + ((μ + σ)/σ) I'` at `(2, 1, 1)`, with
`S' = 1 - 2·2·1 - 2 = -5`, `E' = 4 - 2 = 2`, `I' = 1 - 2 = -1` computed from the vector field:
`(1/2)(-5) + 2 + 2(-1) = -5/2`. -/
example :
    (1 - 1 / 2) * ((1 : ℝ) * 1 - 2 * 2 * 1 / 1 - 1 * 2) + ((2 : ℝ) * 2 * 1 / 1 - (1 + 1) * 1) +
      (1 + 1) / 1 * ((1 : ℝ) * 1 - (1 + 1) * 1) = -5 / 2 := by
  norm_num

/-- Any solution of the `β = 2` model through `(2, 1, 1)` has `d/dt V₀ = -5/2` there. -/
example {S E I R : ℝ → ℝ} (h : IsSolution 2 1 1 1 1 S E I R) {t : ℝ} (ht : 0 ≤ t)
    (hS : S t = 2) (hI : I t = 1) :
    HasDerivAt (fun s => dfeLyapunov 1 1 1 (S s) (E s) (I s)) (-5 / 2) t := by
  have := h.hasDerivAt_dfeLyapunov one_ne_zero one_ne_zero ht (by rw [hS]; norm_num)
  rwa [hS, hI, dfeLyapunovDeriv_val] at this

/-- The general bound `V̇₀ ≤ -μ (S - N)² / S` agrees at that state (`-5/2 ≤ -1/2`). -/
example : dfeLyapunovDeriv 2 1 1 1 1 2 1 ≤ -(1 * (2 - 1) ^ 2 / 2) :=
  dfeLyapunovDeriv_le one_pos zero_le_one one_pos hR_half zero_le_one

/-- At the threshold `R₀ = 1` (`β = 4`), `V̇₀ = 0` at `(S, I) = (N, 1)` although `I > 0`: the
Lyapunov function alone does not force `I → 0`. -/
example : R0 4 1 1 1 ≤ 1 := by norm_num [R0]
example : dfeLyapunovDeriv 4 1 1 1 1 1 1 = 0 := by norm_num [dfeLyapunovDeriv]

/-! ### An explicit trajectory with `R₀ = 0` (`β = 0`) -/

private theorem hasDerivAt_exp_neg (t : ℝ) : HasDerivAt (fun x => exp (-x)) (-exp (-t)) t :=
  ((hasDerivAt_neg t).exp).congr_deriv (by ring)

private theorem hasDerivAt_exp_neg_two (t : ℝ) :
    HasDerivAt (fun x => exp (-(2 * x))) (-(2 * exp (-(2 * t)))) t :=
  (((hasDerivAt_id' t).const_mul 2).neg.exp).congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- `S = 1 + e^{-t}`, `E = e^{-2t}`, `I = (t + 1) e^{-2t}`, `R = 2 e^{-t} - (t + 2) e^{-2t}`
solves the model `β = 0, σ = 1, γ = 1, μ = 1, N = 1`, checked against each right-hand side. -/
theorem isSolution_explicit :
    IsSolution 0 1 1 1 1 (fun t => 1 + exp (-t)) (fun t => exp (-(2 * t)))
      (fun t => (t + 1) * exp (-(2 * t))) (fun t => 2 * exp (-t) - (t + 2) * exp (-(2 * t))) :=
  ⟨fun t _ => ((hasDerivAt_exp_neg t).const_add 1).congr_deriv (by ring),
    fun t _ => (hasDerivAt_exp_neg_two t).congr_deriv (by ring),
    fun t _ => (((hasDerivAt_id' t).add_const 1).mul (hasDerivAt_exp_neg_two t)).congr_deriv
      (by ring),
    fun t _ => (((hasDerivAt_exp_neg t).const_mul 2).sub
      (((hasDerivAt_id' t).add_const 2).mul (hasDerivAt_exp_neg_two t))).congr_deriv (by ring)⟩

example : R0 0 1 1 1 = 0 := by norm_num [R0]
theorem hR_zero : R0 0 1 1 1 ≤ 1 := by norm_num [R0]

/-- The trajectory starts in the open orthant: `(S, E, I)(0) = (2, 1, 1)`. -/
example : (1 + exp (-0) : ℝ) = 2 ∧ exp (-(2 * 0)) = (1 : ℝ) ∧ ((0 : ℝ) + 1) * exp (-(2 * 0)) = 1 :=
  by norm_num

/-- **Global attractivity on the explicit trajectory**: `(S, E, I) → (1, 0, 0)`. -/
theorem explicit_tendsto :
    Tendsto (fun t => (1 + exp (-t), exp (-(2 * t)), (t + 1) * exp (-(2 * t)))) atTop
      (𝓝 ((1 : ℝ), (0 : ℝ), (0 : ℝ))) :=
  isSolution_explicit.tendsto_diseaseFree le_rfl one_pos zero_le_one one_pos one_pos hR_zero
    (by positivity) (by positivity) (by positivity)

/-- Independent check of the `S` and `E` limits, from `e^{-t} → 0`. -/
example : Tendsto (fun t : ℝ => 1 + exp (-t)) atTop (𝓝 1) := by
  simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_add 1)

example : Tendsto (fun t : ℝ => exp (-(2 * t))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop two_pos)

/-- `R → R* = γ · 0 / μ = 0` on the explicit trajectory. -/
example : Tendsto (fun t => 2 * exp (-t) - (t + 2) * exp (-(2 * t))) atTop (𝓝 0) :=
  isSolution_explicit.tendsto_removed_diseaseFree le_rfl one_pos zero_le_one one_pos one_pos
    hR_zero (by positivity) (by positivity) (by positivity)

/-- Lyapunov stability of `(1, 0, 0)` (`ε = 1`) applied to the explicit trajectory. -/
example : ∃ δ > 0, dist ((1 + exp (-0) : ℝ), exp (-(2 * 0) : ℝ), ((0 : ℝ) + 1) * exp (-(2 * 0)))
      ((1 : ℝ), (0 : ℝ), (0 : ℝ)) < δ →
    ∀ t, 0 ≤ t → dist (1 + exp (-t), exp (-(2 * t)), (t + 1) * exp (-(2 * t)))
      ((1 : ℝ), (0 : ℝ), (0 : ℝ)) < 1 := by
  obtain ⟨δ, hδ, hst⟩ :=
    diseaseFree_lyapunovStable le_rfl one_pos zero_le_one one_pos one_pos hR_zero 1 one_pos
  exact ⟨δ, hδ, hst _ _ _ _ isSolution_explicit (by positivity) (by positivity) (by positivity)⟩

/-- The global asymptotic stability theorem, attractivity half, on the explicit trajectory. -/
example : Tendsto (fun t => (1 + exp (-t), exp (-(2 * t)), (t + 1) * exp (-(2 * t)))) atTop
    (𝓝 ((1 : ℝ), (0 : ℝ), (0 : ℝ))) :=
  (diseaseFree_globallyAsymptoticallyStable le_rfl one_pos zero_le_one one_pos one_pos
    hR_zero).2 _ _ _ _ isSolution_explicit (by positivity) (by positivity) (by positivity)

/-! ### `R₀ > 1`: disease-free stability is not claimed -/

/-- For `β = 8` (`R₀ = 2`) the hypothesis `R₀ ≤ 1` fails. -/
example : ¬ R0 8 1 1 1 ≤ 1 := by norm_num [R0]

/-- `V̇₀ = (8 - 4) · 1 = 4 > 0` at `(1, 1, 1)`: `V₀` is not a Lyapunov function above the
threshold. -/
example : dfeLyapunovDeriv 8 1 1 1 1 1 1 = 4 := by norm_num [dfeLyapunovDeriv]

/-- The constant endemic solution starts in the open orthant and does not converge to the
disease-free state `(1, 0, 0)`: the conclusion of `tendsto_diseaseFree` is false at `R₀ = 2`. -/
example : ¬ Tendsto (fun _ : ℝ => ((1 / 2 : ℝ), (1 / 4 : ℝ), (1 / 8 : ℝ))) atTop
    (𝓝 ((1 : ℝ), (0 : ℝ), (0 : ℝ))) := by
  rw [tendsto_const_nhds_iff]
  norm_num

/-! ### `R → R*` with explicit numbers -/

/-- `β = 12, σ = 1, γ = 2, μ = 1, N = 1`: `R₀ = 12 / (2 · 3) = 2`. -/
theorem hR12 : 1 < R0 12 1 2 1 := by norm_num [R0]

example : endemicS 12 1 2 1 1 = 1 / 2 := by norm_num [endemicS]
example : endemicE 12 1 2 1 1 = 1 / 4 := by norm_num [endemicE, endemicS]
example : endemicI 12 1 2 1 1 = 1 / 12 := by norm_num [endemicI, endemicE, endemicS]

/-- `R* = γ I* / μ = 2 · (1/12) / 1 = 1/6`, from the definitions. -/
example : endemicR 12 1 2 1 1 = 1 / 6 := by norm_num [endemicR, endemicI, endemicE, endemicS]

/-- `S* + E* + I* + R* = 1/2 + 1/4 + 1/12 + 1/6 = 1 = N`. -/
example : endemicS 12 1 2 1 1 + endemicE 12 1 2 1 1 + endemicI 12 1 2 1 1 +
    endemicR 12 1 2 1 1 = 1 := by norm_num [endemicR, endemicI, endemicE, endemicS]

/-- The constant solution at `(1/2, 1/4, 1/12, 1/6)`, checked against each right-hand side. -/
theorem isSolution_const12 :
    IsSolution 12 1 2 1 1 (fun _ => 1 / 2) (fun _ => 1 / 4) (fun _ => 1 / 12) (fun _ => 1 / 6) :=
  ⟨fun t _ => (hasDerivAt_const t _).congr_deriv (by norm_num),
    fun t _ => (hasDerivAt_const t _).congr_deriv (by norm_num),
    fun t _ => (hasDerivAt_const t _).congr_deriv (by norm_num),
    fun t _ => (hasDerivAt_const t _).congr_deriv (by norm_num)⟩

/-- `tendsto_removed_endemic` on it: `R → R* = endemicR 12 1 2 1 1`. -/
example : Tendsto (fun _ : ℝ => (1 / 6 : ℝ)) atTop (𝓝 (endemicR 12 1 2 1 1)) :=
  isSolution_const12.tendsto_removed_endemic one_pos zero_le_two one_pos one_pos hR12
    (by norm_num) (by norm_num) (by norm_num)

/-- `tendsto_removed` with `I → 1/12` gives `R → 2 · (1/12) / 1 = 1/6`. -/
example : Tendsto (fun _ : ℝ => (1 / 6 : ℝ)) atTop (𝓝 (2 * (1 / 12) / 1)) :=
  isSolution_const12.tendsto_removed one_pos tendsto_const_nhds

/-- `tendsto_total` on it: `S + E + I + R → N = 1`. -/
example : Tendsto (fun _ : ℝ => (1 / 2 : ℝ) + 1 / 4 + 1 / 12 + 1 / 6) atTop (𝓝 1) :=
  isSolution_const12.tendsto_total one_pos

/-! ### Existence -/

/-- **Concrete existence** at `β = σ = γ = 1`, `μ = 0.1`, `N = 1`, initial data
`(0.9, 0.05, 0.05, 0)`. The initial values come from the theorem; the initial derivatives are
computed from the right-hand sides in `IsSolution`:
`S'(0) = 0.1 - 0.9 · 0.05 - 0.1 · 0.9 = -0.035`, `E'(0) = 0.045 - 1.1 · 0.05 = -0.01`,
`I'(0) = 0.05 - 1.1 · 0.05 = -0.005`, `R'(0) = 0.05 - 0.1 · 0 = 0.05`. The total stays
`≤ max 1 1 = 1`. -/
theorem exists_concrete : ∃ S E I R : ℝ → ℝ, IsSolution 1 1 1 0.1 1 S E I R ∧
    S 0 = 0.9 ∧ E 0 = 0.05 ∧ I 0 = 0.05 ∧ R 0 = 0 ∧
    HasDerivAt S (-0.035) 0 ∧ HasDerivAt E (-0.01) 0 ∧ HasDerivAt I (-0.005) 0 ∧
    HasDerivAt R 0.05 0 ∧ ∀ t, 0 ≤ t → S t + E t + I t + R t ≤ 1 := by
  obtain ⟨S, E, I, R, h, h0, h1, h2, h3, -, htot⟩ :=
    exists_isSolution (β := 1) (σ := 1) (γ := 1) (μ := 0.1) (N := 1) zero_le_one one_pos
      zero_le_one (by norm_num) one_pos (S₀ := 0.9) (E₀ := 0.05) (I₀ := 0.05) (R₀ := 0)
      (by norm_num) (by norm_num) (by norm_num) le_rfl
  refine ⟨S, E, I, R, h, h0, h1, h2, h3, ?_, ?_, ?_, ?_, fun t ht => ?_⟩
  · exact (h.hasDerivAt_susceptible 0 le_rfl).congr_deriv (by rw [h0, h2]; norm_num)
  · exact (h.hasDerivAt_exposed 0 le_rfl).congr_deriv (by rw [h0, h1, h2]; norm_num)
  · exact (h.hasDerivAt_infected 0 le_rfl).congr_deriv (by rw [h1, h2]; norm_num)
  · exact (h.hasDerivAt_removed 0 le_rfl).congr_deriv (by rw [h2, h3]; norm_num)
  · have := htot t ht
    norm_num at this
    linarith

/-- The existence theorem discharges the `IsSolution` hypothesis of the stability theorem with a
non-constant solution: in the `R₀ = 2` model, the solution from `(0.9, 0.05, 0.05, 0)` (which is
not the equilibrium `(1/2, 1/4, 1/8)`) converges to the endemic equilibrium. -/
example : ∃ S E I R : ℝ → ℝ, IsSolution 8 1 1 1 1 S E I R ∧
    S 0 = 0.9 ∧ E 0 = 0.05 ∧ I 0 = 0.05 ∧ R 0 = 0 ∧
    Tendsto (fun t => (S t, E t, I t)) atTop
      (𝓝 (endemicS 8 1 1 1 1, endemicE 8 1 1 1 1, endemicI 8 1 1 1 1)) := by
  obtain ⟨S, E, I, R, h, h0, h1, h2, h3, -, -⟩ :=
    exists_isSolution (β := 8) (σ := 1) (γ := 1) (μ := 1) (N := 1) (by norm_num) one_pos
      zero_le_one one_pos one_pos (S₀ := 0.9) (E₀ := 0.05) (I₀ := 0.05) (R₀ := 0)
      (by norm_num) (by norm_num) (by norm_num) le_rfl
  exact ⟨S, E, I, R, h, h0, h1, h2, h3, h.tendsto_endemic one_pos zero_le_one one_pos one_pos hR
    (by rw [h0]; norm_num) (by rw [h1]; norm_num) (by rw [h2]; norm_num)⟩

/-- `μ = 0` is outside `exists_isSolution`, whose hypothesis `0 < μ` fails there. -/
example : ¬ (0 : ℝ) < 0 := lt_irrefl 0

/-- `μ = 0` is covered separately by `exists_isSolution_of_nonneg` (hypothesis `0 ≤ μ`), and the
solution solves the closed SEIR model by `isSolution_zero_iff`; the total stays `≤ 1`. -/
example : ∃ S E I R : ℝ → ℝ, MathlibExt.Biology.Epidemiology.SEIR.IsSolution 1 1 1 1 S E I R ∧
    S 0 = 0.9 ∧ E 0 = 0.05 ∧ I 0 = 0.05 ∧ R 0 = 0 ∧
    ∀ t, 0 ≤ t → S t + E t + I t + R t ≤ 1 := by
  obtain ⟨S, E, I, R, h, h0, h1, h2, h3, -, htot⟩ :=
    exists_isSolution_of_nonneg (β := 1) (σ := 1) (γ := 1) (μ := 0) (N := 1) zero_le_one
      zero_le_one zero_le_one le_rfl zero_le_one (S₀ := 0.9) (E₀ := 0.05) (I₀ := 0.05) (R₀ := 0)
      (by norm_num) (by norm_num) (by norm_num) le_rfl
  refine ⟨S, E, I, R, isSolution_zero_iff.1 h, h0, h1, h2, h3, fun t ht => ?_⟩
  have := htot t ht
  norm_num at this
  linarith

/-- Negative initial data: the hypothesis `0 ≤ S₀` of `exists_isSolution` fails at `S₀ = -1`. -/
example : ¬ (0 : ℝ) ≤ -1 := by norm_num

/-- Negative initial data: no solution with `S(0) = -1` lies in the feasible region, from the
initial value alone (independently of the existence theorem). -/
example : ¬ ∃ S E I R : ℝ → ℝ, IsSolution 1 1 1 0.1 1 S E I R ∧ S 0 = -1 ∧
    ∀ t, 0 ≤ t → 0 ≤ S t ∧ 0 ≤ E t ∧ 0 ≤ I t ∧ 0 ≤ R t := by
  rintro ⟨S, E, I, R, -, h0, hnn⟩
  have := (hnn 0 le_rfl).1
  rw [h0] at this
  norm_num at this

end MathlibExtTest.Biology.Epidemiology.SEIRGlobalStability
