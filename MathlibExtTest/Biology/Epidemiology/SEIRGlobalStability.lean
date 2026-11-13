/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.SEIRGlobalStability

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

end MathlibExtTest.Biology.Epidemiology.SEIRGlobalStability
