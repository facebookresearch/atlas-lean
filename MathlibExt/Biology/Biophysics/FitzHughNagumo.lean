/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import MathlibExt.Biology.Dynamics.PlanarStability
import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# FitzHugh–Nagumo dynamics

## The model (frozen form)

This file works with FitzHugh's form of the FitzHugh–Nagumo model of an excitable membrane:

  `v' = v - v³ / 3 - w + I`,
  `w' = ε (v + a - b w)`,

where `v` is the (dimensionless) membrane potential (fast variable), `w` the recovery variable
(slow variable), and the four real parameters are

* `a ∈ ℝ`: offset of the recovery nullcline (FitzHugh's classical value `a = 0.7`);
* `b > 0`: recovery feedback (classically `0 < b < 1`, e.g. `b = 0.8`);
* `ε > 0`: time-scale ratio (classically small, e.g. `ε = 0.08`);
* `I ∈ ℝ`: applied current (stimulus).

`vField I v w` and `wField a b ε v w` are the two right-hand sides and `field a b ε I` the
packed field on `ℝ × ℝ`. `IsSolution a b ε I v w` asks for the two equations at every `t ≥ 0`
with two-sided derivatives. The results below state their hypotheses on `a, b, ε, I` explicitly;
global existence, the invariant region, and boundedness need `b > 0`, `ε > 0`; uniqueness of
the equilibrium needs `0 < b ≤ 1`.

## Main results

* **Invariant region (trapping).** With `energy ε v w = v² + w² / ε`, the derivative of the
  energy along the field is `energyFlux a b ε I v w = ⟪∇energy, field⟫ =
  2 (v² - v⁴/3 + I v + a w - b w²)` (`hasDerivAt_energy`). `energyFlux_neg_of_energy_eq`: for
  `b, ε > 0` and every level `R > trapRadius a b ε I`, the field points strictly inward on the
  ellipse `energy = R`. `IsSolution.energy_le`: the sublevel set `energy ≤ R` is therefore
  forward invariant, and `IsSolution.energy_le_max` bounds every solution.
  `IsSolution.energy_le_absorb`: `energy(t) ≤ e^{-2κt} energy(0) + (C/κ)(1 - e^{-2κt})`
  (`C = absorbConst a b I`, `κ = decayRate b ε`); the bound converges exponentially to
  `C/κ = trapRadius`.
* **Global existence and uniqueness.** `exists_isSolution`: for `b, ε > 0` every initial state
  has a solution on `[0, ∞)`; `IsSolution.eq_of_initial`: it is unique forward in time.
* **Equilibria.** `isEquilibrium_iff`: equilibria are `w = (v + a) / b` with
  `eqCubic a b I v = 0`. `existsUnique_equilibrium`: for `0 < b ≤ 1` there is exactly one.
* **Linearization and classification.** `jacobian b ε v = !![1 - v², -1; ε, -ε b]` is the matrix
  of partial derivatives of the field (`jacobian_eq_partials`); its trace is
  `jacTrace b ε v = 1 - v² - ε b` and its determinant `jacDet b ε v = ε (1 - b + b v²)`
  (`trace_jacobian`, `det_jacobian`), and its complex eigenvalues are the roots of
  `z² - τ z + Δ` (`det_jacobian_sub`, `isCharRoot_iff_det`). The planar trace–determinant theory
  (characteristic roots, the Routh–Hurwitz criteria, and the classification `linearType`) is in
  `MathlibExt.Biology.Dynamics.PlanarStability`. `equilibriumType b ε v` is the type of the
  equilibrium with voltage `v`. For `0 < b < 1`, `ε > 0` the Jacobian is Hurwitz
  (`Matrix.IsHurwitz`) iff `v² > 1 - ε b` (`isHurwitz_jacobian_iff_of_lt_one`), has an
  eigenvalue in the open right half-plane iff `v² < 1 - ε b`
  (`exists_spectrum_jacobian_re_pos_iff_of_lt_one`), and is a linear center (purely imaginary
  eigenvalues, a nonhyperbolic equilibrium) iff `v² = 1 - ε b`
  (`equilibriumType_eq_center_iff_of_lt_one`,
  `re_eq_zero_and_im_ne_zero_of_mem_spectrum_jacobian`). `isLinearlyStable_iff_of_lt_one` and
  `isLinearlyUnstable_iff_of_lt_one` state the first two in trace–determinant form.
  `equilibriumType_eq_saddle_iff`: saddles occur iff `b (1 - v²) > 1`.
* **Post-pulse drift (single pulse).** A pulse of amplitude `δ` moves the rest state `(v*, w*)`
  to `(v* + δ, w*)`. The voltage is rising after the pulse (`IsRisingAfterPulse`) when the
  voltage field is positive there and falling (`IsFallingAfterPulse`) when it is negative; this
  is the instantaneous drift only, not a statement about the trajectory.
  `vField_pulse`: at rest, `vField I (v* + δ) w* = δ (1 - v*² - v* δ - δ² / 3)`;
  `isRisingAfterPulse_iff`, `isFallingAfterPulse_iff`: for `v*² ≤ 4` and `δ > 0` the voltage
  rises after the pulse iff `pulseRootLow v* < δ < pulseRootHigh v*`, the two amplitudes at
  which the post-pulse state lies on the voltage nullcline. `pulseRootLow_pos`: the lower root
  is positive for `v* < -1`. `stable_rest_pulse_drift`: for `0 < b < 1`, `ε > 0`, at a rest state
  on the left branch `-2 ≤ v* < -1` the Jacobian is Hurwitz, the voltage falls after small
  pulses and rises after pulses between the two roots (an empty range at `v* = -2`, where the
  roots coincide). `stable_rest_rising_pulse_window`: on the open branch `-2 < v* < -1` the
  roots are moreover distinct (`pulseRootLow_lt_pulseRootHigh`), so the rising window is a
  nonempty open interval of positive amplitudes. Along trajectories
  (`IsSolution.v_le_of_barrier`, `IsSolution.le_v_of_barrier`, `IsSolution.exists_v_ge`,
  `single_pulse_response`): while the slow variable has drifted by at most `η` (bounded by
  `|ε| M t`, `IsSolution.abs_w_sub_le`, with `M` from the trapping ellipse,
  `abs_le_of_energy_le`), after a pulse whose drift is negative with margin `η` the voltage
  never exceeds its post-pulse value, whereas if the voltage field stays above `η` up to a level
  `γ` the voltage reaches `γ` within an explicit time. These trajectory statements carry their
  slow-drift, margin and time hypotheses explicitly; they do not follow from
  `IsRisingAfterPulse` alone.

The singular-perturbation (`ε → 0`) analysis, a trajectory-level firing threshold, the full return
to rest after a spike, periodic orbits and bifurcations (a linear center is only a nonhyperbolic
linearization; no transversality or nonlinear nondegeneracy condition is checked), and the Nagumo
cubic `v (v - α)(1 - v)` form are not treated.

## References

* R. FitzHugh, *Impulses and physiological states in theoretical models of nerve membrane*,
  Biophys. J. 1 (1961), 445–466.
* J. Nagumo, S. Arimoto, S. Yoshizawa, *An active pulse transmission line simulating nerve
  axon*, Proc. IRE 50 (1962), 2061–2070.
* J. Keener, J. Sneyd, *Mathematical Physiology I*, 2nd ed., Springer (2009), §5.2.
* E. M. Izhikevich, *Dynamical Systems in Neuroscience*, MIT Press (2007), §4.2 and §7.1.
-/

@[expose] public noncomputable section

open Set Filter Real
open scoped Topology

namespace MathlibExt.Biology.Biophysics.FitzHughNagumo

open MathlibExt.Biology.Dynamics.PlanarStability

/-! ### The model -/

/-- Voltage (fast) component of the FitzHugh–Nagumo field: `v - v³/3 - w + I`. -/
def vField (I v w : ℝ) : ℝ := v - v ^ 3 / 3 - w + I

/-- Recovery (slow) component of the FitzHugh–Nagumo field: `ε (v + a - b w)`. -/
def wField (a b ε v w : ℝ) : ℝ := ε * (v + a - b * w)

/-- The FitzHugh–Nagumo field on the state space `ℝ × ℝ` of pairs `(v, w)`. -/
def field (a b ε I : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (vField I x.1 x.2, wField a b ε x.1 x.2)

/-- `(v, w)` solves the FitzHugh–Nagumo system on `[0, ∞)` (two-sided derivatives at every
`t ≥ 0`). -/
def IsSolution (a b ε I : ℝ) (v w : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt v (vField I (v t) (w t)) t ∧ HasDerivAt w (wField a b ε (v t) (w t)) t

variable {a b ε I : ℝ} {v w : ℝ → ℝ}

theorem contDiff_field {n : WithTop ℕ∞} : ContDiff ℝ n (field a b ε I) := by
  unfold field vField wField
  fun_prop

/-! ### Energy, the trapping ellipse, and forward invariance -/

/-- The energy `v² + w² / ε`, whose sublevel sets are the trapping ellipses. -/
def energy (ε v w : ℝ) : ℝ := v ^ 2 + w ^ 2 / ε

/-- The flux `⟪∇energy, field⟫ = 2 v · vField + (2 w / ε) · wField` of the field through the
level sets of `energy`: the derivative of `energy` along trajectories (`hasDerivAt_energy`).
It is negative exactly where the field points into the sublevel set. -/
def energyFlux (a b ε I v w : ℝ) : ℝ := 2 * v * vField I v w + 2 * w / ε * wField a b ε v w

/-- The flux in closed form (the coupling terms `∓ v w` cancel). -/
theorem energyFlux_eq (hε : ε ≠ 0) (v w : ℝ) :
    energyFlux a b ε I v w = 2 * (v ^ 2 - v ^ 4 / 3 + I * v + a * w - b * w ^ 2) := by
  unfold energyFlux vField wField
  field_simp
  ring

/-- The constant `C = 5 + I²/2 + a²/(2b)` in the dissipation inequality. -/
def absorbConst (a b I : ℝ) : ℝ := 5 + I ^ 2 / 2 + a ^ 2 / (2 * b)

/-- The decay rate `κ = min 1 (b ε / 2)` in the dissipation inequality. -/
def decayRate (b ε : ℝ) : ℝ := min 1 (b * ε / 2)

/-- Every ellipse `energy = R` with `R > trapRadius a b ε I = C / κ` is trapping. -/
def trapRadius (a b ε I : ℝ) : ℝ := absorbConst a b I / decayRate b ε

theorem decayRate_pos (hb : 0 < b) (hε : 0 < ε) : 0 < decayRate b ε :=
  lt_min one_pos (by positivity)

theorem absorbConst_pos (hb : 0 < b) : 0 < absorbConst a b I := by
  unfold absorbConst; positivity

theorem trapRadius_pos (hb : 0 < b) (hε : 0 < ε) : 0 < trapRadius a b ε I :=
  div_pos (absorbConst_pos hb) (decayRate_pos hb hε)

/-- **Dissipation inequality.** `energyFlux ≤ 2 (C - κ · energy)`. -/
theorem energyFlux_le (hb : 0 < b) (hε : 0 < ε) (v w : ℝ) :
    energyFlux a b ε I v w ≤ 2 * (absorbConst a b I - decayRate b ε * energy ε v w) := by
  rw [energyFlux_eq hε.ne']
  have h1 : v ^ 2 - v ^ 4 / 3 + I * v ≤ 5 + I ^ 2 / 2 - v ^ 2 := by
    nlinarith [sq_nonneg (v ^ 2 - 15 / 4), sq_nonneg (v - I)]
  have h2 : a * w - b * w ^ 2 ≤ a ^ 2 / (2 * b) - b / 2 * w ^ 2 := by
    have : a ^ 2 / (2 * b) - b / 2 * w ^ 2 - (a * w - b * w ^ 2) = (b * w - a) ^ 2 / (2 * b) := by
      field_simp; ring
    nlinarith [div_nonneg (sq_nonneg (b * w - a)) (by positivity : (0 : ℝ) ≤ 2 * b)]
  have hk1 : decayRate b ε ≤ 1 := min_le_left _ _
  have hk2 : decayRate b ε ≤ b * ε / 2 := min_le_right _ _
  have hk0 := (decayRate_pos hb hε).le
  have h3 : decayRate b ε * energy ε v w ≤ v ^ 2 + b / 2 * w ^ 2 := by
    unfold energy
    have hw : decayRate b ε * (w ^ 2 / ε) ≤ b / 2 * w ^ 2 := by
      rw [mul_div_assoc', div_le_iff₀ hε]
      nlinarith [sq_nonneg w, mul_le_mul_of_nonneg_right hk2 (sq_nonneg w)]
    nlinarith [mul_le_mul_of_nonneg_right hk1 (sq_nonneg v)]
  unfold absorbConst
  linarith

/-- **Trapping.** For `b, ε > 0` and every level `R > trapRadius a b ε I`, the field points
strictly into the ellipse `energy ε v w ≤ R` at every point of its boundary `energy ε v w = R`:
the flux `⟪∇energy, field⟫` is negative there. -/
theorem energyFlux_neg_of_energy_eq (hb : 0 < b) (hε : 0 < ε) {R : ℝ}
    (hR : trapRadius a b ε I < R) {v w : ℝ} (hvw : energy ε v w = R) :
    energyFlux a b ε I v w < 0 := by
  have hk := decayRate_pos hb hε
  have : absorbConst a b I < decayRate b ε * R := by
    rwa [trapRadius, div_lt_iff₀ hk, mul_comm] at hR
  have := energyFlux_le (I := I) (a := a) hb hε v w
  rw [hvw] at this
  linarith

/-- The derivative of the energy along a trajectory is the flux. -/
theorem hasDerivAt_energy {t : ℝ} (hv : HasDerivAt v (vField I (v t) (w t)) t)
    (hw : HasDerivAt w (wField a b ε (v t) (w t)) t) :
    HasDerivAt (fun s => energy ε (v s) (w s)) (energyFlux a b ε I (v t) (w t)) t := by
  have := (hv.pow 2).add ((hw.pow 2).div_const ε)
  refine this.congr_deriv ?_
  unfold energyFlux
  push_cast
  ring

/-- **Forward invariance of the trapping ellipses.** For `b, ε > 0` and `R > trapRadius`, a
solution starting in `energy ≤ R` stays there for all `t ≥ 0`.

Proof: `t ↦ energy (v t) (w t)` can only reach the level `R` with negative derivative
(`energyFlux_neg_of_energy_eq`), so Mathlib's fencing lemma
`image_le_of_deriv_right_lt_deriv_boundary'` keeps it below the constant barrier `R`. -/
theorem IsSolution.energy_le (h : IsSolution a b ε I v w) (hb : 0 < b) (hε : 0 < ε) {R : ℝ}
    (hR : trapRadius a b ε I < R) (h0 : energy ε (v 0) (w 0) ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    energy ε (v t) (w t) ≤ R := by
  have hd : ∀ s ∈ Icc 0 t, HasDerivAt (fun s => energy ε (v s) (w s))
      (energyFlux a b ε I (v s) (w s)) s := fun s hs =>
    hasDerivAt_energy (h s hs.1).1 (h s hs.1).2
  refine image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => R) (B' := fun _ => 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) h0 continuousOn_const
    (fun _ _ => hasDerivWithinAt_const _ _ _) (fun s _ hs => ?_) ⟨ht, le_rfl⟩
  exact energyFlux_neg_of_energy_eq hb hε hR hs

/-- **Boundedness.** For `b, ε > 0` every solution stays in the ellipse of level
`max (energy at 0) (trapRadius + 1)` for all `t ≥ 0`. -/
theorem IsSolution.energy_le_max (h : IsSolution a b ε I v w) (hb : 0 < b) (hε : 0 < ε)
    {t : ℝ} (ht : 0 ≤ t) :
    energy ε (v t) (w t) ≤ max (energy ε (v 0) (w 0)) (trapRadius a b ε I + 1) :=
  h.energy_le hb hε (lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)) (le_max_left _ _) ht

/-- **Absorption.** For `b, ε > 0`, with `C = absorbConst a b I` and `κ = decayRate b ε`,
`energy(t) ≤ e^{-2κt} energy(0) + (C / κ)(1 - e^{-2κt})` for `t ≥ 0`; in particular every
solution eventually enters every trapping ellipse (`C / κ = trapRadius`).

Proof: the dissipation inequality `energy' ≤ 2C - 2κ energy` and Mathlib's Grönwall bound
`le_gronwallBound_of_liminf_deriv_right_le` with `K = -2κ`. -/
theorem IsSolution.energy_le_absorb (h : IsSolution a b ε I v w) (hb : 0 < b) (hε : 0 < ε)
    {t : ℝ} (ht : 0 ≤ t) :
    energy ε (v t) (w t) ≤ exp (-(2 * decayRate b ε) * t) * energy ε (v 0) (w 0) +
      trapRadius a b ε I * (1 - exp (-(2 * decayRate b ε) * t)) := by
  have hk := decayRate_pos hb hε
  have hd : ∀ s ∈ Icc 0 t, HasDerivAt (fun s => energy ε (v s) (w s))
      (energyFlux a b ε I (v s) (w s)) s := fun s hs =>
    hasDerivAt_energy (h s hs.1).1 (h s hs.1).2
  have := le_gronwallBound_of_liminf_deriv_right_le (f := fun s => energy ε (v s) (w s))
    (δ := energy ε (v 0) (w 0)) (K := -(2 * decayRate b ε)) (ε := 2 * absorbConst a b I)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs _ hr => ((hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt).liminf_right_slope_le hr)
    le_rfl (fun s hs => by
      have := energyFlux_le (a := a) (I := I) hb hε (v s) (w s)
      linarith) t ⟨ht, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 (by linarith), sub_zero] at this
  convert this using 1
  unfold trapRadius
  field_simp
  ring

/-! ### Global existence and forward uniqueness -/

/-- The packed field satisfies the spacetime local Lipschitz hypothesis of
`ode_maximal_solution_exit_compact` on `U = univ`. -/
theorem field_locallyLipschitz (a b ε I : ℝ) (p : ℝ × (ℝ × ℝ)) :
    ∃ C : NNReal, ∃ s ∈ 𝓝 p, ∀ t : ℝ, ∀ x y : ℝ × ℝ,
      (t, x) ∈ s ∩ univ → (t, y) ∈ s ∩ univ →
        dist (Function.uncurry (fun _ : ℝ => field a b ε I) (t, x))
          (Function.uncurry (fun _ : ℝ => field a b ε I) (t, y)) ≤ C * dist x y := by
  obtain ⟨C, hC⟩ := ((contDiff_field (a := a) (b := b) (ε := ε) (I := I) (n := 1)).contDiffOn
    (s := Metric.closedBall p.2 1)).exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
    (isCompact_closedBall _ _)
  refine ⟨C, univ ×ˢ Metric.closedBall p.2 1,
    prod_mem_nhds univ_mem (Metric.closedBall_mem_nhds _ one_pos), ?_⟩
  rintro t x y ⟨⟨-, hx⟩, -⟩ ⟨⟨-, hy⟩, -⟩
  exact hC.dist_le_mul x hx y hy

/-- The trapping ellipses are compact. -/
theorem isCompact_energy_le (hε : 0 < ε) (R : ℝ) :
    IsCompact {x : ℝ × ℝ | energy ε x.1 x.2 ≤ R} := by
  have hcont : Continuous fun x : ℝ × ℝ => energy ε x.1 x.2 := by unfold energy; fun_prop
  refine (isCompact_Icc (a := ((-(R + 1), -(ε * R + 1)) : ℝ × ℝ)) (b := (R + 1, ε * R + 1)))
    |>.of_isClosed_subset (isClosed_le hcont continuous_const) ?_
  rintro ⟨x, y⟩ hxy
  simp only [mem_ofPred_eq, energy] at hxy
  have hx : x ^ 2 ≤ R := by nlinarith [div_nonneg (sq_nonneg y) hε.le]
  have hy : y ^ 2 ≤ ε * R := by
    have : y ^ 2 / ε ≤ R := by nlinarith [sq_nonneg x]
    rwa [div_le_iff₀ hε, mul_comm] at this
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only <;> nlinarith [sq_nonneg (x + 1 / 2),
    sq_nonneg (x - 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (y - 1 / 2)]

/-- **Global existence.** For `b, ε > 0` every initial state `(v₀, w₀)` has a solution of the
FitzHugh–Nagumo system on `[0, ∞)`.

Proof: the maximal solution of `ode_maximal_solution_exit_compact` (`U = univ`, `t₀ = 0`) stays
over `[0, T] ∩ J` in the compact set `[0, T] ×ˢ {energy ≤ R}`, `R = max (energy₀) (trapRadius + 1)`
(`IsSolution.energy_le`, applied on `[0, T]`); if some `T ≥ 0` were not in its open interval
`J`, the time `max c 0` would contradict the forward exit from that compact set. -/
theorem exists_isSolution (hb : 0 < b) (hε : 0 < ε) (v₀ w₀ : ℝ) :
    ∃ v w : ℝ → ℝ, IsSolution a b ε I v w ∧ v 0 = v₀ ∧ w 0 = w₀ := by
  obtain ⟨J, x, hx0, hJo, h0J, hJc, hxd, hexit⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact univ
      (Function.uncurry (fun _ : ℝ => field a b ε I)) 0 (v₀, w₀) isOpen_univ trivial
      ((contDiff_field (n := 0)).continuous.comp continuous_snd).continuousOn
      fun p _ => field_locallyLipschitz a b ε I p
  have hd : ∀ t ∈ J, HasDerivAt (fun s => (x s).1) (vField I (x t).1 (x t).2) t ∧
      HasDerivAt (fun s => (x s).2) (wField a b ε (x t).1 (x t).2) t := fun t ht =>
    ⟨(hxd t ht).2.fst, (hxd t ht).2.snd⟩
  set R := max (energy ε v₀ w₀) (trapRadius a b ε I + 1)
  have hR : trapRadius a b ε I < R := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  -- the energy bound on `[0, T]` for `T ∈ J`
  have hbd : ∀ T ∈ J, 0 ≤ T → energy ε (x T).1 (x T).2 ≤ R := by
    intro T hT hT0
    have hdT : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => energy ε (x s).1 (x s).2)
        (energyFlux a b ε I (x s).1 (x s).2) s := fun s hs =>
      hasDerivAt_energy (hd s (hJc 0 h0J T hT hs)).1 (hd s (hJc 0 h0J T hT hs)).2
    refine image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => R) (B' := fun _ => 0)
      (fun s hs => (hdT s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hdT s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp only [hx0]; exact le_max_left _ _) continuousOn_const
      (fun _ _ => hasDerivWithinAt_const _ _ _) (fun s _ hs => ?_) ⟨hT0, le_rfl⟩
    exact energyFlux_neg_of_energy_eq hb hε hR hs
  have hglobal : Ici 0 ⊆ J := by
    intro T hT0
    by_contra hTJ
    obtain ⟨⟨c, hcJ, hc⟩, -⟩ := hexit (Icc 0 T ×ˢ {x : ℝ × ℝ | energy ε x.1 x.2 ≤ R})
      (isCompact_Icc.prod (isCompact_energy_le hε R)) (subset_univ _)
    have htJ : max c 0 ∈ J := by rcases max_choice c 0 with h | h <;> rw [h] <;> assumption
    set t := max c 0
    have ht0 : 0 ≤ t := le_max_right _ _
    have htT : t ≤ T := by
      by_contra h
      exact hTJ (hJc 0 h0J t htJ ⟨hT0, (not_le.1 h).le⟩)
    exact hc t htJ (le_max_left _ _) ⟨⟨ht0, htT⟩, hbd t htJ ht0⟩
  exact ⟨fun s => (x s).1, fun s => (x s).2, fun t ht => hd t (hglobal ht),
    by simp [hx0], by simp [hx0]⟩

/-- **Forward uniqueness.** Two solutions with the same initial state agree at every `t ≥ 0`
(any real parameters).

Proof: on `[0, t]` both packed curves lie in a common closed ball, on which the polynomial field
is Lipschitz; apply Mathlib's `ODE_solution_unique_of_mem_Icc_right`. -/
theorem IsSolution.eq_of_initial {v' w' : ℝ → ℝ} (h : IsSolution a b ε I v w)
    (h' : IsSolution a b ε I v' w') (hv : v 0 = v' 0) (hw : w 0 = w' 0) {t : ℝ} (ht : 0 ≤ t) :
    v t = v' t ∧ w t = w' t := by
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun s => (v s, w s)) (field a b ε I (v s, w s)) s :=
    fun s hs => (h s hs).1.prodMk (h s hs).2
  have hd' : ∀ s, 0 ≤ s → HasDerivAt (fun s => (v' s, w' s)) (field a b ε I (v' s, w' s)) s :=
    fun s hs => (h' s hs).1.prodMk (h' s hs).2
  have hc : ContinuousOn (fun s => (v s, w s)) (Icc 0 t) :=
    fun s hs => (hd s hs.1).continuousAt.continuousWithinAt
  have hc' : ContinuousOn (fun s => (v' s, w' s)) (Icc 0 t) :=
    fun s hs => (hd' s hs.1).continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc'
  obtain ⟨K, hK⟩ := ((contDiff_field (a := a) (b := b) (ε := ε) (I := I) (n := 1)).contDiffOn
    (s := Metric.closedBall 0 (max C₁ C₂))).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => field a b ε I) (s := fun _ => Metric.closedBall 0 (max C₁ C₂))
    (fun _ _ => hK) hc (fun s hs => (hd s hs.1).hasDerivWithinAt)
    (fun s hs => mem_closedBall_zero_iff.2
      ((hC₁ s (Ico_subset_Icc_self hs)).trans (le_max_left _ _)))
    hc' (fun s hs => (hd' s hs.1).hasDerivWithinAt)
    (fun s hs => mem_closedBall_zero_iff.2
      ((hC₂ s (Ico_subset_Icc_self hs)).trans (le_max_right _ _)))
    (by simp [hv, hw]) ⟨ht, le_rfl⟩
  exact Prod.ext_iff.1 heq

/-! ### Equilibria -/

/-- `(v, w)` is an equilibrium (rest state) of the FitzHugh–Nagumo field. -/
def IsEquilibrium (a b ε I v w : ℝ) : Prop := vField I v w = 0 ∧ wField a b ε v w = 0

/-- The equilibrium cubic `v - v³/3 - (v + a)/b + I`: the voltage field on the recovery
nullcline `w = (v + a)/b`. -/
def eqCubic (a b I v : ℝ) : ℝ := v - v ^ 3 / 3 - (v + a) / b + I

/-- Equilibria lie on the recovery nullcline `w = (v + a)/b` at roots of the equilibrium cubic. -/
theorem isEquilibrium_iff (hb : b ≠ 0) (hε : ε ≠ 0) {v w : ℝ} :
    IsEquilibrium a b ε I v w ↔ w = (v + a) / b ∧ eqCubic a b I v = 0 := by
  unfold IsEquilibrium vField wField eqCubic
  constructor
  · rintro ⟨h1, h2⟩
    have hw : w = (v + a) / b := by
      rw [eq_div_iff hb]
      have := (mul_eq_zero.1 h2).resolve_left hε
      linarith
    exact ⟨hw, by rw [← hw]; linarith⟩
  · rintro ⟨hw, h⟩
    refine ⟨by rw [hw]; linarith, ?_⟩
    rw [hw]
    field_simp
    ring

/-- For `0 < b ≤ 1` the equilibrium cubic is strictly decreasing. -/
theorem eqCubic_strictAnti (hb : 0 < b) (hb1 : b ≤ 1) : StrictAnti (eqCubic a b I) := by
  intro u v huv
  unfold eqCubic
  have h1b : 1 ≤ 1 / b := by rw [le_div_iff₀ hb]; linarith
  have key : (v - v ^ 3 / 3 - (v + a) / b + I) - (u - u ^ 3 / 3 - (u + a) / b + I) =
      (v - u) * (1 - (u ^ 2 + u * v + v ^ 2) / 3 - 1 / b) := by
    field_simp
    ring
  have hq : 0 < u ^ 2 + u * v + v ^ 2 := by
    nlinarith [sq_nonneg (u + v), mul_pos (sub_pos.2 huv) (sub_pos.2 huv)]
  have : (v - u) * (1 - (u ^ 2 + u * v + v ^ 2) / 3 - 1 / b) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  linarith

/-- For `0 < b ≤ 1` the equilibrium cubic has a root (intermediate value theorem on
`[-M, M]`, `M = 3 + |I| + |a|/b`). -/
theorem exists_eqCubic_eq_zero (hb : 0 < b) (hb1 : b ≤ 1) : ∃ v, eqCubic a b I v = 0 := by
  set M := 3 + |I| + |a| / b with hMdef
  have hab : 0 ≤ |a| / b := div_nonneg (abs_nonneg a) hb.le
  have hM : 3 ≤ M := by have := abs_nonneg I; linarith
  have hcont : Continuous (eqCubic a b I) := by
    unfold eqCubic
    fun_prop
  have hMb : M ≤ M / b := le_div_self (by linarith) hb hb1
  have hdiv : |a / b| = |a| / b := by rw [abs_div, abs_of_pos hb]
  have ha1 := neg_abs_le (a / b)
  have ha2 := le_abs_self (a / b)
  have hI1 := neg_abs_le I
  have hI2 := le_abs_self I
  have hneg : eqCubic a b I M ≤ 0 := by
    unfold eqCubic
    rw [add_div]
    nlinarith [mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ M ^ 2)]
  have hpos : 0 ≤ eqCubic a b I (-M) := by
    unfold eqCubic
    rw [add_div, neg_div]
    nlinarith [mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ M ^ 2)]
  obtain ⟨v, -, hv⟩ := intermediate_value_Icc' (by linarith : -M ≤ M) hcont.continuousOn
    ⟨hneg, hpos⟩
  exact ⟨v, hv⟩

/-- **Unique rest state.** For `0 < b ≤ 1` and `ε ≠ 0` (any `a`, `I`) the FitzHugh–Nagumo field
has exactly one equilibrium. -/
theorem existsUnique_equilibrium (hb : 0 < b) (hb1 : b ≤ 1) (hε : ε ≠ 0) :
    ∃! p : ℝ × ℝ, IsEquilibrium a b ε I p.1 p.2 := by
  obtain ⟨v, hv⟩ := exists_eqCubic_eq_zero (a := a) (I := I) hb hb1
  refine ⟨(v, (v + a) / b), (isEquilibrium_iff hb.ne' hε).2 ⟨rfl, hv⟩, ?_⟩
  rintro ⟨u, x⟩ h
  obtain ⟨hx, hu⟩ := (isEquilibrium_iff hb.ne' hε).1 h
  have : u = v := (eqCubic_strictAnti hb hb1).injective (hu.trans hv.symm)
  subst this
  exact Prod.ext rfl hx

/-! ### Linearization -/

/-- The Jacobian matrix of the field at a state with voltage `v`
(rows: `vField`, `wField`; columns: `∂/∂v`, `∂/∂w`). -/
def jacobian (b ε v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - v ^ 2, -1; ε, -(ε * b)]

theorem hasDerivAt_vField_v (I v w : ℝ) : HasDerivAt (fun u => vField I u w) (1 - v ^ 2) v := by
  have := (((hasDerivAt_id v).sub ((hasDerivAt_pow 3 v).div_const 3)).sub_const w).add_const I
  refine this.congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

theorem hasDerivAt_vField_w (I v w : ℝ) : HasDerivAt (fun x => vField I v x) (-1) w := by
  have := ((hasDerivAt_id w).const_sub (v - v ^ 3 / 3)).add_const I
  exact this.congr_deriv (by simp)

theorem hasDerivAt_wField_v (a b ε v w : ℝ) : HasDerivAt (fun u => wField a b ε u w) ε v := by
  have := (((hasDerivAt_id v).add_const a).sub_const (b * w)).const_mul ε
  exact this.congr_deriv (by simp)

theorem hasDerivAt_wField_w (a b ε v w : ℝ) :
    HasDerivAt (fun x => wField a b ε v x) (-(ε * b)) w := by
  have := (((hasDerivAt_id w).const_mul b).const_sub (v + a)).const_mul ε
  exact this.congr_deriv (by simp)

/-- The entries of `jacobian b ε v` are the partial derivatives of the field at `(v, w)`. -/
theorem jacobian_eq_partials (a b ε I v w : ℝ) :
    HasDerivAt (fun u => vField I u w) (jacobian b ε v 0 0) v ∧
      HasDerivAt (fun x => vField I v x) (jacobian b ε v 0 1) w ∧
      HasDerivAt (fun u => wField a b ε u w) (jacobian b ε v 1 0) v ∧
      HasDerivAt (fun x => wField a b ε v x) (jacobian b ε v 1 1) w := by
  simpa [jacobian] using ⟨hasDerivAt_vField_v I v w, hasDerivAt_vField_w I v w,
    hasDerivAt_wField_v a b ε v w, hasDerivAt_wField_w a b ε v w⟩

/-- Trace of the Jacobian: `τ = 1 - v² - ε b`. -/
def jacTrace (b ε v : ℝ) : ℝ := 1 - v ^ 2 - ε * b

/-- Determinant of the Jacobian: `Δ = ε (1 - b + b v²)`. -/
def jacDet (b ε v : ℝ) : ℝ := ε * (1 - b + b * v ^ 2)

theorem trace_jacobian (b ε v : ℝ) : (jacobian b ε v).trace = jacTrace b ε v := by
  simp [jacobian, Matrix.trace_fin_two, jacTrace]
  ring

theorem det_jacobian (b ε v : ℝ) : (jacobian b ε v).det = jacDet b ε v := by
  simp [jacobian, Matrix.det_fin_two, jacDet]
  ring

/-- The complex eigenvalues of the Jacobian are exactly the characteristic roots of
`(jacTrace, jacDet)`: `det (J - z 1) = z² - τ z + Δ`. -/
theorem det_jacobian_sub (b ε v : ℝ) (z : ℂ) :
    ((jacobian b ε v).map (fun r : ℝ => (r : ℂ)) - z • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det =
      z ^ 2 - jacTrace b ε v * z + jacDet b ε v := by
  simp [jacobian, Matrix.det_fin_two, jacTrace, jacDet]
  ring

theorem isCharRoot_iff_det (b ε v : ℝ) (z : ℂ) :
    IsCharRoot (jacTrace b ε v) (jacDet b ε v) z ↔
      ((jacobian b ε v).map (fun r : ℝ => (r : ℂ)) -
        z • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
  rw [det_jacobian_sub, IsCharRoot]

/-! ### Classification of the FitzHugh–Nagumo equilibria -/

/-- The linearization type of the FitzHugh–Nagumo equilibrium with voltage `v`, a function of the
parameters `b`, `ε` and of `v` (which itself depends on `a`, `b`, `I` through `eqCubic`). -/
def equilibriumType (b ε v : ℝ) : LinearType := linearType (jacTrace b ε v) (jacDet b ε v)

/-- Saddles occur exactly when `b (1 - v²) > 1` (impossible for `0 < b ≤ 1`). -/
theorem equilibriumType_eq_saddle_iff (hε : 0 < ε) {v : ℝ} :
    equilibriumType b ε v = .saddle ↔ 1 < b * (1 - v ^ 2) := by
  rw [equilibriumType, linearType_eq_saddle_iff, jacDet]
  constructor
  · intro h; nlinarith [(mul_neg_iff.1 h)]
  · intro h; exact mul_neg_of_pos_of_neg hε (by linarith)

/-- In the classical regime `0 < b < 1`, `ε > 0` the determinant is positive: no saddles and no
zero eigenvalue. -/
theorem jacDet_pos (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε) (v : ℝ) : 0 < jacDet b ε v := by
  unfold jacDet; have := sq_nonneg v; positivity

/-- **Stability of the rest state (`0 < b < 1`, `ε > 0`).** The equilibrium with voltage `v` is
linearly stable (both eigenvalues in the open left half-plane) iff `v² > 1 - ε b`. -/
theorem isLinearlyStable_iff_of_lt_one (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε) {v : ℝ} :
    IsLinearlyStable (jacTrace b ε v) (jacDet b ε v) ↔ 1 - ε * b < v ^ 2 := by
  rw [isLinearlyStable_iff, jacTrace]
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; exact ⟨by linarith, jacDet_pos hb hb1 hε v⟩

/-- **Instability (`0 < b < 1`, `ε > 0`).** The equilibrium is linearly unstable (an eigenvalue in
the open right half-plane) iff `v² < 1 - ε b`. -/
theorem isLinearlyUnstable_iff_of_lt_one (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε) {v : ℝ} :
    IsLinearlyUnstable (jacTrace b ε v) (jacDet b ε v) ↔ v ^ 2 < 1 - ε * b := by
  rw [isLinearlyUnstable_iff, jacTrace]
  have := jacDet_pos hb hb1 hε v
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h; exact Or.inl (by linarith)

/-- The Jacobian is Hurwitz (`Matrix.IsHurwitz`) iff its trace–determinant pair is linearly
stable. -/
theorem isHurwitz_jacobian_iff_isLinearlyStable (b ε v : ℝ) :
    (jacobian b ε v).IsHurwitz ↔ IsLinearlyStable (jacTrace b ε v) (jacDet b ε v) := by
  rw [isHurwitz_iff_isLinearlyStable, trace_jacobian, det_jacobian]

/-- **Stability of the rest state, Hurwitz form (`0 < b < 1`, `ε > 0`).** The Jacobian at the
equilibrium with voltage `v` is Hurwitz (every eigenvalue in the open left half-plane) iff
`v² > 1 - ε b`. -/
theorem isHurwitz_jacobian_iff_of_lt_one (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε) {v : ℝ} :
    (jacobian b ε v).IsHurwitz ↔ 1 - ε * b < v ^ 2 :=
  (isHurwitz_jacobian_iff_isLinearlyStable b ε v).trans
    (isLinearlyStable_iff_of_lt_one hb hb1 hε)

/-- **Instability, eigenvalue form (`0 < b < 1`, `ε > 0`).** The Jacobian has an eigenvalue in the
open right half-plane iff `v² < 1 - ε b` (from `exists_spectrum_re_pos_iff`). -/
theorem exists_spectrum_jacobian_re_pos_iff_of_lt_one (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε)
    {v : ℝ} :
    (∃ μ ∈ spectrum ℂ ((jacobian b ε v).map (algebraMap ℝ ℂ)), 0 < μ.re) ↔
      v ^ 2 < 1 - ε * b := by
  rw [exists_spectrum_re_pos_iff, trace_jacobian, det_jacobian, ← isLinearlyUnstable_iff]
  exact isLinearlyUnstable_iff_of_lt_one hb hb1 hε

/-- **Purely imaginary eigenvalues (`0 < b < 1`, `ε > 0`).** The linearization is a center
(purely imaginary eigenvalues, so the equilibrium is nonhyperbolic) iff `v² = 1 - ε b`. This is a
condition on the linearization only: no transversality or nonlinear nondegeneracy is claimed. -/
theorem equilibriumType_eq_center_iff_of_lt_one (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε)
    {v : ℝ} :
    equilibriumType b ε v = .center ↔ v ^ 2 = 1 - ε * b := by
  rw [equilibriumType, linearType_eq_center_iff, jacTrace]
  have := jacDet_pos hb hb1 hε v
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨this, by linarith⟩

/-- At the linear center `v² = 1 - ε b` (`0 < b < 1`, `ε > 0`) every eigenvalue of the Jacobian is
purely imaginary and nonzero. -/
theorem re_eq_zero_and_im_ne_zero_of_mem_spectrum_jacobian (hb : 0 < b) (hb1 : b < 1)
    (hε : 0 < ε) {v : ℝ} (hv : v ^ 2 = 1 - ε * b) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ ((jacobian b ε v).map (algebraMap ℝ ℂ))) :
    μ.re = 0 ∧ μ.im ≠ 0 := by
  rw [mem_spectrum_iff_isCharRoot, trace_jacobian, det_jacobian] at hμ
  have hτ : jacTrace b ε v = 0 := by unfold jacTrace; linarith
  have hΔ := jacDet_pos hb hb1 hε v
  exact ⟨hμ.re_eq_zero hτ hΔ, hμ.im_ne_zero (by rw [hτ]; nlinarith)⟩

/-! ### Post-pulse drift of a single pulse -/

/-- After a pulse of amplitude `δ` applied to the state `(v, w)` (an instantaneous voltage jump to
`(v + δ, w)`) the voltage is **rising**: the voltage field is positive at the post-pulse state.
This is the instantaneous drift only; it says nothing about the later trajectory. -/
def IsRisingAfterPulse (I v w δ : ℝ) : Prop := 0 < vField I (v + δ) w

/-- After a pulse of amplitude `δ` the voltage is **falling**: the voltage field is negative at the
post-pulse state. -/
def IsFallingAfterPulse (I v w δ : ℝ) : Prop := vField I (v + δ) w < 0

/-- At a zero of the voltage field (in particular at rest), the post-pulse voltage field is
`δ (1 - v² - v δ - δ²/3)`. -/
theorem vField_pulse {v w : ℝ} (h : vField I v w = 0) (δ : ℝ) :
    vField I (v + δ) w = δ * (1 - v ^ 2 - v * δ - δ ^ 2 / 3) := by
  unfold vField at *
  linear_combination h

/-- The lower root `(-3v - √(12 - 3v²))/2` of the post-pulse factor `1 - v² - v δ - δ²/3` in `δ`
(`pulse_factor`, for `v² ≤ 4`): from a rest state with voltage `v`, a pulse of this amplitude
lands on the voltage nullcline. On the left branch `-2 < v < -1` it is positive, and the positive
pulses after which the voltage rises are exactly those with
`pulseRootLow v < δ < pulseRootHigh v` (`isRisingAfterPulse_iff`), a nonempty open interval
(`pulseRootLow_lt_pulseRootHigh`). -/
def pulseRootLow (v : ℝ) : ℝ := (-3 * v - √(12 - 3 * v ^ 2)) / 2

/-- The upper root `(-3v + √(12 - 3v²))/2` of the post-pulse factor (`pulse_factor`). On the left
branch `-2 < v < -1` it is the upper end of the open interval of positive pulses after which the
voltage rises, from a rest state with voltage `v`. -/
def pulseRootHigh (v : ℝ) : ℝ := (-3 * v + √(12 - 3 * v ^ 2)) / 2

theorem pulse_factor {v : ℝ} (hv : v ^ 2 ≤ 4) (δ : ℝ) :
    1 - v ^ 2 - v * δ - δ ^ 2 / 3 = -((δ - pulseRootLow v) * (δ - pulseRootHigh v)) / 3 := by
  have hs : √(12 - 3 * v ^ 2) ^ 2 = 12 - 3 * v ^ 2 := Real.sq_sqrt (by linarith)
  unfold pulseRootLow pulseRootHigh
  linear_combination (-1 / 12 : ℝ) * hs

theorem pulseRootLow_le_pulseRootHigh (v : ℝ) : pulseRootLow v ≤ pulseRootHigh v := by
  unfold pulseRootLow pulseRootHigh
  have := Real.sqrt_nonneg (12 - 3 * v ^ 2)
  linarith

/-- For `v² < 4` the two roots are distinct. -/
theorem pulseRootLow_lt_pulseRootHigh {v : ℝ} (hv : v ^ 2 < 4) :
    pulseRootLow v < pulseRootHigh v := by
  unfold pulseRootLow pulseRootHigh
  have := Real.sqrt_pos.2 (by linarith : (0 : ℝ) < 12 - 3 * v ^ 2)
  linarith

/-- **Rising window.** At rest with `v² ≤ 4`, the voltage rises after a positive pulse `δ` iff
`pulseRootLow v < δ < pulseRootHigh v`. -/
theorem isRisingAfterPulse_iff {v w δ : ℝ} (h : vField I v w = 0) (hv : v ^ 2 ≤ 4) (hδ : 0 < δ) :
    IsRisingAfterPulse I v w δ ↔ pulseRootLow v < δ ∧ δ < pulseRootHigh v := by
  rw [IsRisingAfterPulse, vField_pulse h, pulse_factor hv]
  have hle := pulseRootLow_le_pulseRootHigh v
  constructor
  · intro hpos
    have : (δ - pulseRootLow v) * (δ - pulseRootHigh v) < 0 := by
      by_contra hc; push Not at hc
      nlinarith
    rcases mul_neg_iff.1 this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact absurd hle (by linarith)
  · rintro ⟨h1, h2⟩
    have : (δ - pulseRootLow v) * (δ - pulseRootHigh v) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    nlinarith

/-- At rest with `v² ≤ 4`, the voltage falls after a positive pulse `δ` iff `δ < pulseRootLow v`
or `δ > pulseRootHigh v`. -/
theorem isFallingAfterPulse_iff {v w δ : ℝ} (h : vField I v w = 0) (hv : v ^ 2 ≤ 4) (hδ : 0 < δ) :
    IsFallingAfterPulse I v w δ ↔ δ < pulseRootLow v ∨ pulseRootHigh v < δ := by
  rw [IsFallingAfterPulse, vField_pulse h, pulse_factor hv]
  have hle := pulseRootLow_le_pulseRootHigh v
  constructor
  · intro hneg
    have : 0 < (δ - pulseRootLow v) * (δ - pulseRootHigh v) := by
      by_contra hc; push Not at hc
      nlinarith
    rcases mul_pos_iff.1 this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (h1 | h1)
    · have : 0 < (δ - pulseRootLow v) * (δ - pulseRootHigh v) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      nlinarith
    · have : 0 < (δ - pulseRootLow v) * (δ - pulseRootHigh v) :=
        mul_pos (by linarith) (by linarith)
      nlinarith

/-- For a rest voltage `v < -1` (left branch of the cubic nullcline) the lower root
`pulseRootLow v` is positive. -/
theorem pulseRootLow_pos {v : ℝ} (hv1 : v < -1) : 0 < pulseRootLow v := by
  unfold pulseRootLow
  have hs : √(12 - 3 * v ^ 2) < -3 * v := by
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  linarith

/-- **The voltage falls after small pulses** on the left branch `-2 ≤ v < -1`. -/
theorem isFallingAfterPulse_of_lt_pulseRootLow {v w δ : ℝ} (h : vField I v w = 0) (hv1 : v < -1)
    (hv2 : -2 ≤ v) (hδ : 0 < δ) (hδθ : δ < pulseRootLow v) : IsFallingAfterPulse I v w δ :=
  (isFallingAfterPulse_iff h (by nlinarith) hδ).2 (Or.inl hδθ)

/-- **Post-pulse drift at a stable rest state.** In the classical regime `0 < b < 1`, `ε > 0`, at
an equilibrium on the left branch `-2 ≤ v < -1` the Jacobian is Hurwitz and `pulseRootLow v` is
positive: the voltage falls after pulses `0 < δ < pulseRootLow v` and rises after pulses
`pulseRootLow v < δ < pulseRootHigh v`. At the endpoint `v = -2` the two roots coincide
(`pulseRootLow (-2) = pulseRootHigh (-2) = 3`), so the last statement is vacuous and the voltage
rises after no positive pulse; `stable_rest_rising_pulse_window` treats `-2 < v < -1`. -/
theorem stable_rest_pulse_drift (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε) {v w : ℝ}
    (hrest : IsEquilibrium a b ε I v w) (hv1 : v < -1) (hv2 : -2 ≤ v) :
    (jacobian b ε v).IsHurwitz ∧ 0 < pulseRootLow v ∧
      (∀ δ, 0 < δ → δ < pulseRootLow v → IsFallingAfterPulse I v w δ) ∧
      (∀ δ, pulseRootLow v < δ → δ < pulseRootHigh v → IsRisingAfterPulse I v w δ) := by
  have hpos := pulseRootLow_pos hv1
  refine ⟨(isHurwitz_jacobian_iff_of_lt_one hb hb1 hε).2 (by nlinarith [mul_pos hε hb]), hpos,
    fun δ hδ hδθ => isFallingAfterPulse_of_lt_pulseRootLow hrest.1 hv1 hv2 hδ hδθ,
    fun δ h1 h2 => (isRisingAfterPulse_iff hrest.1 (by nlinarith) (by linarith)).2 ⟨h1, h2⟩⟩

/-- `stable_rest_pulse_drift` with the stability conclusion in trace–determinant form. -/
theorem stable_rest_pulse_drift_isLinearlyStable (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε)
    {v w : ℝ} (hrest : IsEquilibrium a b ε I v w) (hv1 : v < -1) (hv2 : -2 ≤ v) :
    IsLinearlyStable (jacTrace b ε v) (jacDet b ε v) ∧ 0 < pulseRootLow v ∧
      (∀ δ, 0 < δ → δ < pulseRootLow v → IsFallingAfterPulse I v w δ) ∧
      (∀ δ, pulseRootLow v < δ → δ < pulseRootHigh v → IsRisingAfterPulse I v w δ) := by
  obtain ⟨hst, hrest'⟩ := stable_rest_pulse_drift hb hb1 hε hrest hv1 hv2
  exact ⟨(isHurwitz_jacobian_iff_isLinearlyStable b ε v).1 hst, hrest'⟩

/-- **Rising window at a stable rest state.** In the classical regime `0 < b < 1`, `ε > 0`, at an
equilibrium on the open left branch `-2 < v < -1` the Jacobian is Hurwitz and
`0 < pulseRootLow v < pulseRootHigh v`: the voltage falls after pulses `0 < δ < pulseRootLow v`
and rises after pulses in the nonempty window `pulseRootLow v < δ < pulseRootHigh v`. This is
the instantaneous post-pulse drift; `single_pulse_response` gives trajectory bounds under
explicit slow-drift hypotheses. -/
theorem stable_rest_rising_pulse_window (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε) {v w : ℝ}
    (hrest : IsEquilibrium a b ε I v w) (hv1 : v < -1) (hv2 : -2 < v) :
    (jacobian b ε v).IsHurwitz ∧ 0 < pulseRootLow v ∧
      pulseRootLow v < pulseRootHigh v ∧
      (∀ δ, 0 < δ → δ < pulseRootLow v → IsFallingAfterPulse I v w δ) ∧
      (∀ δ, pulseRootLow v < δ → δ < pulseRootHigh v → IsRisingAfterPulse I v w δ) := by
  obtain ⟨hst, hpos, hsub, hsup⟩ := stable_rest_pulse_drift hb hb1 hε hrest hv1 hv2.le
  exact ⟨hst, hpos, pulseRootLow_lt_pulseRootHigh (by nlinarith), hsub, hsup⟩

/-- `stable_rest_rising_pulse_window` with the stability conclusion in trace–determinant form. -/
theorem stable_rest_rising_pulse_window_isLinearlyStable (hb : 0 < b) (hb1 : b < 1)
    (hε : 0 < ε) {v w : ℝ} (hrest : IsEquilibrium a b ε I v w) (hv1 : v < -1) (hv2 : -2 < v) :
    IsLinearlyStable (jacTrace b ε v) (jacDet b ε v) ∧ 0 < pulseRootLow v ∧
      pulseRootLow v < pulseRootHigh v ∧
      (∀ δ, 0 < δ → δ < pulseRootLow v → IsFallingAfterPulse I v w δ) ∧
      (∀ δ, pulseRootLow v < δ → δ < pulseRootHigh v → IsRisingAfterPulse I v w δ) := by
  obtain ⟨hst, hrest'⟩ := stable_rest_rising_pulse_window hb hb1 hε hrest hv1 hv2
  exact ⟨(isHurwitz_jacobian_iff_isLinearlyStable b ε v).1 hst, hrest'⟩

/-! ### Single-pulse response of the full system -/

/-- **Slow drift.** While `|v + a - b w| ≤ M` on `[0, T]`, the recovery variable moves by at most
`|ε| M t` by time `t ∈ [0, T]`. -/
theorem IsSolution.abs_w_sub_le (h : IsSolution a b ε I v w) {T M : ℝ}
    (hM : ∀ s ∈ Icc 0 T, |v s + a - b * w s| ≤ M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    |w t - w 0| ≤ |ε| * M * t := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := w) (a := 0) (b := t)
    (C := |ε| * M) (fun s hs => (h s hs.1).2.hasDerivWithinAt) (fun s hs => by
      rw [Real.norm_eq_abs, wField, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM s ⟨hs.1, hs.2.le.trans ht.2⟩) (abs_nonneg _))
    t ⟨ht.1, le_rfl⟩
  simpa [Real.norm_eq_abs] using this

/-- On the trapping ellipse `energy ≤ R`, `|v + a - b w| ≤ √R + |a| + |b| √(ε R)`. -/
theorem abs_le_of_energy_le (hε : 0 < ε) {R v w : ℝ} (h : energy ε v w ≤ R) :
    |v + a - b * w| ≤ √R + |a| + |b| * √(ε * R) := by
  unfold energy at h
  have hv : |v| ≤ √R := Real.abs_le_sqrt (by nlinarith [div_nonneg (sq_nonneg w) hε.le])
  have hw : |w| ≤ √(ε * R) := Real.abs_le_sqrt (by
    have : w ^ 2 / ε ≤ R := by nlinarith [sq_nonneg v]
    rwa [div_le_iff₀ hε, mul_comm] at this)
  calc |v + a - b * w| ≤ |v| + |a| + |b| * |w| := by
        rw [← abs_mul]
        exact (abs_sub _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ √R + |a| + |b| * √(ε * R) := by gcongr

/-- **Upper voltage barrier.** If the recovery variable stays within `η` of `w₀` on `[0, T]` and
`vField I β w₀ + η < 0`, a solution with `v 0 ≤ β` keeps `v ≤ β` on `[0, T]`. -/
theorem IsSolution.v_le_of_barrier (h : IsSolution a b ε I v w) {T β w₀ η : ℝ}
    (hw : ∀ t ∈ Icc 0 T, |w t - w₀| ≤ η) (hβ : vField I β w₀ + η < 0) (h0 : v 0 ≤ β) :
    ∀ t ∈ Icc 0 T, v t ≤ β := by
  intro t ht
  refine image_le_of_deriv_right_lt_deriv_boundary' (f := v) (B := fun _ => β) (B' := fun _ => 0)
    (fun s hs => (h s hs.1).1.continuousAt.continuousWithinAt)
    (fun s hs => (h s hs.1).1.hasDerivWithinAt) h0 continuousOn_const
    (fun _ _ => hasDerivWithinAt_const _ _ _) (fun s hs hvs => ?_) ht
  have := abs_le.1 (hw s (Ico_subset_Icc_self hs))
  unfold vField at hβ ⊢
  rw [hvs]
  linarith

/-- **Lower voltage barrier.** If the recovery variable stays within `η` of `w₀` on `[0, T]` and
`vField I α w₀ > η`, a solution with `α ≤ v 0` keeps `α ≤ v` on `[0, T]`. -/
theorem IsSolution.le_v_of_barrier (h : IsSolution a b ε I v w) {T α w₀ η : ℝ}
    (hw : ∀ t ∈ Icc 0 T, |w t - w₀| ≤ η) (hα : η < vField I α w₀) (h0 : α ≤ v 0) :
    ∀ t ∈ Icc 0 T, α ≤ v t := by
  intro t ht
  have := image_le_of_deriv_right_lt_deriv_boundary' (f := fun s => -v s) (B := fun _ => -α)
    (B' := fun _ => 0) (f' := fun s => -vField I (v s) (w s))
    (fun s hs => (h s hs.1).1.neg.continuousAt.continuousWithinAt)
    (fun s hs => (h s hs.1).1.neg.hasDerivWithinAt) (by simpa using h0) continuousOn_const
    (fun _ _ => hasDerivWithinAt_const _ _ _) (fun s hs hvs => ?_) ht
  · simpa using this
  have := abs_le.1 (hw s (Ico_subset_Icc_self hs))
  have hvs' : v s = α := by simpa using hvs
  unfold vField at hα ⊢
  rw [hvs']
  linarith

/-- **Reaching a voltage level.** If the recovery variable stays within `η` of `w₀` on `[0, T]`,
the voltage field satisfies `vField I u w₀ ≥ m > η` for all `u ∈ [α, γ]`, and `T` is long enough
(`γ - α ≤ (m - η) T`), then a solution with `α ≤ v 0` reaches the level `γ` within `[0, T]`. -/
theorem IsSolution.exists_v_ge (h : IsSolution a b ε I v w) {T α γ w₀ η m : ℝ} (hT : 0 ≤ T)
    (hw : ∀ t ∈ Icc 0 T, |w t - w₀| ≤ η) (hαγ : α ≤ γ)
    (hm : ∀ u ∈ Icc α γ, m ≤ vField I u w₀) (hηm : η < m) (hTlen : γ - α ≤ (m - η) * T)
    (h0 : α ≤ v 0) : ∃ t ∈ Icc 0 T, γ ≤ v t := by
  by_contra hcon
  push Not at hcon
  have hα := h.le_v_of_barrier hw (lt_of_lt_of_le hηm (hm α ⟨le_rfl, hαγ⟩)) h0
  have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := T)
    (f := fun t => v 0 + (m - η) * t) (f' := fun _ => m - η) (B := v)
    (B' := fun t => vField I (v t) (w t))
    (by fun_prop) (fun s _ => by
      simpa using ((hasDerivAt_id s).const_mul (m - η)).const_add (v 0) |>.hasDerivWithinAt)
    (by simp) (fun s hs => (h s hs.1).1.continuousAt.continuousWithinAt)
    (fun s hs => (h s hs.1).1.hasDerivWithinAt) (fun s hs => by
      have hs' := Ico_subset_Icc_self hs
      have h1 := hm (v s) ⟨hα s hs', (hcon s hs').le⟩
      have h2 := abs_le.1 (hw s hs')
      unfold vField at h1 ⊢
      linarith) ⟨hT, le_rfl⟩
  have := hcon T ⟨hT, le_rfl⟩
  linarith

/-- **Single-pulse response.** Let `(vr, wr)` be a rest state, let a solution start at the
post-pulse state `(vr + δ, wr)`, and let `T ≥ 0`. Suppose `|v + a - b w| ≤ M` on `[0, T]` (for
`b, ε > 0` such an
`M` comes from the trapping ellipse, `abs_le_of_energy_le`), and put `η = |ε| M T`.

* If the post-pulse drift is negative with margin `η`, i.e. `δ (1 - vr² - vr δ - δ²/3) + η < 0`,
  the voltage never exceeds its post-pulse value `vr + δ` on `[0, T]`.
* If the voltage field at the frozen recovery value satisfies `vField I u wr ≥ m > η` on
  `[vr + δ, γ]` (in particular the voltage rises after the pulse, with margin `η`) and
  `γ - (vr + δ) ≤ (m - η) T`, the voltage reaches `γ` within `[0, T]`. -/
theorem single_pulse_response {vr wr δ : ℝ} (hrest : IsEquilibrium a b ε I vr wr)
    (h : IsSolution a b ε I v w) (hv0 : v 0 = vr + δ) (hw0 : w 0 = wr) {T M : ℝ} (hT : 0 ≤ T)
    (hM : ∀ s ∈ Icc 0 T, |v s + a - b * w s| ≤ M) :
    (δ * (1 - vr ^ 2 - vr * δ - δ ^ 2 / 3) + |ε| * M * T < 0 →
        ∀ t ∈ Icc 0 T, v t ≤ vr + δ) ∧
      (∀ γ m, vr + δ ≤ γ → (∀ u ∈ Icc (vr + δ) γ, m ≤ vField I u wr) → |ε| * M * T < m →
        γ - (vr + δ) ≤ (m - |ε| * M * T) * T → ∃ t ∈ Icc 0 T, γ ≤ v t) := by
  have hdrift : ∀ t ∈ Icc 0 T, |w t - wr| ≤ |ε| * M * T := by
    intro t ht
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
    rw [← hw0]
    exact (h.abs_w_sub_le hM ht).trans
      (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (abs_nonneg _) hM0))
  refine ⟨fun hsub => h.v_le_of_barrier hdrift ?_ hv0.le, fun γ m hγ hm hηm hTlen =>
    h.exists_v_ge hT hdrift hγ hm hηm hTlen hv0.ge⟩
  rwa [vField_pulse hrest.1]

end MathlibExt.Biology.Biophysics.FitzHughNagumo
