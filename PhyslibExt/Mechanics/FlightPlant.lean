/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.ODE.Basic
public import PhyslibExt.Mechanics.RigidMotionPorts
public import PhyslibExt.Statistics.UncertaintyPropagation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import MathlibExt.Analysis.ODE.FiniteIntervalSublevel
import MathlibExt.Analysis.ODE.LyapunovStability
import MathlibExt.Analysis.ODE.MaximalSolution
import MathlibExt.LinearAlgebra.Matrix.SylvesterCriterion

/-!
# Six-degree-of-freedom flight plant: translational port, longitudinal trim and linearization

The body-axis translational equation of a rigid motion's centre of mass, derived from the
rotating-frame transport law, paired with the existing Euler equations of the same motion, the
plant defined by aerodynamic and propulsive force and moment maps on an admitted domain, and a
synthetic controlled longitudinal fixture of that plant with its trim, its actuator domain, its
linearization about the trim, a Lyapunov certificate for that linearization, and the local
existence and decay of the nonlinear reduced flight.

## i. Overview

A rigid vehicle is a Physlib `RigidBodyMotion` `M`: its mass `m = M.mass`, constant since the
mass distribution is body-fixed, the inertial coordinates `X(t)` of its centre-of-mass trajectory
and its orientation `R(t) ∈ SO(3)`, with the body-to-inertial convention `v_I = R v_B` of
`Units.EngineeringFrames`. The body velocity is `v_B = Rᵀ X'`, the velocity of the centre of mass
in body components (for a differentiable trajectory, `X'` has the components of Physlib's
`centerOfMassVelocity`, by `Time.derivVec_space`), and `ω_B` is Physlib's body angular velocity,
the vee of `Rᵀ Ṙ`. The translational and the rotational data thus belong to one rigid body.

The translational balance law `m X'' = R F_B + m g` is a model input: `F_B` is the aerodynamic and
propulsive force in body components and `g` the uniform gravitational acceleration in inertial
components. Since `X' = R v_B`, the transport law `d(R u)/dt = R (u' + ω_B × u)` of
`Mechanics.RigidMotionPorts` gives `X'' = R (v_B' + ω_B × v_B)`, and for a `C²` trajectory and
orientation the law holds exactly when

`v_B' = F_B / m + Rᵀ g - ω_B × v_B`

in body components. The rotational half is not proved again: `Mechanics.RigidMotionPorts`
transports the balance law `dL_COM/dt = τ_I` to Euler's equations
`I_B ω_B' + ω_B × (I_B ω_B) = Rᵀ τ_I`. The six-degree-of-freedom body equations pair the
translational equation with that Euler equation, and both inertial laws hold exactly when the pair
does.

Aerodynamic and propulsive maps are explicit model inputs with admitted domains: a force map and a
moment map defined only on the admitted states (a polar validity region, for example), so they are
never evaluated elsewhere. The plant itself requires positive mass and `C²` data on an open set of
times around the given time: without them the totalized inverse `m⁻¹ = 0` at `m = 0` would drop the
force from the translational equation, and `∂ₜ` of a nondifferentiable curve is a fallback value.
For a body frame centered at the centre of mass, the plant holds exactly when, in addition, the
state is admitted and the inertial laws hold with the force and the moment the maps give.

Section D is a synthetic ideal-force-controlled longitudinal fixture of the plant, in
nondimensional units with mass, pitch inertia, gravity, trim speed, air density and reference
area `1`; it is not a measured aircraft. The forward/up plane is spanned by the first two
inertial axes, gravity is `(0, -1, 0)`, and the pitch angle `θ` is the rotation `Rz(θ)` of
`Units.EngineeringFrames` about the third axis, so `θ > 0` turns the body forward axis
`R e₁ = (cos θ, sin θ, 0)` from forward toward up (nose up); it is not an aviation body-axis sign
convention. The state `(x, z, θ, q)` has the velocity `(1 + x, z, 0)`, the speed
`V = √((1 + x)² + z²)`, the pitch angle `θ` and the pitch rate `q`. The lift `½ V² C_L`, with
`C_L = 2`, acts along the velocity turned a quarter turn toward up, and the drag `½ V² C_D`, with
the polar `C_D = 1/10 + C_L²/20 = 3/10`, against it; both are written without division, so they
are defined (and zero) at `V = 0`, and both are independent of the attitude. The ideal vector
force actuator `A = (-x - x³, 1 - z, 0) - F_aero` and the pitch-moment actuator `M = -2 q - sin θ`
are explicit parts of the model, and the maps are admitted on the box of radius `1/100` in each
state coordinate. For a body of mass `1`, centre of mass `0` and unit pitch inertia about a
principal third axis, a planar motion (centre of mass in the forward/up plane, orientation
`Rz(θ)`) is a plant solution exactly when its state is in the box and obeys `x' = -x - x³`,
`z' = -z`, `θ' = q`, `q' = -2 q - sin θ`. At the zero state `V = 1`, the lift balances the unit
weight, and the drag and the horizontal actuator are `3/20`; the trim is a relative equilibrium:
the position moves as `p(t) = p₀ + (t, 0)`, not a stationary world position. On the box
`V ≥ 99/100`, `1/10 < A_x < 1/5`, `|A_z| < 1/20` and `|M| ≤ 3/100`, and a state of zero speed lies
outside it.

Section E linearizes the reduced field `f(x, z, θ, q) = (-x - x³, -z, q, -2 q - sin θ)` of the
fixture about its trim, the zero state. Its Jacobian there is
`A = diag(-1, -1) ⊕ [[0, 1], [-1, -2]]`, and `f e = A e + (-x³, 0, 0, θ - sin θ)`; this remainder is
also the first-order remainder `f (0 + δ) - f 0 - Df(0) δ` of
`Statistics.UncertaintyPropagation.jacobianRemainder`. For `0 < r ≤ 1/100` and a deviation `δ`
with every coordinate at most `r` in absolute value, `δ` lies in the actuator box and the
remainder components are at most `r ‖δ‖²`, `0`, `0` and `(r / 6) ‖δ‖²` in absolute value, with
`‖δ‖` the sup norm on `Fin 4 → ℝ`; the last bound is the cubic sine bound
`|θ - sin θ| ≤ |θ|³ / 6`. For every `0 < r`, the componentwise remainder theorem of
`Statistics.UncertaintyPropagation`, given the actual second derivatives and the constant
`H = (6 r, 0, 0, r)` that bounds their operator norms on the radius-`r` box, gives the looser
bounds `H i / 2 * ‖δ‖²` there. For a state `e : EuclideanSpace ℝ (Fin 4)`, with coordinates
`WithLp.ofLp e`, `‖ofLp e‖ ≤ ‖e‖ ≤ 2 ‖ofLp e‖` (sup norm outside, Euclidean norm in the middle),
the Euclidean ball of radius `r` lies in the box of radius `r`, and the bounds above hold with the
Euclidean norm. `A` linearizes the reduced state only: the world position is not part of it, and
every planar plant solution moves forward with position rate at least `99/100`.

Section F certifies the linearization. On the state `e : EuclideanSpace ℝ (Fin 4)`, with
coordinates `WithLp.ofLp e`, the Euclidean norm and nondimensional time `t : ℝ`, the reduced linear
plant is `e' = A e`. The Lyapunov matrix `P = diag(1/2, 1/2) ⊕ [[3/2, 1/2], [1/2, 1/2]]` and
`Q = 1` are symmetric positive definite, `P` by Sylvester's criterion (leading principal minors
`1/2`, `1/4`, `3/8`, `1/8`), and `Aᵀ P + P A = -Q`. The quadratic function `V(e) = eᵀ P e`
satisfies `(1/4) ‖e‖² ≤ V(e) ≤ 2 ‖e‖²` and vanishes only at the trim; its derivative is
`DV(e) h = 2 hᵀ P e`, so along the plant `DV(e) (A e) = -‖e‖²`, zero at the trim and negative
elsewhere. The linear plant is globally Lipschitz, so from every initial state it has exactly one
global solution, and Lyapunov's direct method gives `‖e t‖ ≤ √8 exp(-t / 4) ‖e 0‖` for `t ≥ 0`
along every forward solution, with `√8 = √(2 / (1/4))`; no converse (Hurwitz) theorem is used.
This is decay of the linear plant's own solutions; section G treats the nonlinear reduced field,
and neither section covers the world position.

Section G returns to the nonlinear reduced field `f` on the same Euclidean state,
`nonlinearReducedField`. Along it `DV(e) f(e) = 2 f(e)ᵀ P e = -‖e‖² - x⁴ + (θ + q) (θ - sin θ)`:
the linear part gives `-‖e‖²` and the remainder of section E the other terms. On the ball
`‖e‖ ≤ r = 1/100` the cubic sine bound of section E gives `DV(e) f(e) ≤ -(1/2) ‖e‖² ≤ -V(e) / 4`,
negative exactly away from the trim and `0` at it. The sublevel set `{V ≤ r² / 8}` is compact,
contains the ball `‖e‖ ≤ r / 4` and lies in the ball of radius `r / √2`, hence in the actuator box.
A forward solution that starts in it stays in it: before the first time it could reach the sphere
`‖e‖ = r`, `V` does not increase, so that time does not exist. For `‖e₀‖ ≤ r / 4` the maximal
solution in `ℝ × {‖e‖ < r}`, built from local Picard–Lindelöf solutions, never leaves the compact
set `[0, T] × {V ≤ r² / 8}`, so it is defined on `[0, ∞)` and stays in the actuator box, and the
direct method gives `‖e t‖ ≤ √8 exp(-t / 8) ‖e₀‖` for `t ≥ 0`, for every forward solution with
`‖e 0‖ ≤ r / 4`. Everything is forward in time: from `x₀ ≠ 0` the solution of `x' = -x - x³` blows
up in finite negative time. The decay is local, as the tests show: the inverted trim
`(0, 0, π, 0)` is an equilibrium whose constant solution does not decay, and from a state on the
sphere `‖e‖ = r` no forward solution stays in the ball, so the Lyapunov inequality alone gives only
conditional decay. This is the reduced field near the trim, not the six-degree-of-freedom plant or
the world position.

Model inputs (hypotheses of the module):

* the translational law `m X'' = R F_B + m g` and the rotational law `dL_COM/dt = R M_B`, with the
  body force `F_B` and the body moment `M_B` about the centre of mass, are assumed;
* the mass `m = M.mass` of the motion is positive, a hypothesis since Physlib's mass functional is
  an arbitrary linear functional, and constant, so no mass depletion is represented; the
  gravitational acceleration `g` is uniform;
* `R` (entry by entry) and the centre-of-mass trajectory (component by component) are `C²` on an
  open set of times; time derivatives are Physlib's `∂ₜ`;
* the rotational law takes a body frame centered at the centre of mass (`centerOfMass = 0`);
* the force and moment maps and their admitted domain are given;
* in section D, the synthetic lift, drag and polar, the ideal actuator laws and their admitted
  box are model inputs.

Non-goals: aerodynamic coefficient models other than the synthetic polar of section D, trim of
anything but the planar ideal-actuator fixture of section D, linearization of anything but its
reduced field about the trim (section E), stability of anything but the reduced linear plant and
the nonlinear reduced field near the trim (section F proves decay of the linear plant's own
solutions, section G local decay of the reduced field from the sublevel set `V ≤ 1/80000`; no
larger region of attraction and no decay of the world position), existence of trajectories for
given maps (section D exhibits only the trim trajectory; section F solves only the linear plant;
section G solves only the reduced field, forward in time, from that sublevel set), and any
empirical adequacy or system safety claim.

## ii. Key results

- `bodyVelocity`, `differentiableAt_bodyVelocity` : the body velocity `v_B = Rᵀ X'` of the centre
  of mass, differentiable along `C²` data.
- `newton_iff_deriv_bodyVelocity` : `m X'' = R F_B + m g` holds exactly when
  `v_B' = F_B / m + Rᵀ g - ω_B × v_B`.
- `SixDofBodyEquations`, `balanceLaws_iff_sixDofBodyEquations` : the translational body equation
  paired with Euler's equations, equivalent to both inertial balance laws.
- `ForceMomentMaps`, `SixDofPlant`, `sixDofPlant_iff` : force and moment maps on an admitted
  domain, and the plant they define, which requires positive mass and `C²` data.
- `liftCoeff`, `dragCoeff`, `flightSpeed`, `liftForce`, `dragForce`, `aeroForce`,
  `actuatorForce`, `pitchMoment`, `dragCoeff_eq`, `liftForce_dragForce_spec`,
  `aeroForce_add_actuatorForce_add_weight` : the synthetic aerodynamics and the ideal actuators
  of the longitudinal fixture.
- `reducedField`, `actuatorBox`, `pitchOrientation`, `longitudinalMaps`, `planarMotion`,
  `planarState`, `planar_sixDofPlant_iff` : the plant restricted to planar motions is the reduced
  longitudinal system on the actuator box.
- `trim_relative_equilibrium`, `actuatorBox_bounds`, `longitudinalMaps_rejects` : the trim as a
  relative equilibrium, the actuator bounds on the box, and no evaluation outside it.
- `longitudinalJacobian`, `longitudinalJacobian_eq_fromBlocks`, `hasFDerivAt_reducedField_zero` :
  the Jacobian `diag(-1, -1) ⊕ [[0, 1], [-1, -2]]` of the reduced field at the trim.
- `longitudinalRemainder`, `reducedField_eq_mulVec_add_remainder`,
  `jacobianRemainder_reducedField` : the remainder `(-x³, 0, 0, θ - sin θ)`.
- `longitudinalRemainder_bounds`, `longitudinalRemainder_bounds_euclidean` : its bounds on the box
  in the sup norm and on the ball in the Euclidean norm.
- `contDiff_reducedField`, `fderiv_fderiv_reducedField_apply`,
  `norm_fderiv_fderiv_reducedField_le`, `jacobianRemainder_reducedField_le_of_hessian` : the
  componentwise remainder bound from the actual second derivatives.
- `norm_ofLp_le_norm_le_two_mul`, `abs_ofLp_le_of_norm_le` : the sup and Euclidean norms of a
  state.
- `planar_sixDofPlant_forward_rate` : every plant solution moves forward.
- `longitudinalLyapunovMatrix`, `longitudinalLyapunovMatrix_eq_fromBlocks`,
  `longitudinalLyapunovMatrix_posDef`, `longitudinalLyapunov_equation` : the Lyapunov matrix
  `P = diag(1/2, 1/2) ⊕ [[3/2, 1/2], [1/2, 1/2]]`, positive definite like `1`, and
  `Aᵀ P + P A = -1`.
- `linearReducedField`, `linearReducedField_eq_fderiv` : the reduced linear plant `e' = A e` on the
  Euclidean state space, the derivative of the reduced field at the trim.
- `longitudinalLyapunov`, `longitudinalLyapunov_bounds`, `longitudinalLyapunov_eq_zero_iff`,
  `differentiable_longitudinalLyapunov`, `fderiv_longitudinalLyapunov_apply`,
  `fderiv_longitudinalLyapunov_linearReducedField` : `V(e) = eᵀ P e`, its comparison bounds, its
  only zero at the trim, its derivative `2 hᵀ P e` and its orbital derivative `-‖e‖²`.
- `existsUnique_linearReducedField_solution`, `norm_le_of_isIntegralCurveOn_linearReducedField`,
  `linearReducedField_solution_decay` : the global solution of the linear plant and the decay
  `‖e t‖ ≤ √8 exp(-t / 4) ‖e 0‖`.
- `nonlinearReducedField`, `ofLp_nonlinearReducedField` : the reduced field on the Euclidean
  state, the linear plant plus the remainder.
- `fderiv_longitudinalLyapunov_nonlinearReducedField`,
  `fderiv_longitudinalLyapunov_nonlinearReducedField_le`,
  `fderiv_longitudinalLyapunov_nonlinearReducedField_neg_iff` : its orbital derivative, the
  Lyapunov inequality on the ball `‖e‖ ≤ 1/100` and strict decay exactly away from the trim.
- `longitudinalLyapunov_sublevel_spec`,
  `mapsTo_sublevel_of_isIntegralCurveOn_nonlinearReducedField` : the compact invariant sublevel
  set `{V ≤ 1/80000}` inside the actuator box.
- `exists_nonlinearReducedField_solution`,
  `norm_le_of_isIntegralCurveOn_nonlinearReducedField_of_norm_le`,
  `norm_le_of_isIntegralCurveOn_nonlinearReducedField`, `nonlinearReducedField_solution_decay` :
  forward existence in the actuator box and the local decay `‖e t‖ ≤ √8 exp(-t / 8) ‖e 0‖`.

## iii. Table of contents

- A. Body velocity and the translational correspondence
- B. The six-degree-of-freedom body equations
- C. Coefficient maps with admitted domains
- D. A controlled longitudinal fixture
- E. Linearization about the trim
- F. A Lyapunov certificate for the reduced linear plant
- G. Local existence and decay of the nonlinear reduced flight

## iv. References

- B. L. Stevens, F. L. Lewis and E. N. Johnson, *Aircraft Control and Simulation*, 3rd edition,
  2016, chapter 1 (the rigid-body six-degree-of-freedom equations in body axes).
- B. Etkin, *Dynamics of Atmospheric Flight*, 1972 (the equations of motion in body axes and the
  longitudinal equations).
- J. D. Anderson, *Introduction to Flight*, McGraw-Hill (lift and drag coefficients and the
  parabolic drag polar `C_D = C_D0 + K C_L²`).
- L. D. Landau and E. M. Lifshitz, *Mechanics*, Sections 34 and 39 (the equations of motion of a
  rigid body; motion in a non-inertial frame of reference).
- H. K. Khalil, *Nonlinear Systems*, 3rd edition, 2002, Section 4.3 (linearization at an
  equilibrium; the Lyapunov equation), Sections 4.1 and 4.5 (Lyapunov's direct method,
  Theorem 4.10; positively invariant sublevel sets) and Section 3.1 (Theorem 3.3: a solution that
  stays in a compact set exists for all forward time).
- R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd edition, 2013, Theorem 7.2.5 (Sylvester's
  criterion).
- G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, 2012, Section 2.2 (global
  existence for globally Lipschitz fields), Theorem 2.13 and Corollaries 2.15 and 2.16 (maximal
  solutions leave every compact set).
- `Mechanics.RigidMotionPorts` (the transport law `deriv_bodyToInertialVec` and the Euler
  equivalence `deriv_comAngularMomentum_eq_iff_euler`), Physlib's
  `RigidBodyMotion.bodyAngularVelocity` and
  `RigidBodyMotion.deriv_orientation_mulVec_eq_orientation_bodyAngularVelocity_cross`, and the
  frame dictionary `Units.EngineeringFrames`.
- `Statistics.UncertaintyPropagation.jacobianRemainder_component_le_of_hessian` (the componentwise
  remainder bound from a Hessian bound) and Mathlib's `Real.abs_sub_sin_le` (the cubic sine bound).
- `IsIntegralCurveOn.norm_sub_le_of_lyapunov` (Lyapunov's direct method),
  `MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz` (global
  existence) and `Matrix.posDef_iff_leadingPrincipalMinors_pos` (Sylvester's criterion).
- `IsIntegralCurveOn.mapsTo_sublevel_of_lyapunov` (sublevel invariance),
  `MathlibExt.Analysis.ODE.finite_interval_mapsTo_sublevel` (sublevel invariance on a finite
  interval), `MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact`
  (maximal solutions leave compact sets) and Mathlib's `ContDiffAt.exists_lipschitzOnWith`.
-/

@[expose] public section

open scoped Matrix
open Time

namespace Mechanics.FlightPlant

open Units.EngineeringFrames Mechanics.RigidMotionPorts

/-! ## A. Body velocity and the translational correspondence -/

/-- The body velocity `v_B = Rᵀ X'` of the motion `M`: the body components of the velocity `X'`
of its centre of mass, with `X` the inertial coordinates of the centre-of-mass trajectory and `R`
the orientation. The time derivative is total: at a time where `X` is not differentiable, `X'` is
taken to be `0`. -/
noncomputable def bodyVelocity (M : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ :=
  inertialToBodyVec (M.orientation t) (∂ₜ (fun s j => M.comTrajectory s j) t)

/-- Entrywise `C²` regularity of the orientation on an open set gives differentiability with the
default matrix instances. -/
private lemma differentiableAt_orientation_of_entries (M : RigidBodyMotion 3) {U : Set Time}
    (hU : IsOpen U) (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    {t : Time} (ht : t ∈ U) : DifferentiableAt ℝ (fun s => (M.orientation s).1) t := by
  have h : DifferentiableAt ℝ (fun s => Matrix.of.symm (M.orientation s).1) t :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      ((hR i j).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)
  exact h

/-- The time derivative of a `C²` curve on an open set is differentiable there. -/
private lemma differentiableAt_deriv_of_two {X : Time → Fin 3 → ℝ} {U : Set Time}
    (hU : IsOpen U) (hX : ContDiffOn ℝ 2 X U) {t : Time} (ht : t ∈ U) :
    DifferentiableAt ℝ (∂ₜ X) t := by
  have h : ContDiffOn ℝ 1 (∂ₜ X) U :=
    (hX.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const
  exact (h.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)

/-- Along a motion whose orientation (entry by entry) and centre-of-mass trajectory (component by
component) are `C²` on an open set, the body velocity is differentiable, so `∂ₜ` of it is a
genuine derivative. -/
lemma differentiableAt_bodyVelocity (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (hX : ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) {t : Time} (ht : t ∈ U) :
    DifferentiableAt ℝ (bodyVelocity M) t := by
  have hXd := differentiableAt_deriv_of_two hU (contDiffOn_pi.2 hX) ht
  refine differentiableAt_pi.2 fun i => ?_
  simp only [bodyVelocity, inertialToBodyVec, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine DifferentiableAt.fun_sum fun j _ => ?_
  exact (((hR j i).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)).mul
    (differentiableAt_pi.1 hXd j)

/-- Translational correspondence: for a motion `M` of positive mass `m = M.mass` whose
orientation `R` (entry by entry) and centre-of-mass coordinates `X` are `C²` on an open set `U`, at
every `t ∈ U` the inertial law `m X'' = R F_B + m g` holds exactly when the body equation
`v_B' = F_B / m + Rᵀ g - ω_B × v_B` holds. -/
lemma newton_iff_deriv_bodyVelocity (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (hX : ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) (hm : 0 < M.mass)
    (FB g : Fin 3 → ℝ) {t : Time} (ht : t ∈ U) :
    M.mass • ∂ₜ (∂ₜ (fun s j => M.comTrajectory s j)) t =
        bodyToInertialVec (M.orientation t) FB + M.mass • g ↔
      ∂ₜ (bodyVelocity M) t = M.mass⁻¹ • FB + inertialToBodyVec (M.orientation t) g -
        M.bodyAngularVelocity t ⨯₃ bodyVelocity M t := by
  -- `X' = R v_B`, so the transport law of the rotating-frame module gives `X''`
  have hfun : ∂ₜ (fun s j => M.comTrajectory s j) =
      fun s => bodyToInertialVec (M.orientation s) (bodyVelocity M s) := by
    funext s
    exact (bodyToInertialVec_inertialToBodyVec (M.orientation s)
      (∂ₜ (fun s j => M.comTrajectory s j) s)).symm
  have htr := deriv_bodyToInertialVec M (bodyVelocity M) t
    (differentiableAt_orientation_of_entries M hU hR ht)
    (differentiableAt_bodyVelocity M hU hR hX ht)
  rw [hfun, htr]
  set m := M.mass
  set R := M.orientation t
  set a := ∂ₜ (bodyVelocity M) t
  set w := M.bodyAngularVelocity t ⨯₃ bodyVelocity M t
  have hm0 : m ≠ 0 := hm.ne'
  have key : ∀ x y : Fin 3 → ℝ, bodyToInertialVec R x = y ↔ x = inertialToBodyVec R y := by
    intro x y
    constructor
    · rintro rfl
      exact (inertialToBodyVec_bodyToInertialVec R x).symm
    · rintro rfl
      exact bodyToInertialVec_inertialToBodyVec R y
  have hsmul : m • bodyToInertialVec R (a + w) = bodyToInertialVec R (m • (a + w)) :=
    (Matrix.mulVec_smul _ m _).symm
  have hadd : ∀ x y, inertialToBodyVec R (x + y) = inertialToBodyVec R x + inertialToBodyVec R y :=
    fun x y => Matrix.mulVec_add _ x y
  have hsm : ∀ (c : ℝ) x, inertialToBodyVec R (c • x) = c • inertialToBodyVec R x :=
    fun c x => Matrix.mulVec_smul _ c x
  -- apply `Rᵀ` and divide by `m`
  rw [hsmul, key, hadd, hsm, inertialToBodyVec_bodyToInertialVec]
  constructor
  · intro h
    have h' : a + w = m⁻¹ • FB + inertialToBodyVec R g := by
      have h2 := congrArg (fun x => m⁻¹ • x) h
      simpa only [smul_add, smul_smul, inv_mul_cancel₀ hm0, one_smul] using h2
    exact eq_sub_of_add_eq h'
  · intro h
    rw [h, sub_add_cancel, smul_add, smul_smul, mul_inv_cancel₀ hm0, one_smul]

/-! ## B. The six-degree-of-freedom body equations -/

/-- The six-degree-of-freedom body equations of the motion `M` at time `t`, with its mass
`m = M.mass`, uniform gravity `g` (inertial components), body force `F_B` and body moment `M_B`
about the centre of mass: the translational equation `v_B' = F_B / m + Rᵀ g - ω_B × v_B` and
Euler's equations `I_B ω_B' + ω_B × (I_B ω_B) = M_B` of the rotating-frame module. Time
derivatives are total (`0` where a curve is not differentiable), and with the convention
`0⁻¹ = 0` the force drops out of the translational equation when `m = 0`; the intended domain is
positive mass and `C²` data, as in `SixDofPlant`. -/
def SixDofBodyEquations (M : RigidBodyMotion 3) (g FB MB : Fin 3 → ℝ) (t : Time) : Prop :=
  ∂ₜ (bodyVelocity M) t = M.mass⁻¹ • FB + inertialToBodyVec (M.orientation t) g -
      M.bodyAngularVelocity t ⨯₃ bodyVelocity M t ∧
    M.inertiaTensorAbout M.centerOfMass *ᵥ ∂ₜ M.bodyAngularVelocity t +
        M.bodyAngularVelocity t ⨯₃
          (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t) = MB

/-- The package with the reused rotation equation: for a motion of positive mass `m = M.mass`
whose orientation and centre-of-mass trajectory are `C²` on an open set `U`, with a body frame
centered at the centre of mass, at every `t ∈ U` the translational law `m X'' = R F_B + m g` and
the rotational law `dL_COM/dt = R M_B` both hold exactly when the six-degree-of-freedom body
equations hold. -/
lemma balanceLaws_iff_sixDofBodyEquations (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (hX : ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) (hc : M.centerOfMass = 0)
    (hm : 0 < M.mass) (g FB MB : Fin 3 → ℝ) {t : Time} (ht : t ∈ U) :
    (M.mass • ∂ₜ (∂ₜ (fun s j => M.comTrajectory s j)) t =
          bodyToInertialVec (M.orientation t) FB + M.mass • g ∧
        ∂ₜ (comAngularMomentum M) t = bodyToInertialVec (M.orientation t) MB) ↔
      SixDofBodyEquations M g FB MB t := by
  rw [newton_iff_deriv_bodyVelocity M hU hR hX hm FB g ht,
    deriv_comAngularMomentum_eq_iff_euler M hU hR hc ht, inertialToBodyVec_bodyToInertialVec]
  rfl

/-! ## C. Coefficient maps with admitted domains -/

/-- Aerodynamic and propulsive coefficient maps, explicit model inputs: the body force and the
body moment about the centre of mass as functions of a state in `S`, defined only on the admitted
domain (a polar validity region, for example), so they are never evaluated outside it. -/
structure ForceMomentMaps (S : Type*) where
  /-- The admitted states. -/
  domain : Set S
  /-- The body force at an admitted state. -/
  force : domain → Fin 3 → ℝ
  /-- The body moment about the centre of mass at an admitted state. -/
  moment : domain → Fin 3 → ℝ

/-- The six-degree-of-freedom plant of the motion `M` at time `t` along the state trajectory `x`,
the state the maps read: the motion has positive mass, its orientation (entry by entry) and its
centre-of-mass trajectory (component by component) are `C²` on an open set of times containing
`t`, the state is admitted, and the body equations hold with the force and the moment the maps give
there. Positive mass keeps the force in the translational equation, and the regularity makes the
derivatives in the body equations genuine. -/
def SixDofPlant {S : Type*} (c : ForceMomentMaps S) (x : Time → S) (M : RigidBodyMotion 3)
    (g : Fin 3 → ℝ) (t : Time) : Prop :=
  0 < M.mass ∧
    (∃ U : Set Time, IsOpen U ∧ t ∈ U ∧
      (∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) ∧
      ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) ∧
    ∃ hx : x t ∈ c.domain, SixDofBodyEquations M g (c.force ⟨x t, hx⟩) (c.moment ⟨x t, hx⟩) t

/-- The coefficient-map domain wrapper: for a body frame centered at the centre of mass, the plant
holds at `t` exactly when the motion has positive mass and `C²` data on an open set of times
containing `t`, the state is admitted there, and both inertial balance laws hold with the force and
the moment the maps give at that state. -/
lemma sixDofPlant_iff {S : Type*} (c : ForceMomentMaps S) (x : Time → S) (M : RigidBodyMotion 3)
    (hc : M.centerOfMass = 0) (g : Fin 3 → ℝ) (t : Time) :
    SixDofPlant c x M g t ↔ 0 < M.mass ∧
      (∃ U : Set Time, IsOpen U ∧ t ∈ U ∧
        (∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) ∧
        ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) ∧
      ∃ hx : x t ∈ c.domain,
        M.mass • ∂ₜ (∂ₜ (fun s j => M.comTrajectory s j)) t =
            bodyToInertialVec (M.orientation t) (c.force ⟨x t, hx⟩) + M.mass • g ∧
          ∂ₜ (comAngularMomentum M) t =
            bodyToInertialVec (M.orientation t) (c.moment ⟨x t, hx⟩) := by
  constructor
  · rintro ⟨hm, ⟨U, hU, ht, hR, hX⟩, hx, hbody⟩
    exact ⟨hm, ⟨U, hU, ht, hR, hX⟩, hx,
      (balanceLaws_iff_sixDofBodyEquations M hU hR hX hc hm g _ _ ht).mpr hbody⟩
  · rintro ⟨hm, ⟨U, hU, ht, hR, hX⟩, hx, hlaws⟩
    exact ⟨hm, ⟨U, hU, ht, hR, hX⟩, hx,
      (balanceLaws_iff_sixDofBodyEquations M hU hR hX hc hm g _ _ ht).mp hlaws⟩

/-! ## D. A controlled longitudinal fixture -/

/-- The lift coefficient of the fixture, `C_L = 2`. -/
def liftCoeff : ℝ := 2

/-- The drag polar of the fixture, `C_D = 1/10 + C_L² / 20`. -/
noncomputable def dragCoeff : ℝ := 1 / 10 + 1 / 20 * liftCoeff ^ 2

/-- The flight speed `V = √((1 + x)² + z²)` at the velocity `(1 + x, z)` of the forward/up
plane. -/
noncomputable def flightSpeed (x z : ℝ) : ℝ := Real.sqrt ((1 + x) ^ 2 + z ^ 2)

/-- The lift at the velocity `(1 + x, z, 0)` with unit air density and reference area: magnitude
`½ V² C_L`, along the velocity turned a quarter turn from forward toward up, written as
`½ V C_L (-z, 1 + x, 0)`: in inertial components, independent of the attitude, and `0` at
`V = 0`. -/
noncomputable def liftForce (x z : ℝ) : Fin 3 → ℝ :=
  (flightSpeed x z * liftCoeff / 2) • ![-z, 1 + x, 0]

/-- The drag at the velocity `(1 + x, z, 0)` with unit air density and reference area: magnitude
`½ V² C_D`, against the velocity, written as `-½ V C_D (1 + x, z, 0)`: in inertial components,
independent of the attitude, and `0` at `V = 0`. -/
noncomputable def dragForce (x z : ℝ) : Fin 3 → ℝ :=
  -(flightSpeed x z * dragCoeff / 2) • ![1 + x, z, 0]

/-- The aerodynamic force, lift plus drag, in inertial components. -/
noncomputable def aeroForce (x z : ℝ) : Fin 3 → ℝ := liftForce x z + dragForce x z

/-- The ideal vector force actuator `A = (-x - x³, 1 - z, 0) - F_aero`, an explicit part of the
model, in inertial components. -/
noncomputable def actuatorForce (x z : ℝ) : Fin 3 → ℝ :=
  ![-x - x ^ 3, 1 - z, 0] - aeroForce x z

/-- The pitch-moment actuator `M = -2 q - sin θ`. -/
noncomputable def pitchMoment (θ q : ℝ) : ℝ := -2 * q - Real.sin θ

/-- The reduced longitudinal field in the state order `(x, z, θ, q)`:
`(-x - x³, -z, q, -2 q - sin θ)`. -/
noncomputable def reducedField (e : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-e 0 - e 0 ^ 3, -e 1, e 3, -2 * e 3 - Real.sin (e 2)]

/-- The admitted actuator box: every state coordinate of `(x, z, θ, q)` at most `1/100` in
absolute value. -/
def actuatorBox : Set (Fin 4 → ℝ) := {e | ∀ i, |e i| ≤ 1 / 100}

/-- The pitch orientation `Rz(θ)`, the rotation by `θ` about the third axis. With the first two axes
spanning the forward/up plane, `θ > 0` turns the body forward axis `Rz(θ) e₁ = (cos θ, sin θ, 0)`
from forward toward up (nose up). -/
noncomputable def pitchOrientation (θ : ℝ) : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨rotZ θ, rotZ_mem_specialOrthogonalGroup θ⟩

/-- The longitudinal force and moment maps on the admitted box, read on the state
`(x, z, θ, q)`: the body force `Rz(θ)ᵀ (F_aero + A)`, the aerodynamic and actuator force in body
components, and the body moment `(0, 0, M)` about the pitch axis. -/
noncomputable def longitudinalMaps : ForceMomentMaps (Fin 4 → ℝ) where
  domain := actuatorBox
  force := fun e => inertialToBodyVec (pitchOrientation (e.1 2))
    (aeroForce (e.1 0) (e.1 1) + actuatorForce (e.1 0) (e.1 1))
  moment := fun e => ![0, 0, pitchMoment (e.1 2) (e.1 3)]

/-- The planar longitudinal motion of the mass distribution `B`: the centre of mass at
`(X₁ t, X₂ t, 0)` in the forward/up plane and the pitch orientation `Rz(θ t)`. -/
noncomputable def planarMotion (B : RigidBody 3) (X₁ X₂ θ : Time → ℝ) : RigidBodyMotion 3 where
  toRigidBody := B
  comTrajectory := fun s => ⟨![X₁ s, X₂ s, 0]⟩
  orientation := fun s => pitchOrientation (θ s)

/-- The longitudinal state of the planar motion at time `t`: `x = X₁' - 1`, `z = X₂'`, the pitch
angle `θ` and the pitch rate `q = θ'`. Time derivatives are total, taken as `0` at a time where the
function is not differentiable. -/
noncomputable def planarState (X₁ X₂ θ : Time → ℝ) (t : Time) : Fin 4 → ℝ :=
  ![∂ₜ X₁ t - 1, ∂ₜ X₂ t, θ t, ∂ₜ θ t]

/-- The drag polar gives `C_D = 3/10` at `C_L = 2`. -/
lemma dragCoeff_eq : dragCoeff = 3 / 10 := by
  unfold dragCoeff liftCoeff
  norm_num

/-- **Lift and drag.** At the velocity `v = (1 + x, z, 0)` the lift is perpendicular to `v`, has
squared magnitude `(V²)²` and points to the up side of `v`; the drag is `-(3 V / 20) v`, against
`v`, with squared magnitude `(3 V² / 20)²`. -/
lemma liftForce_dragForce_spec (x z : ℝ) :
    liftForce x z ⬝ᵥ ![1 + x, z, 0] = 0 ∧
      liftForce x z ⬝ᵥ liftForce x z = (flightSpeed x z ^ 2) ^ 2 ∧
      0 ≤ liftForce x z ⬝ᵥ ![-z, 1 + x, 0] ∧
      dragForce x z = -(3 / 20 * flightSpeed x z) • ![1 + x, z, 0] ∧
      dragForce x z ⬝ᵥ dragForce x z = (3 / 20 * flightSpeed x z ^ 2) ^ 2 := by
  have hV2 : flightSpeed x z ^ 2 = (1 + x) ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
  have hV0 : 0 ≤ flightSpeed x z := Real.sqrt_nonneg _
  have hL : liftForce x z = flightSpeed x z • ![-z, 1 + x, 0] := by
    unfold liftForce liftCoeff
    congr 1
    ring
  have hDr : dragForce x z = -(3 / 20 * flightSpeed x z) • ![1 + x, z, 0] := by
    unfold dragForce
    rw [dragCoeff_eq]
    congr 1
    ring
  refine ⟨?_, ?_, ?_, hDr, ?_⟩
  · rw [hL]
    simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  · rw [hL]
    simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (-(flightSpeed x z ^ 2)) * hV2
  · rw [hL]
    simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have : 0 ≤ flightSpeed x z * ((1 + x) ^ 2 + z ^ 2) := by positivity
    nlinarith
  · rw [hDr]
    simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (-(9 / 400 * flightSpeed x z ^ 2)) * hV2

/-- **The force balance.** The aerodynamic force, the actuator force and the weight
`(0, -1, 0)` add up to `(-x - x³, -z, 0)`. -/
lemma aeroForce_add_actuatorForce_add_weight (x z : ℝ) :
    aeroForce x z + actuatorForce x z + ![0, -1, 0] = ![-x - x ^ 3, -z, 0] := by
  ext i
  fin_cases i <;> simp [actuatorForce]
  ring

/-- The time derivative of a vector-valued curve differentiable at `t` is taken component by
component. -/
private lemma deriv_apply_of_differentiableAt {n : ℕ} {f : Time → Fin n → ℝ} {t : Time}
    (hf : DifferentiableAt ℝ f t) (i : Fin n) : ∂ₜ (fun s => f s i) t = ∂ₜ f t i := by
  have h : HasFDerivAt (fun s => f s i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp (fderiv ℝ f t)) t :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt.comp t
      hf.hasFDerivAt
  rw [Time.deriv_eq, h.fderiv, Time.deriv_eq]
  rfl

/-- The time derivative of a curve `s ↦ (a s, b s, c s)` with components differentiable at `t`. -/
private lemma deriv_vec3 {a b c : Time → ℝ} {t : Time} (ha : DifferentiableAt ℝ a t)
    (hb : DifferentiableAt ℝ b t) (hc : DifferentiableAt ℝ c t) :
    ∂ₜ (fun s => ![a s, b s, c s]) t = ![∂ₜ a t, ∂ₜ b t, ∂ₜ c t] := by
  have hd : DifferentiableAt ℝ (fun s => ![a s, b s, c s]) t := by
    refine differentiableAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hb
    · simpa using hc
  funext i
  rw [← deriv_apply_of_differentiableAt hd i]
  fin_cases i
  · rfl
  · rfl
  · rfl

/-- The chain rule for `cos ∘ θ` and `sin ∘ θ` with the time derivative. -/
private lemma deriv_cos_sin_comp {θ : Time → ℝ} {t : Time} (hθ : DifferentiableAt ℝ θ t) :
    ∂ₜ (fun s => Real.cos (θ s)) t = ∂ₜ θ t * -Real.sin (θ t) ∧
      ∂ₜ (fun s => Real.sin (θ s)) t = ∂ₜ θ t * Real.cos (θ t) ∧
      ∂ₜ (fun s => -Real.sin (θ s)) t = ∂ₜ θ t * -Real.cos (θ t) := by
  have h := Time.hasDerivAt_mk_of_differentiableAt hθ
  refine ⟨?_, ?_, ?_⟩
  · exact Time.deriv_eq_of_hasDerivAt (((Real.hasDerivAt_cos _).comp t.val h).congr_deriv
      (by ring))
  · exact Time.deriv_eq_of_hasDerivAt (((Real.hasDerivAt_sin _).comp t.val h).congr_deriv
      (by ring))
  · exact Time.deriv_eq_of_hasDerivAt (((Real.hasDerivAt_sin _).comp t.val h).neg.congr_deriv
      (by ring))

/-- The pitch orientation along a curve differentiable at `t` is differentiable at `t`. -/
private lemma differentiableAt_rotZ_comp {θ : Time → ℝ} {t : Time}
    (hθ : DifferentiableAt ℝ θ t) : DifferentiableAt ℝ (fun s => rotZ (θ s)) t := by
  have hc : DifferentiableAt ℝ (fun s => Real.cos (θ s)) t := Real.differentiableAt_cos.comp t hθ
  have hs : DifferentiableAt ℝ (fun s => Real.sin (θ s)) t := Real.differentiableAt_sin.comp t hθ
  have h : DifferentiableAt ℝ (fun s => Matrix.of.symm (rotZ (θ s))) t := by
    refine differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp only [rotZ] <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
        Matrix.cons_val_fin_one, Equiv.symm_apply_apply] <;>
      first
        | exact hc
        | exact hs
        | exact hs.neg
        | exact differentiableAt_const _
  exact h

/-- The pitch orientation has the derivative `θ' dRz/dθ`. -/
private lemma deriv_rotZ_comp {θ : Time → ℝ} {t : Time} (hθ : DifferentiableAt ℝ θ t) :
    ∂ₜ (fun s => rotZ (θ s)) t = ∂ₜ θ t •
      !![-Real.sin (θ t), -Real.cos (θ t), 0; Real.cos (θ t), -Real.sin (θ t), 0; 0, 0, 0] := by
  obtain ⟨dc, ds, dns⟩ := deriv_cos_sin_comp hθ
  ext i j
  refine (Time.deriv_matrix_apply _ t (differentiableAt_rotZ_comp hθ) i j).symm.trans ?_
  fin_cases i <;> fin_cases j <;> simp only [rotZ] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.smul_apply, smul_eq_mul] <;>
    first
      | exact dc
      | exact ds
      | exact dns
      | simp

/-- The body angular velocity of the planar motion is `(0, 0, θ')`. -/
private lemma planarMotion_bodyAngularVelocity (B : RigidBody 3) (X₁ X₂ : Time → ℝ)
    {θ : Time → ℝ} {t : Time} (hθ : DifferentiableAt ℝ θ t) :
    (planarMotion B X₁ X₂ θ).bodyAngularVelocity t = ![0, 0, ∂ₜ θ t] := by
  have h : (planarMotion B X₁ X₂ θ).bodyAngularVelocity t = Matrix.crossProductVee
      ((((planarMotion B X₁ X₂ θ).orientation t : Matrix (Fin 3) (Fin 3) ℝ))ᵀ *
        ∂ₜ (fun s => ((planarMotion B X₁ X₂ θ).orientation s).1) t) := rfl
  have hR : (((planarMotion B X₁ X₂ θ).orientation t : Matrix (Fin 3) (Fin 3) ℝ)) =
      rotZ (θ t) := rfl
  have hRf : (fun s => ((planarMotion B X₁ X₂ θ).orientation s).1) = fun s => rotZ (θ s) := rfl
  rw [h, hRf, deriv_rotZ_comp hθ, hR]
  have hcs := Real.cos_sq_add_sin_sq (θ t)
  ext i
  fin_cases i
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ∂ₜ θ t * hcs

/-- **Restriction of the plant to the plane.** For a mass distribution of mass `1` with centre of
mass `0` and inertia `diag(I_xx, I_yy, 1)` about it (pitch inertia `1` about the principal third
axis), and `C²` coordinates `X₁`, `X₂` and pitch angle `θ`, the six-degree-of-freedom plant of
the planar motion with the longitudinal maps and gravity `(0, -1, 0)` holds at `t` exactly when
the state is in the actuator box and its rate is the reduced field:
`x' = -x - x³`, `z' = -z`, `θ' = q`, `q' = -2 q - sin θ`. -/
lemma planar_sixDofPlant_iff (B : RigidBody 3) (hm : B.mass = 1) (hc : B.centerOfMass = 0)
    {Ixx Iyy : ℝ} (hI : B.inertiaTensorAbout B.centerOfMass = Matrix.diagonal ![Ixx, Iyy, 1])
    {X₁ X₂ θ : Time → ℝ} (hX₁ : ContDiff ℝ 2 X₁) (hX₂ : ContDiff ℝ 2 X₂) (hθ : ContDiff ℝ 2 θ)
    (t : Time) :
    SixDofPlant longitudinalMaps (planarState X₁ X₂ θ) (planarMotion B X₁ X₂ θ) ![0, -1, 0] t ↔
      planarState X₁ X₂ θ t ∈ actuatorBox ∧
        (fun i => ∂ₜ (fun s => planarState X₁ X₂ θ s i) t) =
          reducedField (planarState X₁ X₂ θ t) := by
  have hd1 : Differentiable ℝ X₁ := hX₁.differentiable (by norm_num)
  have hd2 : Differentiable ℝ X₂ := hX₂.differentiable (by norm_num)
  have hdθ : Differentiable ℝ θ := hθ.differentiable (by norm_num)
  have hdd1 : Differentiable ℝ (∂ₜ X₁) := deriv_differentiable_of_contDiff_two X₁ hX₁
  have hdd2 : Differentiable ℝ (∂ₜ X₂) := deriv_differentiable_of_contDiff_two X₂ hX₂
  have hddθ : Differentiable ℝ (∂ₜ θ) := deriv_differentiable_of_contDiff_two θ hθ
  have hR : ∀ i j, ContDiffOn ℝ 2 (fun s => ((planarMotion B X₁ X₂ θ).orientation s).1 i j)
      Set.univ := by
    intro i j
    have hc := (Real.contDiff_cos.comp hθ).contDiffOn (s := Set.univ)
    have hs := (Real.contDiff_sin.comp hθ).contDiffOn (s := Set.univ)
    fin_cases i <;> fin_cases j <;> simp only [planarMotion, pitchOrientation, rotZ] <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
        Matrix.cons_val_fin_one] <;>
      first
        | exact hc
        | exact hs
        | exact hs.neg
        | exact contDiffOn_const
  have hX : ∀ j, ContDiffOn ℝ 2 (fun s => (planarMotion B X₁ X₂ θ).comTrajectory s j)
      Set.univ := by
    intro j
    fin_cases j
    · exact hX₁.contDiffOn
    · exact hX₂.contDiffOn
    · exact contDiffOn_const
  have hc' : (planarMotion B X₁ X₂ θ).centerOfMass = 0 := hc
  have hm' : (planarMotion B X₁ X₂ θ).mass = 1 := hm
  have hI' : (planarMotion B X₁ X₂ θ).inertiaTensorAbout (planarMotion B X₁ X₂ θ).centerOfMass =
      Matrix.diagonal ![Ixx, Iyy, 1] := hI
  have hvel : ∂ₜ (fun s j => (planarMotion B X₁ X₂ θ).comTrajectory s j) =
      fun s => ![∂ₜ X₁ s, ∂ₜ X₂ s, 0] := by
    funext s
    have h := deriv_vec3 (hd1 s) (hd2 s) (differentiableAt_const (0 : ℝ))
    rw [Time.deriv_const] at h
    exact h
  have hacc : ∂ₜ (∂ₜ (fun s j => (planarMotion B X₁ X₂ θ).comTrajectory s j)) t =
      ![∂ₜ (∂ₜ X₁) t, ∂ₜ (∂ₜ X₂) t, 0] := by
    rw [hvel]
    have h := deriv_vec3 (hdd1 t) (hdd2 t) (differentiableAt_const (0 : ℝ))
    rw [Time.deriv_const] at h
    exact h
  have hω : ∀ s, (planarMotion B X₁ X₂ θ).bodyAngularVelocity s = ![0, 0, ∂ₜ θ s] :=
    fun s => planarMotion_bodyAngularVelocity B X₁ X₂ (hdθ s)
  have hω' : ∂ₜ (planarMotion B X₁ X₂ θ).bodyAngularVelocity t = ![0, 0, ∂ₜ (∂ₜ θ) t] := by
    rw [show (planarMotion B X₁ X₂ θ).bodyAngularVelocity = fun s => ![0, 0, ∂ₜ θ s] from
      funext hω]
    have h := deriv_vec3 (differentiableAt_const (0 : ℝ)) (differentiableAt_const (0 : ℝ))
      (hddθ t) (t := t)
    rw [Time.deriv_const] at h
    exact h
  have hstate : (fun i => ∂ₜ (fun s => planarState X₁ X₂ θ s i) t) =
      ![∂ₜ (∂ₜ X₁) t, ∂ₜ (∂ₜ X₂) t, ∂ₜ θ t, ∂ₜ (∂ₜ θ) t] := by
    funext i
    fin_cases i
    · change ∂ₜ (fun s => ∂ₜ X₁ s - 1) t = ∂ₜ (∂ₜ X₁) t
      exact Time.deriv_eq_of_hasDerivAt
        ((Time.hasDerivAt_mk_of_differentiableAt (hdd1 t)).sub_const 1)
    · rfl
    · rfl
    · rfl
  have hF : ∀ hx : planarState X₁ X₂ θ t ∈ longitudinalMaps.domain,
      bodyToInertialVec ((planarMotion B X₁ X₂ θ).orientation t)
          (longitudinalMaps.force ⟨planarState X₁ X₂ θ t, hx⟩) =
        ![-(∂ₜ X₁ t - 1) - (∂ₜ X₁ t - 1) ^ 3, 1 - ∂ₜ X₂ t, 0] := by
    intro hx
    change bodyToInertialVec (pitchOrientation (θ t)) (inertialToBodyVec (pitchOrientation (θ t))
      (aeroForce (∂ₜ X₁ t - 1) (∂ₜ X₂ t) + actuatorForce (∂ₜ X₁ t - 1) (∂ₜ X₂ t))) = _
    rw [bodyToInertialVec_inertialToBodyVec]
    unfold actuatorForce
    abel
  have hMB : ∀ hx : planarState X₁ X₂ θ t ∈ longitudinalMaps.domain,
      longitudinalMaps.moment ⟨planarState X₁ X₂ θ t, hx⟩ =
        ![0, 0, pitchMoment (θ t) (∂ₜ θ t)] := fun _ => rfl
  have heuler : ∀ τ : Fin 3 → ℝ,
      ∂ₜ (comAngularMomentum (planarMotion B X₁ X₂ θ)) t =
          bodyToInertialVec ((planarMotion B X₁ X₂ θ).orientation t) τ ↔
        ![0, 0, ∂ₜ (∂ₜ θ) t] = τ := by
    intro τ
    rw [deriv_comAngularMomentum_eq_iff_euler _ isOpen_univ hR hc' (Set.mem_univ t),
      inertialToBodyVec_bodyToInertialVec, hI', hω t, hω']
    have hlhs : Matrix.diagonal ![Ixx, Iyy, 1] *ᵥ ![0, 0, ∂ₜ (∂ₜ θ) t] +
        ![0, 0, ∂ₜ θ t] ⨯₃ (Matrix.diagonal ![Ixx, Iyy, 1] *ᵥ ![0, 0, ∂ₜ θ t]) =
          ![0, 0, ∂ₜ (∂ₜ θ) t] := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec_diagonal, cross_apply]
    rw [hlhs]
  rw [sixDofPlant_iff longitudinalMaps _ (planarMotion B X₁ X₂ θ) hc' _ t, hstate]
  constructor
  · rintro ⟨-, -, hx, hlaw, hang⟩
    refine ⟨hx, ?_⟩
    rw [hF hx, hm', one_smul, one_smul, hacc] at hlaw
    rw [hMB hx, heuler] at hang
    have h0 := congrFun hlaw 0
    have h1 := congrFun hlaw 1
    have h3 := congrFun hang 2
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, neg_sub,
      Pi.add_apply, add_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h3
    unfold pitchMoment at h3
    funext i
    fin_cases i
    · simp [reducedField, planarState]
      linarith
    · simp [reducedField, planarState]
      linarith
    · simp [reducedField, planarState]
    · simp [reducedField, planarState]
      linarith
  · rintro ⟨hx, hred⟩
    have h0 := congrFun hred 0
    have h1 := congrFun hred 1
    have h3 := congrFun hred 3
    simp [reducedField, planarState] at h0 h1 h3
    refine ⟨by rw [hm']; norm_num, ⟨Set.univ, isOpen_univ, Set.mem_univ t, hR, hX⟩, hx, ?_, ?_⟩
    · rw [hF hx, hm', one_smul, one_smul, hacc]
      ext i
      fin_cases i
      · simp
        linarith
      · simp
        linarith
      · simp
    · rw [hMB hx, heuler]
      ext i
      fin_cases i
      · simp
      · simp
      · simp [pitchMoment]
        linarith

/-- **The trim is a relative equilibrium.** For a mass distribution as in
`planar_sixDofPlant_iff`, the planar motion with position `p(t) = (p₁ + t, p₂)` and zero pitch has
zero longitudinal state and is a plant solution at every time, while its centre of mass moves
with the nonzero rate `(1, 0, 0)`: not a stationary world-position state. -/
lemma trim_relative_equilibrium (B : RigidBody 3) (hm : B.mass = 1) (hc : B.centerOfMass = 0)
    {Ixx Iyy : ℝ} (hI : B.inertiaTensorAbout B.centerOfMass = Matrix.diagonal ![Ixx, Iyy, 1])
    (p₁ p₂ : ℝ) (t : Time) :
    planarState (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0) t = 0 ∧
      SixDofPlant longitudinalMaps (planarState (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0))
        (planarMotion B (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0)) ![0, -1, 0] t ∧
      ∂ₜ (fun s j => (planarMotion B (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0)).comTrajectory
        s j) t = ![1, 0, 0] := by
  have hX₁ : ContDiff ℝ 2 (fun s : Time => p₁ + s.val) := contDiff_const.add Time.val_contDiff
  have hX₂ : ContDiff ℝ 2 (fun _ : Time => p₂) := contDiff_const
  have hθ : ContDiff ℝ 2 (fun _ : Time => (0 : ℝ)) := contDiff_const
  have hrate : ∀ s : Time, ∂ₜ (fun s : Time => p₁ + s.val) s = 1 := fun s =>
    Time.deriv_eq_of_hasDerivAt (by simpa using (hasDerivAt_id s.val).const_add p₁)
  have hstate : ∀ s, planarState (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0) s = 0 := by
    intro s
    ext i
    fin_cases i <;> simp [planarState, hrate]
  refine ⟨hstate t, ?_, ?_⟩
  · rw [planar_sixDofPlant_iff B hm hc hI hX₁ hX₂ hθ t]
    refine ⟨by rw [hstate t]; intro i; simp, ?_⟩
    rw [hstate t]
    funext i
    have h : (fun s => planarState (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0) s i) =
        fun _ => 0 := by
      funext s
      rw [hstate s]
      rfl
    rw [h, Time.deriv_const]
    fin_cases i <;> simp [reducedField]
  · have hd : DifferentiableAt ℝ (fun s : Time => p₁ + s.val) t :=
      (hX₁.differentiable (by norm_num)) t
    have h := deriv_vec3 hd (differentiableAt_const p₂) (differentiableAt_const (0 : ℝ))
    rw [hrate, Time.deriv_const, Time.deriv_const] at h
    exact h

/-- **Actuator domain.** On the box: `V ≥ 99/100`, `1/10 < A_x < 1/5`, `|A_z| < 1/20` and
`|M| ≤ 3/100`. -/
lemma actuatorBox_bounds {e : Fin 4 → ℝ} (he : e ∈ actuatorBox) :
    99 / 100 ≤ flightSpeed (e 0) (e 1) ∧ 1 / 10 < actuatorForce (e 0) (e 1) 0 ∧
      actuatorForce (e 0) (e 1) 0 < 1 / 5 ∧ |actuatorForce (e 0) (e 1) 1| < 1 / 20 ∧
      |pitchMoment (e 2) (e 3)| ≤ 3 / 100 := by
  have hx := he 0
  have hz := he 1
  have hθ := he 2
  have hq := he 3
  set x := e 0
  set z := e 1
  have hV2 : flightSpeed x z ^ 2 = (1 + x) ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
  have hV0 : 0 ≤ flightSpeed x z := Real.sqrt_nonneg _
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  have hVlo : 99 / 100 ≤ flightSpeed x z := by nlinarith [sq_nonneg z]
  have hVhi : flightSpeed x z ≤ 10101 / 10000 := by nlinarith [sq_nonneg z]
  have hx3 : |x ^ 3| ≤ 1 / 1000000 := by
    rw [abs_pow]
    calc |x| ^ 3 ≤ (1 / 100) ^ 3 := pow_le_pow_left₀ (abs_nonneg x) hx 3
      _ = 1 / 1000000 := by norm_num
  obtain ⟨hx31, hx32⟩ := abs_le.mp hx3
  have hD : dragCoeff = 3 / 10 := dragCoeff_eq
  have hAx : actuatorForce x z 0 =
      -x - x ^ 3 + flightSpeed x z * (z + 3 / 20 * (1 + x)) := by
    simp [actuatorForce, aeroForce, liftForce, dragForce, hD, liftCoeff]
    ring
  have hAz : actuatorForce x z 1 =
      1 - z - flightSpeed x z * (1 + x) + 3 / 20 * (flightSpeed x z * z) := by
    simp [actuatorForce, aeroForce, liftForce, dragForce, hD, liftCoeff]
    ring
  have hw1 : 1385 / 10000 ≤ z + 3 / 20 * (1 + x) := by linarith
  have hw2 : z + 3 / 20 * (1 + x) ≤ 1615 / 10000 := by linarith
  have hVw1 : 99 / 100 * (1385 / 10000) ≤ flightSpeed x z * (z + 3 / 20 * (1 + x)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hVlo) (by linarith : (0 : ℝ) ≤ z + 3 / 20 * (1 + x))]
  have hVw2 : flightSpeed x z * (z + 3 / 20 * (1 + x)) ≤ 10101 / 10000 * (1615 / 10000) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hVhi) (by linarith : (0 : ℝ) ≤ z + 3 / 20 * (1 + x))]
  have hVx1 : 99 / 100 * (99 / 100) ≤ flightSpeed x z * (1 + x) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hVlo) (by linarith : (0 : ℝ) ≤ 1 + x)]
  have hVx2 : flightSpeed x z * (1 + x) ≤ 10101 / 10000 * (101 / 100) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hVhi) (by linarith : (0 : ℝ) ≤ 1 + x)]
  have hVz : |flightSpeed x z * z| ≤ 10101 / 10000 * (1 / 100) := by
    rw [abs_mul, abs_of_nonneg hV0]
    exact mul_le_mul hVhi hz (abs_nonneg z) (by norm_num)
  obtain ⟨hVz1, hVz2⟩ := abs_le.mp hVz
  refine ⟨hVlo, ?_, ?_, ?_, ?_⟩
  · rw [hAx]
    linarith
  · rw [hAx]
    linarith
  · rw [hAz, abs_lt]
    constructor <;> linarith
  · unfold pitchMoment
    have hs : |Real.sin (e 2)| ≤ |e 2| := Real.abs_sin_le_abs
    calc |-2 * e 3 - Real.sin (e 2)| ≤ |-2 * e 3| + |Real.sin (e 2)| := abs_sub _ _
      _ ≤ 2 * (1 / 100) + 1 / 100 := by
        rw [abs_mul]
        norm_num
        linarith
      _ = 3 / 100 := by norm_num

/-- **No evaluation outside the box.** A state of zero speed is outside the box, and at a state
outside the box the plant fails, whatever the motion and the gravity. -/
lemma longitudinalMaps_rejects {x : Time → Fin 4 → ℝ} (M : RigidBodyMotion 3) (g : Fin 3 → ℝ)
    (t : Time) :
    (flightSpeed (x t 0) (x t 1) = 0 → x t ∉ actuatorBox) ∧
      (x t ∉ actuatorBox → ¬ SixDofPlant longitudinalMaps x M g t) := by
  refine ⟨fun h0 hx => ?_, fun hx hplant => ?_⟩
  · have := (actuatorBox_bounds hx).1
    rw [h0] at this
    norm_num at this
  · obtain ⟨-, -, hx', -⟩ := hplant
    exact hx hx'

/-! ## E. Linearization about the trim -/

/-- The Jacobian of the reduced longitudinal field at the trim, in the state order
`(x, z, θ, q)`: `diag(-1, -1) ⊕ [[0, 1], [-1, -2]]`. -/
def longitudinalJacobian : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 0, 1; 0, 0, -1, -2]

/-- The nonlinear remainder of the reduced longitudinal field about the trim, in the state order
`(x, z, θ, q)`: `(-x³, 0, 0, θ - sin θ)`. -/
noncomputable def longitudinalRemainder (e : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-e 0 ^ 3, 0, 0, e 2 - Real.sin (e 2)]

/-- The Jacobian is the direct sum of the translational block `diag(-1, -1)` on `(x, z)` and the
pitch block `[[0, 1], [-1, -2]]` on `(θ, q)`. -/
lemma longitudinalJacobian_eq_fromBlocks :
    longitudinalJacobian = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (Matrix.diagonal ![-1, -1]) 0 0 !![0, 1; -1, -2]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The derivative of the component `-x - x³` of the reduced field at `y`: `(-1 - 3 x²) dx`. -/
private lemma hasFDerivAt_reducedField_comp0 (y : Fin 4 → ℝ) :
    HasFDerivAt (fun e : Fin 4 → ℝ => reducedField e 0)
      ((-1 - 3 * y 0 ^ 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0) y := by
  have h := ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).fun_neg).fun_sub
    ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).pow 3)
  have hf : (fun e : Fin 4 → ℝ => reducedField e 0) = fun e => -e 0 - e 0 ^ 3 := by
    funext e
    simp [reducedField]
  rw [hf]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp
  ring

/-- The derivative of the component `-z` of the reduced field: `-dz`. -/
private lemma hasFDerivAt_reducedField_comp1 (y : Fin 4 → ℝ) :
    HasFDerivAt (fun e : Fin 4 → ℝ => reducedField e 1)
      (-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1) y := by
  have hf : (fun e : Fin 4 → ℝ => reducedField e 1) = fun e => -e 1 := by
    funext e
    simp [reducedField]
  rw [hf]
  exact (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y).neg

/-- The derivative of the component `q` of the reduced field: `dq`. -/
private lemma hasFDerivAt_reducedField_comp2 (y : Fin 4 → ℝ) :
    HasFDerivAt (fun e : Fin 4 → ℝ => reducedField e 2)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3) y := by
  have hf : (fun e : Fin 4 → ℝ => reducedField e 2) = fun e => e 3 := by
    funext e
    simp [reducedField]
  rw [hf]
  exact hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y

/-- The derivative of the component `-2 q - sin θ` of the reduced field at `y`:
`-2 dq - cos θ dθ`. -/
private lemma hasFDerivAt_reducedField_comp3 (y : Fin 4 → ℝ) :
    HasFDerivAt (fun e : Fin 4 → ℝ => reducedField e 3)
      ((-2 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3 -
        Real.cos (y 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2) y := by
  have hs' := (Real.hasDerivAt_sin (y 2)).comp_hasFDerivAt y
    (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y)
  have hs : HasFDerivAt (fun e : Fin 4 → ℝ => Real.sin (e 2))
      (Real.cos (y 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2) y := hs'
  have h := ((hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y).const_mul (-2 : ℝ)).fun_sub hs
  have hf : (fun e : Fin 4 → ℝ => reducedField e 3) = fun e => -2 * e 3 - Real.sin (e 2) := by
    funext e
    simp [reducedField]
  rw [hf]
  exact h

/-- **The Jacobian at the trim.** The reduced field is differentiable at the zero state, with
derivative `δ ↦ longitudinalJacobian *ᵥ δ`. -/
lemma hasFDerivAt_reducedField_zero :
    HasFDerivAt reducedField
      (LinearMap.toContinuousLinearMap (Matrix.toLin' longitudinalJacobian)) 0 := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · refine (hasFDerivAt_reducedField_comp0 0).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [longitudinalJacobian, dotProduct, Fin.sum_univ_four]
  · refine (hasFDerivAt_reducedField_comp1 0).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [longitudinalJacobian, dotProduct, Fin.sum_univ_four]
  · refine (hasFDerivAt_reducedField_comp2 0).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [longitudinalJacobian, dotProduct, Fin.sum_univ_four]
  · refine (hasFDerivAt_reducedField_comp3 0).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [longitudinalJacobian, dotProduct, Fin.sum_univ_four]
    ring

/-- **Linear part and remainder.** At every state the reduced field is the Jacobian part plus the
nonlinear remainder: `f e = A *ᵥ e + (-x³, 0, 0, θ - sin θ)`. -/
lemma reducedField_eq_mulVec_add_remainder (e : Fin 4 → ℝ) :
    reducedField e = longitudinalJacobian *ᵥ e + longitudinalRemainder e := by
  ext i
  fin_cases i <;>
    simp [reducedField, longitudinalRemainder, longitudinalJacobian, dotProduct,
      Fin.sum_univ_four] <;>
    ring

/-- **The first-order remainder at the trim.** For every deviation `δ`, the remainder
`f (0 + δ) - f 0 - Df(0) δ` of the reused uncertainty-propagation API, for the reduced field at the
trim, is `longitudinalRemainder δ`. -/
lemma jacobianRemainder_reducedField (δ : Fin 4 → ℝ) :
    Statistics.UncertaintyPropagation.jacobianRemainder reducedField 0 δ =
      longitudinalRemainder δ := by
  have hD : fderiv ℝ reducedField 0 δ = longitudinalJacobian *ᵥ δ := by
    rw [hasFDerivAt_reducedField_zero.fderiv]
    simp [Matrix.toLin'_apply]
  have h0 : reducedField 0 = 0 := by
    ext i
    fin_cases i <;> simp [reducedField]
  rw [Statistics.UncertaintyPropagation.jacobianRemainder, zero_add, hD, h0, sub_zero,
    reducedField_eq_mulVec_add_remainder δ, add_sub_cancel_left]

/-- **Remainder bounds, sup norm.** For `0 < r ≤ 1/100` and a deviation `δ` with every coordinate
at most `r` in absolute value, `δ` lies in the actuator box, and with `‖δ‖` the sup norm:
`|-x³| ≤ r ‖δ‖²`, the middle components vanish, and `|θ - sin θ| ≤ (r / 6) ‖δ‖²` by the cubic
sine bound. -/
lemma longitudinalRemainder_bounds {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 100) {δ : Fin 4 → ℝ}
    (hδ : ∀ i, |δ i| ≤ r) :
    δ ∈ actuatorBox ∧ |longitudinalRemainder δ 0| ≤ r * ‖δ‖ ^ 2 ∧
      longitudinalRemainder δ 1 = 0 ∧ longitudinalRemainder δ 2 = 0 ∧
      |longitudinalRemainder δ 3| ≤ r / 6 * ‖δ‖ ^ 2 := by
  have hn : ∀ j, |δ j| ≤ ‖δ‖ := fun j => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm δ j
  refine ⟨fun i => (hδ i).trans hr, ?_, by simp [longitudinalRemainder],
    by simp [longitudinalRemainder], ?_⟩
  · simp only [longitudinalRemainder, Matrix.cons_val_zero]
    rw [abs_neg, abs_pow]
    calc |δ 0| ^ 3 = |δ 0| * |δ 0| ^ 2 := by ring
      _ ≤ r * ‖δ‖ ^ 2 :=
        mul_le_mul (hδ 0) (pow_le_pow_left₀ (abs_nonneg _) (hn 0) 2) (by positivity) hr0.le
  · simp only [longitudinalRemainder]
    simp only [Matrix.cons_val]
    calc |δ 2 - Real.sin (δ 2)| ≤ |δ 2| ^ 3 / 6 := Real.abs_sub_sin_le _
      _ = |δ 2| * |δ 2| ^ 2 / 6 := by ring
      _ ≤ r * ‖δ‖ ^ 2 / 6 := by
        gcongr
        · exact hδ 2
        · exact hn 2
      _ = r / 6 * ‖δ‖ ^ 2 := by ring

/-- The reduced field is `C²`: polynomial in `x`, `z`, `q` and trigonometric in `θ`. -/
lemma contDiff_reducedField : ContDiff ℝ 2 reducedField := by
  have hc : ∀ j : Fin 4, ContDiff ℝ 2 fun e : Fin 4 → ℝ => e j := fun j =>
    contDiff_apply ℝ (fun _ : Fin 4 => ℝ) j
  rw [contDiff_pi]
  intro i
  fin_cases i
  · have h : ContDiff ℝ 2 fun e : Fin 4 → ℝ => -e 0 - e 0 ^ 3 := (hc 0).neg.sub ((hc 0).pow 3)
    simpa [reducedField] using h
  · have h : ContDiff ℝ 2 fun e : Fin 4 → ℝ => -e 1 := (hc 1).neg
    simpa [reducedField] using h
  · simpa [reducedField] using hc 3
  · have h : ContDiff ℝ 2 fun e : Fin 4 → ℝ => -2 * e 3 - Real.sin (e 2) :=
      (contDiff_const.mul (hc 3)).sub (Real.contDiff_sin.comp (hc 2))
    simpa [reducedField] using h

/-- **The actual second derivatives** of the components of the reduced field, as bilinear forms
in the directions `h` and `k`: `-6 x h₀ k₀` for `-x - x³`, `0` for `-z` and `q`, and
`sin θ h₂ k₂` for `-2 q - sin θ`. -/
lemma fderiv_fderiv_reducedField_apply (y h k : Fin 4 → ℝ) :
    fderiv ℝ (fderiv ℝ fun e => reducedField e 0) y h k = -6 * y 0 * h 0 * k 0 ∧
      fderiv ℝ (fderiv ℝ fun e => reducedField e 1) y h k = 0 ∧
      fderiv ℝ (fderiv ℝ fun e => reducedField e 2) y h k = 0 ∧
      fderiv ℝ (fderiv ℝ fun e => reducedField e 3) y h k = Real.sin (y 2) * h 2 * k 2 := by
  have d0 : fderiv ℝ (fun e : Fin 4 → ℝ => reducedField e 0) = fun y =>
      (-1 - 3 * y 0 ^ 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0 :=
    funext fun y => (hasFDerivAt_reducedField_comp0 y).fderiv
  have d1 : fderiv ℝ (fun e : Fin 4 → ℝ => reducedField e 1) = fun _ =>
      -ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1 :=
    funext fun y => (hasFDerivAt_reducedField_comp1 y).fderiv
  have d2 : fderiv ℝ (fun e : Fin 4 → ℝ => reducedField e 2) = fun _ =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3 :=
    funext fun y => (hasFDerivAt_reducedField_comp2 y).fderiv
  have d3 : fderiv ℝ (fun e : Fin 4 → ℝ => reducedField e 3) = fun y =>
      (-2 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3 -
        Real.cos (y 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2 :=
    funext fun y => (hasFDerivAt_reducedField_comp3 y).fderiv
  have hc0 : HasFDerivAt (fun y : Fin 4 → ℝ => -1 - 3 * y 0 ^ 2)
      (0 - (3 : ℝ) • ((2 • y 0 ^ (2 - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0)) y :=
    (hasFDerivAt_const (-1 : ℝ) y).fun_sub
      (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).pow 2).const_mul (3 : ℝ))
  have H0 : HasFDerivAt (fun y : Fin 4 → ℝ => (-1 - 3 * y 0 ^ 2) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0)
      ((0 - (3 : ℝ) • ((2 • y 0 ^ (2 - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0)).smulRight
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0)) y :=
    hc0.smul_const (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0)
  have hcos' := (Real.hasDerivAt_cos (y 2)).comp_hasFDerivAt y
    (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y)
  have hcos : HasFDerivAt (fun y : Fin 4 → ℝ => Real.cos (y 2))
      ((-Real.sin (y 2)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2) y :=
    hcos'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [d0, H0.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, sub_apply, zero_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one]
    ring
  · rw [d1, (hasFDerivAt_const _ y).fderiv]
    rfl
  · rw [d2, (hasFDerivAt_const _ y).fderiv]
    rfl
  · have H3 : HasFDerivAt (fun y : Fin 4 → ℝ =>
        (-2 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3 -
          Real.cos (y 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2)
        (0 - ((-Real.sin (y 2)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ)
          2).smulRight (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2)) y :=
      (hasFDerivAt_const _ y).fun_sub
        (hcos.smul_const (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2))
    rw [d3, H3.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, sub_apply, zero_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring

/-- **Hessian bounds on the box**, in the operator norm for the sup norm on `Fin 4 → ℝ`: at a
state `y` with every coordinate at most `r` in absolute value, the second derivative of component
`i` has norm at most `H i`, with `H = (6 r, 0, 0, r)`. -/
lemma norm_fderiv_fderiv_reducedField_le {r : ℝ} {y : Fin 4 → ℝ} (hy : ∀ j, |y j| ≤ r)
    (i : Fin 4) :
    ‖fderiv ℝ (fderiv ℝ fun e => reducedField e i) y‖ ≤ ![6 * r, 0, 0, r] i := by
  have hr : 0 ≤ r := (abs_nonneg _).trans (hy 0)
  have hn : ∀ (v : Fin 4 → ℝ) (j : Fin 4), |v j| ≤ ‖v‖ := fun v j => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm v j
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
  · refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun h k => ?_
    rw [(fderiv_fderiv_reducedField_apply y h k).1, Real.norm_eq_abs]
    calc |-6 * y 0 * h 0 * k 0| = 6 * |y 0| * |h 0| * |k 0| := by
          rw [abs_mul, abs_mul, abs_mul]
          norm_num
      _ ≤ 6 * r * ‖h‖ * ‖k‖ := by
          gcongr
          · exact hy 0
          · exact hn h 0
          · exact hn k 0
  · refine ContinuousLinearMap.opNorm_le_bound₂ _ le_rfl fun h k => ?_
    rw [(fderiv_fderiv_reducedField_apply y h k).2.1]
    simp
  · refine ContinuousLinearMap.opNorm_le_bound₂ _ le_rfl fun h k => ?_
    rw [(fderiv_fderiv_reducedField_apply y h k).2.2.1]
    simp
  · refine ContinuousLinearMap.opNorm_le_bound₂ _ hr fun h k => ?_
    rw [(fderiv_fderiv_reducedField_apply y h k).2.2.2, Real.norm_eq_abs]
    calc |Real.sin (y 2) * h 2 * k 2| = |Real.sin (y 2)| * |h 2| * |k 2| := by
          rw [abs_mul, abs_mul]
      _ ≤ r * ‖h‖ * ‖k‖ := by
          gcongr
          · exact Real.abs_sin_le_abs.trans (hy 2)
          · exact hn h 2
          · exact hn k 2

/-- **The component-Hessian remainder theorem, instantiated.** For `0 < r` and a deviation `δ`
with every coordinate at most `r` in absolute value, the reused componentwise bound
`Statistics.UncertaintyPropagation.jacobianRemainder_component_le_of_hessian`, applied on that box
with the Hessian bounds above, gives `|jacobianRemainder reducedField 0 δ i| ≤ H i / 2 * ‖δ‖²` in
the sup norm, `H = (6 r, 0, 0, r)`: the constants `3 r` and `r / 2` of components `0` and `3` are
three times those of `longitudinalRemainder_bounds`. -/
lemma jacobianRemainder_reducedField_le_of_hessian {r : ℝ} (hr0 : 0 < r) {δ : Fin 4 → ℝ}
    (hδ : ∀ j, |δ j| ≤ r) (i : Fin 4) :
    |Statistics.UncertaintyPropagation.jacobianRemainder reducedField 0 δ i| ≤
      ![6 * r, 0, 0, r] i / 2 * ‖δ‖ ^ 2 := by
  have hIcc : ∀ y ∈ Set.Icc (fun _ : Fin 4 => -r) (fun _ => r), ∀ j, |y j| ≤ r :=
    fun y hy j => abs_le.2 ⟨hy.1 j, hy.2 j⟩
  refine Statistics.UncertaintyPropagation.jacobianRemainder_component_le_of_hessian reducedField
    0 δ i ![6 * r, 0, 0, r] isOpen_univ (Set.subset_univ _)
    hasFDerivAt_reducedField_zero.differentiableAt
    (contDiff_pi.1 contDiff_reducedField i).contDiffOn
    (fun y hy => norm_fderiv_fderiv_reducedField_le (hIcc y hy) i) ?_ ?_
  · exact ⟨fun j => by simp only [Pi.zero_apply]; linarith, fun j => by
      simp only [Pi.zero_apply]; linarith⟩
  · rw [zero_add]
    exact ⟨fun j => (abs_le.1 (hδ j)).1, fun j => (abs_le.1 (hδ j)).2⟩

/-- **Sup and Euclidean norms of a state.** For `e : EuclideanSpace ℝ (Fin 4)` with coordinates
`WithLp.ofLp e`, the sup norm and the Euclidean norm compare as `‖ofLp e‖ ≤ ‖e‖ ≤ 2 ‖ofLp e‖`,
the factor `2` being `√4`. -/
lemma norm_ofLp_le_norm_le_two_mul (e : EuclideanSpace ℝ (Fin 4)) :
    ‖(WithLp.ofLp e : Fin 4 → ℝ)‖ ≤ ‖e‖ ∧ ‖e‖ ≤ 2 * ‖(WithLp.ofLp e : Fin 4 → ℝ)‖ := by
  refine ⟨(pi_norm_le_iff_of_nonneg (norm_nonneg e)).2 fun i => PiLp.norm_apply_le e i, ?_⟩
  have hi : ∀ i, ‖e i‖ ^ 2 ≤ ‖(WithLp.ofLp e : Fin 4 → ℝ)‖ ^ 2 := fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (WithLp.ofLp e) i) 2
  have hsq : ‖e‖ ^ 2 ≤ (2 * ‖(WithLp.ofLp e : Fin 4 → ℝ)‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
    nlinarith [hi 0, hi 1, hi 2, hi 3]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

/-- **The Euclidean ball lies in the box**: every coordinate of a state of Euclidean norm at most
`r` is at most `r` in absolute value. -/
lemma abs_ofLp_le_of_norm_le {r : ℝ} {e : EuclideanSpace ℝ (Fin 4)} (he : ‖e‖ ≤ r)
    (i : Fin 4) : |WithLp.ofLp e i| ≤ r := by
  have h := PiLp.norm_apply_le e i
  rw [Real.norm_eq_abs] at h
  exact h.trans he

/-- **Remainder bounds, Euclidean norm.** For `0 < r ≤ 1/100` and a state `e` of Euclidean norm at
most `r`, its coordinates lie in the actuator box and the remainder satisfies
`|-x³| ≤ r ‖e‖²`, `0`, `0` and `|θ - sin θ| ≤ (r / 6) ‖e‖²`: the sup-norm bounds through
`‖ofLp e‖ ≤ ‖e‖`. -/
lemma longitudinalRemainder_bounds_euclidean {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 100)
    {e : EuclideanSpace ℝ (Fin 4)} (he : ‖e‖ ≤ r) :
    WithLp.ofLp e ∈ actuatorBox ∧ |longitudinalRemainder (WithLp.ofLp e) 0| ≤ r * ‖e‖ ^ 2 ∧
      longitudinalRemainder (WithLp.ofLp e) 1 = 0 ∧
      longitudinalRemainder (WithLp.ofLp e) 2 = 0 ∧
      |longitudinalRemainder (WithLp.ofLp e) 3| ≤ r / 6 * ‖e‖ ^ 2 := by
  obtain ⟨hA, h0, h1, h2, h3⟩ := longitudinalRemainder_bounds hr0 hr (abs_ofLp_le_of_norm_le he)
  have hsq : ‖(WithLp.ofLp e : Fin 4 → ℝ)‖ ^ 2 ≤ ‖e‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_ofLp_le_norm_le_two_mul e).1 2
  exact ⟨hA, h0.trans (mul_le_mul_of_nonneg_left hsq hr0.le), h1, h2,
    h3.trans (mul_le_mul_of_nonneg_left hsq (by positivity))⟩

/-- **No stationary world position.** For any mass distribution `B`, gravity `g` and coordinates
`X₁`, `X₂`, `θ`, if the planar motion is a plant solution at `t`, its state lies in the actuator
box, so its forward position rate `X₁' = 1 + x` is at least `99/100`. The world position is not
part of the reduced state; `longitudinalJacobian` linearizes the reduced field only. -/
lemma planar_sixDofPlant_forward_rate {B : RigidBody 3} {X₁ X₂ θ : Time → ℝ}
    {g : Fin 3 → ℝ} {t : Time}
    (h : SixDofPlant longitudinalMaps (planarState X₁ X₂ θ) (planarMotion B X₁ X₂ θ) g t) :
    99 / 100 ≤ ∂ₜ X₁ t := by
  obtain ⟨-, -, hx, -⟩ := h
  have h0 : |planarState X₁ X₂ θ t 0| ≤ 1 / 100 := hx 0
  simp only [planarState, Matrix.cons_val_zero] at h0
  linarith [(abs_le.1 h0).1]


/-! ## F. A Lyapunov certificate for the reduced linear plant -/

/-- The Lyapunov matrix of the reduced linear plant, in the state order `(x, z, θ, q)`:
`P = diag(1/2, 1/2) ⊕ [[3/2, 1/2], [1/2, 1/2]]`. -/
noncomputable def longitudinalLyapunovMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 2, 0, 0, 0; 0, 1 / 2, 0, 0; 0, 0, 3 / 2, 1 / 2; 0, 0, 1 / 2, 1 / 2]

/-- The reduced linear plant `e' = A e` on the Euclidean state space: the Jacobian
`longitudinalJacobian` acting on the coordinates `WithLp.ofLp e`, that is
`(x, z, θ, q) ↦ (-x, -z, q, -θ - 2 q)`. -/
def linearReducedField (e : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (longitudinalJacobian *ᵥ WithLp.ofLp e)

/-- The quadratic Lyapunov function `V(e) = eᵀ P e` of a state `e` with coordinates
`WithLp.ofLp e`: `x² / 2 + z² / 2 + 3 θ² / 2 + θ q + q² / 2`. -/
noncomputable def longitudinalLyapunov (e : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  WithLp.ofLp e ⬝ᵥ (longitudinalLyapunovMatrix *ᵥ WithLp.ofLp e)

/-- The Lyapunov matrix is the direct sum of the translational block `diag(1/2, 1/2)` on `(x, z)`
and the pitch block `[[3/2, 1/2], [1/2, 1/2]]` on `(θ, q)`, the block form of
`longitudinalJacobian_eq_fromBlocks`. -/
lemma longitudinalLyapunovMatrix_eq_fromBlocks :
    longitudinalLyapunovMatrix = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (Matrix.diagonal ![1 / 2, 1 / 2]) 0 0
        !![3 / 2, 1 / 2; 1 / 2, 1 / 2]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **The linearization.** In coordinates the reduced linear plant is the derivative of the
reduced field at the trim: `A e = Df(0) e`, by `hasFDerivAt_reducedField_zero`. -/
lemma linearReducedField_eq_fderiv (e : EuclideanSpace ℝ (Fin 4)) :
    WithLp.ofLp (linearReducedField e) = fderiv ℝ reducedField 0 (WithLp.ofLp e) := by
  rw [hasFDerivAt_reducedField_zero.fderiv]
  simp [linearReducedField, Matrix.toLin'_apply]

/-- `P` is symmetric. -/
private lemma longitudinalLyapunovMatrix_isHermitian :
    longitudinalLyapunovMatrix.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longitudinalLyapunovMatrix]

/-- `V` in coordinates. -/
private lemma longitudinalLyapunov_eq_coords (e : EuclideanSpace ℝ (Fin 4)) :
    longitudinalLyapunov e =
      1 / 2 * e 0 ^ 2 + 1 / 2 * e 1 ^ 2 + 3 / 2 * e 2 ^ 2 + e 2 * e 3 + 1 / 2 * e 3 ^ 2 := by
  simp [longitudinalLyapunov, longitudinalLyapunovMatrix, dotProduct, Matrix.mulVec,
    Fin.sum_univ_four]
  ring

/-- The squared Euclidean norm in coordinates. -/
private lemma norm_sq_eq_coords (e : EuclideanSpace ℝ (Fin 4)) :
    ‖e‖ ^ 2 = e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 + e 3 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  simp [Real.norm_eq_abs, sq_abs]

/-- The coordinate functions of the Euclidean state space are differentiable. -/
private lemma hasFDerivAt_coord (i : Fin 4) (e : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt (fun e : EuclideanSpace ℝ (Fin 4) => e i)
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ) e :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).hasFDerivAt

/-- The derivative of `V`: `h ↦ x h₀ + z h₁ + (3 θ + q) h₂ + (θ + q) h₃`. -/
private lemma hasFDerivAt_longitudinalLyapunov (e : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt longitudinalLyapunov
      (e 0 • (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ) +
        e 1 • (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ) +
        (3 * e 2 + e 3) • (EuclideanSpace.proj 2 : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ) +
        (e 2 + e 3) • (EuclideanSpace.proj 3 : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ)) e := by
  have hV : longitudinalLyapunov = fun e : EuclideanSpace ℝ (Fin 4) =>
      1 / 2 * e 0 ^ 2 + 1 / 2 * e 1 ^ 2 + 3 / 2 * e 2 ^ 2 + e 2 * e 3 + 1 / 2 * e 3 ^ 2 :=
    funext longitudinalLyapunov_eq_coords
  rw [hV]
  have h0 := ((hasFDerivAt_coord 0 e).pow 2).const_mul (1 / 2 : ℝ)
  have h1 := ((hasFDerivAt_coord 1 e).pow 2).const_mul (1 / 2 : ℝ)
  have h2 := ((hasFDerivAt_coord 2 e).pow 2).const_mul (3 / 2 : ℝ)
  have h23 := (hasFDerivAt_coord 2 e).fun_mul (hasFDerivAt_coord 3 e)
  have h3 := ((hasFDerivAt_coord 3 e).pow 2).const_mul (1 / 2 : ℝ)
  refine ((((h0.fun_add h1).fun_add h2).fun_add h23).fun_add h3).congr_fderiv
    (ContinuousLinearMap.ext fun v => ?_)
  simp only [add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul, PiLp.proj_apply, Nat.cast_ofNat,
    Nat.reduceSub, pow_one]
  ring

/-- **Definiteness of the certificate.** The Lyapunov matrix `P` and `Q = 1` are symmetric
positive definite. For `P` this is Sylvester's criterion: its leading principal minors are
`1/2`, `1/4`, `3/8` and `1/8`, the last being `1/4` times the pitch-block determinant `1/2`. -/
lemma longitudinalLyapunovMatrix_posDef :
    longitudinalLyapunovMatrix.PosDef ∧ (1 : Matrix (Fin 4) (Fin 4) ℝ).PosDef := by
  refine ⟨(Matrix.posDef_iff_leadingPrincipalMinors_pos 4 _
    longitudinalLyapunovMatrix_isHermitian).2 fun k hk => ?_, Matrix.PosDef.one⟩
  interval_cases k
  · simp [Matrix.leadingPrincipalSubmatrix]
  · simp [Matrix.leadingPrincipalSubmatrix, longitudinalLyapunovMatrix]
  · rw [Matrix.det_fin_two]
    norm_num [Matrix.leadingPrincipalSubmatrix, longitudinalLyapunovMatrix]
  · rw [Matrix.det_fin_three]
    norm_num [Matrix.leadingPrincipalSubmatrix, longitudinalLyapunovMatrix]
  · rw [Matrix.leadingPrincipalSubmatrix_self, longitudinalLyapunovMatrix_eq_fromBlocks,
      Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fin_two]
    simp
    norm_num

/-- **The Lyapunov equation.** `Aᵀ P + P A = -Q` with `Q = 1`: every entry of the sum is that of
`-1`. -/
lemma longitudinalLyapunov_equation :
    longitudinalJacobianᵀ * longitudinalLyapunovMatrix +
      longitudinalLyapunovMatrix * longitudinalJacobian = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalJacobian, longitudinalLyapunovMatrix, Matrix.mul_apply,
      Fin.sum_univ_four] <;>
    norm_num

/-- **Comparison bounds.** In the Euclidean norm, `(1/4) ‖e‖² ≤ V(e) ≤ 2 ‖e‖²`: the eigenvalues
of `P` are `1/2` (twice) and `1 ± 1/√2`, all in `[1/4, 2]`. -/
lemma longitudinalLyapunov_bounds (e : EuclideanSpace ℝ (Fin 4)) :
    1 / 4 * ‖e‖ ^ 2 ≤ longitudinalLyapunov e ∧ longitudinalLyapunov e ≤ 2 * ‖e‖ ^ 2 := by
  rw [longitudinalLyapunov_eq_coords, norm_sq_eq_coords]
  constructor
  · nlinarith [sq_nonneg (e 0), sq_nonneg (e 1), sq_nonneg (e 3 + 2 * e 2), sq_nonneg (e 2)]
  · nlinarith [sq_nonneg (e 0), sq_nonneg (e 1), sq_nonneg (e 2 - e 3), sq_nonneg (e 3)]

/-- **The trim is the only zero of `V`.** `V(e) = 0` exactly when `e = 0`. -/
lemma longitudinalLyapunov_eq_zero_iff (e : EuclideanSpace ℝ (Fin 4)) :
    longitudinalLyapunov e = 0 ↔ e = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h, longitudinalLyapunov]⟩
  have h1 := (longitudinalLyapunov_bounds e).1
  rw [h] at h1
  have h2 : ‖e‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

/-- `V` is differentiable: a quadratic polynomial in the coordinates. -/
lemma differentiable_longitudinalLyapunov : Differentiable ℝ longitudinalLyapunov := by
  exact fun e => (hasFDerivAt_longitudinalLyapunov e).differentiableAt

/-- **The derivative of `V`.** `DV(e) h = 2 hᵀ P e`, `P` being symmetric. -/
lemma fderiv_longitudinalLyapunov_apply (e h : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ longitudinalLyapunov e h =
      2 * (WithLp.ofLp h ⬝ᵥ (longitudinalLyapunovMatrix *ᵥ WithLp.ofLp e)) := by
  rw [(hasFDerivAt_longitudinalLyapunov e).fderiv]
  simp [longitudinalLyapunovMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  ring

/-- **The orbital derivative along the plant.** `DV(e) (A e) = eᵀ (Aᵀ P + P A) e = -‖e‖²`: zero
at the trim `e = 0`, negative at every other state. -/
lemma fderiv_longitudinalLyapunov_linearReducedField (e : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ longitudinalLyapunov e (linearReducedField e) = -‖e‖ ^ 2 := by
  rw [fderiv_longitudinalLyapunov_apply, norm_sq_eq_coords]
  simp [linearReducedField, longitudinalJacobian, longitudinalLyapunovMatrix, dotProduct,
    Matrix.mulVec, Fin.sum_univ_four]
  ring

/-- **The actual global solution.** From every initial state `e₀` the reduced linear plant has
exactly one solution `e` defined at all times, with `e 0 = e₀` and `e' = A e`: the field is
linear, hence globally Lipschitz, and the global existence theorem for globally Lipschitz fields
applies. -/
lemma existsUnique_linearReducedField_solution (e₀ : EuclideanSpace ℝ (Fin 4)) :
    ∃! e : ℝ → EuclideanSpace ℝ (Fin 4),
      e 0 = e₀ ∧ ∀ t, HasDerivAt e (linearReducedField (e t)) t := by
  let F : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap ∘L
      (LinearMap.toContinuousLinearMap (Matrix.toLin' longitudinalJacobian)) ∘L
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap
  have hF : (fun e => linearReducedField e) = ⇑F := by
    funext e
    simp [F, linearReducedField, Matrix.toLin'_apply]
    rfl
  refine MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    (fun _ e => linearReducedField e) 0 e₀ ‖F‖₊ ?_ fun _ => ?_
  · have hu : Function.uncurry (fun (_ : ℝ) (e : EuclideanSpace ℝ (Fin 4)) =>
        linearReducedField e) = fun p => F p.2 := by
      funext p
      exact congrFun hF p.2
    rw [hu]
    exact F.continuous.comp continuous_snd
  · rw [hF]
    exact F.lipschitzWith

/-- **Exponential decay, by the direct method.** Every forward solution of the reduced linear
plant on `[0, ∞)` satisfies `‖e t‖ ≤ √8 * exp (-t / 4) * ‖e 0‖` for `t ≥ 0`: along it `V` has
derivative `-‖e‖² ≤ -V / 2`, so `V` decays at least as `exp (-t / 2)`, and the comparison bounds
give the factor `√(2 / (1/4)) = √8`. From the trim, `e 0 = 0`, the bound forces `e t = 0`: no
decay is claimed there. -/
lemma norm_le_of_isIntegralCurveOn_linearReducedField {e : ℝ → EuclideanSpace ℝ (Fin 4)}
    (he : IsIntegralCurveOn e (fun _ x => linearReducedField x) (Set.Ici 0)) {t : ℝ}
    (ht : 0 ≤ t) : ‖e t‖ ≤ Real.sqrt 8 * Real.exp (-t / 4) * ‖e 0‖ := by
  have h := he.norm_sub_le_of_lyapunov (s := Set.univ) (V := longitudinalLyapunov)
    (V' := fderiv ℝ longitudinalLyapunov) (a := 1 / 2) (x₀ := 0) (c₁ := 1 / 4) (c₂ := 2)
    (fun _ _ => Set.mem_univ _)
    (fun x _ => (differentiable_longitudinalLyapunov x).hasFDerivAt)
    (fun _ _ x _ => by
      rw [fderiv_longitudinalLyapunov_linearReducedField]
      linarith [(longitudinalLyapunov_bounds x).2])
    (by norm_num)
    (fun x _ => by simpa using (longitudinalLyapunov_bounds x).1)
    (fun x _ => by simpa using (longitudinalLyapunov_bounds x).2) ht
  have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
  have hexp : -(1 / 2 / 2) * t = -t / 4 := by ring
  rw [sub_zero, sub_zero, h8, hexp] at h
  exact h

/-- **Decay of the actual initial-value problem.** For every initial state `e₀`, the actual
global solution of `e' = A e`, `e 0 = e₀`, satisfies `‖e t‖ ≤ √8 * exp (-t / 4) * ‖e₀‖` for
every `t ≥ 0`. -/
lemma linearReducedField_solution_decay (e₀ : EuclideanSpace ℝ (Fin 4)) :
    ∃ e : ℝ → EuclideanSpace ℝ (Fin 4), e 0 = e₀ ∧
      (∀ t, HasDerivAt e (linearReducedField (e t)) t) ∧
      ∀ t, 0 ≤ t → ‖e t‖ ≤ Real.sqrt 8 * Real.exp (-t / 4) * ‖e₀‖ := by
  obtain ⟨e, ⟨h0, hd⟩, -⟩ := existsUnique_linearReducedField_solution e₀
  refine ⟨e, h0, hd, fun t ht => ?_⟩
  rw [← h0]
  exact norm_le_of_isIntegralCurveOn_linearReducedField (fun s _ => (hd s).hasDerivWithinAt) ht

/-! ## G. Local existence and decay of the nonlinear reduced flight -/

/-- The nonlinear reduced field on the Euclidean state space: the reduced longitudinal field
`reducedField` acting on the coordinates `WithLp.ofLp e`, that is
`(x, z, θ, q) ↦ (-x - x³, -z, q, -2 q - sin θ)`. -/
noncomputable def nonlinearReducedField (e : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (reducedField (WithLp.ofLp e))

/-- The nonlinear reduced field is `C²`: the reduced field between the coordinate maps. -/
private lemma contDiff_nonlinearReducedField : ContDiff ℝ 2 nonlinearReducedField :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.contDiff.comp
    (contDiff_reducedField.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).contDiff)

/-- **The explicit field.** In coordinates the nonlinear reduced field is the reduced linear plant
plus the remainder of section E: `f e = A e + (-x³, 0, 0, θ - sin θ)`. -/
lemma ofLp_nonlinearReducedField (e : EuclideanSpace ℝ (Fin 4)) :
    WithLp.ofLp (nonlinearReducedField e) =
      WithLp.ofLp (linearReducedField e) + longitudinalRemainder (WithLp.ofLp e) := by
  simp only [nonlinearReducedField, linearReducedField, WithLp.ofLp_toLp]
  exact reducedField_eq_mulVec_add_remainder _

/-- **The orbital derivative.** Along the nonlinear reduced field, `V(e) = eᵀ P e` of section F
has the derivative `DV(e) f(e) = 2 f(e)ᵀ P e = -‖e‖² - x⁴ + (θ + q) (θ - sin θ)`: the linear
part gives `-‖e‖²` and the remainder `(-x³, 0, 0, θ - sin θ)` the other two terms. -/
lemma fderiv_longitudinalLyapunov_nonlinearReducedField (e : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ longitudinalLyapunov e (nonlinearReducedField e) =
      -‖e‖ ^ 2 - e 0 ^ 4 + (e 2 + e 3) * (e 2 - Real.sin (e 2)) := by
  rw [fderiv_longitudinalLyapunov_apply, ofLp_nonlinearReducedField, norm_sq_eq_coords]
  simp [linearReducedField, longitudinalJacobian, longitudinalRemainder,
    longitudinalLyapunovMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  ring

/-- **The Lyapunov inequality on the ball.** For `‖e‖ ≤ r = 1/100`, the cubic sine bound
`|θ - sin θ| ≤ (r / 6) ‖e‖²` and `|θ + q| ≤ 2 r` make the last term at most `‖e‖² / 30000`, so
`DV(e) f(e) ≤ -(1/2) ‖e‖² ≤ -V(e) / 4`. -/
lemma fderiv_longitudinalLyapunov_nonlinearReducedField_le {e : EuclideanSpace ℝ (Fin 4)}
    (he : ‖e‖ ≤ 1 / 100) :
    fderiv ℝ longitudinalLyapunov e (nonlinearReducedField e) ≤ -(1 / 2) * ‖e‖ ^ 2 ∧
      -(1 / 2) * ‖e‖ ^ 2 ≤ -longitudinalLyapunov e / 4 := by
  obtain ⟨-, -, -, -, h3⟩ :=
    longitudinalRemainder_bounds_euclidean (r := 1 / 100) (by norm_num) le_rfl he
  have h3' : |e 2 - Real.sin (e 2)| ≤ 1 / 600 * ‖e‖ ^ 2 := by
    simp only [longitudinalRemainder, Matrix.cons_val] at h3
    linarith
  have hθ := abs_ofLp_le_of_norm_le he 2
  have hq := abs_ofLp_le_of_norm_le he 3
  have hsum : |e 2 + e 3| ≤ 2 / 100 := (abs_add_le _ _).trans (by linarith)
  have hprod : (e 2 + e 3) * (e 2 - Real.sin (e 2)) ≤ 1 / 30000 * ‖e‖ ^ 2 := by
    calc (e 2 + e 3) * (e 2 - Real.sin (e 2))
        ≤ |e 2 + e 3| * |e 2 - Real.sin (e 2)| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ 2 / 100 * (1 / 600 * ‖e‖ ^ 2) :=
        mul_le_mul hsum h3' (abs_nonneg _) (by norm_num)
      _ = 1 / 30000 * ‖e‖ ^ 2 := by ring
  have hx4 : 0 ≤ e 0 ^ 4 := by positivity
  have hb := (longitudinalLyapunov_bounds e).2
  rw [fderiv_longitudinalLyapunov_nonlinearReducedField]
  constructor
  · nlinarith [sq_nonneg ‖e‖]
  · linarith

/-- **Strict decay only away from the trim.** On the ball `‖e‖ ≤ 1/100`, the orbital derivative
is negative exactly at the states other than the trim; at the trim it is `0`. -/
lemma fderiv_longitudinalLyapunov_nonlinearReducedField_neg_iff
    {e : EuclideanSpace ℝ (Fin 4)} (he : ‖e‖ ≤ 1 / 100) :
    fderiv ℝ longitudinalLyapunov e (nonlinearReducedField e) < 0 ↔ e ≠ 0 := by
  constructor
  · rintro h rfl
    rw [fderiv_longitudinalLyapunov_nonlinearReducedField] at h
    simp at h
  · intro h
    have hpos : 0 < ‖e‖ := norm_pos_iff.2 h
    have h1 := (fderiv_longitudinalLyapunov_nonlinearReducedField_le he).1
    nlinarith

/-- **A compact sublevel set between two balls.** The sublevel set `{V ≤ r² / 8} = {V ≤ 1/80000}`
is compact, contains the closed ball of radius `r / 4 = 1/400` about the trim (where
`V ≤ 2 ‖e‖²`), and lies in the ball `‖e‖² ≤ r² / 2 = 1/20000` (where `V ≥ ‖e‖² / 4`), hence in the
actuator box: every coordinate is at most the Euclidean norm. -/
lemma longitudinalLyapunov_sublevel_spec :
    IsCompact {e : EuclideanSpace ℝ (Fin 4) | longitudinalLyapunov e ≤ 1 / 80000} ∧
      (∀ e : EuclideanSpace ℝ (Fin 4), ‖e‖ ≤ 1 / 400 → longitudinalLyapunov e ≤ 1 / 80000) ∧
      ∀ e : EuclideanSpace ℝ (Fin 4), longitudinalLyapunov e ≤ 1 / 80000 →
        ‖e‖ ^ 2 ≤ 1 / 20000 ∧ WithLp.ofLp e ∈ actuatorBox := by
  have hin : ∀ e : EuclideanSpace ℝ (Fin 4), longitudinalLyapunov e ≤ 1 / 80000 →
      ‖e‖ ^ 2 ≤ 1 / 20000 := fun e he => by
    linarith [(longitudinalLyapunov_bounds e).1]
  have hball : ∀ e : EuclideanSpace ℝ (Fin 4), longitudinalLyapunov e ≤ 1 / 80000 →
      ‖e‖ ≤ 1 / 100 := fun e he => by
    nlinarith [hin e he, norm_nonneg e]
  refine ⟨Metric.isCompact_of_isClosed_isBounded
    (isClosed_le differentiable_longitudinalLyapunov.continuous continuous_const)
    (Metric.isBounded_closedBall.subset fun e he => mem_closedBall_zero_iff.2 (hball e he)),
    fun e he => ?_, fun e he => ⟨hin e he, fun i => abs_ofLp_le_of_norm_le (hball e he) i⟩⟩
  nlinarith [(longitudinalLyapunov_bounds e).2, norm_nonneg e]

/-- **Sublevel invariance.** Every forward solution of the nonlinear reduced field on `[0, ∞)`
that starts in a sublevel set `{V ≤ c}` with `c ≤ 1/80000` stays in it. The sublevel set lies
strictly inside the ball `‖e‖ < 1/100`, where the orbital derivative is `≤ 0`; up to the first
time the solution reached the sphere `‖e‖ = 1/100`, `V` does not increase, so that time does not
exist; then the sublevel lemma of the direct method applies on `[0, ∞)`. -/
lemma mapsTo_sublevel_of_isIntegralCurveOn_nonlinearReducedField
    {e : ℝ → EuclideanSpace ℝ (Fin 4)}
    (he : IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0)) {c : ℝ}
    (hc : c ≤ 1 / 80000) (h₀ : longitudinalLyapunov (e 0) ≤ c) :
    Set.MapsTo e (Set.Ici 0) {x | longitudinalLyapunov x ≤ c} := by
  have hsub : ∀ x : EuclideanSpace ℝ (Fin 4), longitudinalLyapunov x ≤ c → ‖x‖ < 1 / 100 := by
    intro x hx
    nlinarith [(longitudinalLyapunov_sublevel_spec.2.2 x (hx.trans hc)).1, norm_nonneg x]
  have hcont : ContinuousOn e (Set.Ici 0) := fun t ht => (he t ht).continuousWithinAt
  have hderiv : ∀ t, 0 < t → HasDerivAt e (nonlinearReducedField (e t)) t := fun t ht =>
    (he t (Set.mem_Ici.2 ht.le)).hasDerivAt (Ici_mem_nhds ht)
  have hdV : ∀ x : EuclideanSpace ℝ (Fin 4), ‖x‖ ≤ 1 / 100 →
      fderiv ℝ longitudinalLyapunov x (nonlinearReducedField x) ≤ 0 := fun x hx => by
    nlinarith [(fderiv_longitudinalLyapunov_nonlinearReducedField_le hx).1, sq_nonneg ‖x‖]
  have hball : ∀ t, 0 ≤ t → ‖e t‖ < 1 / 100 := by
    by_contra hne
    push Not at hne
    obtain ⟨t₁, ht₁, hle⟩ := hne
    set A : Set ℝ := Set.Icc 0 t₁ ∩ (fun t => ‖e t‖) ⁻¹' Set.Ici (1 / 100) with hA
    have hAcl : IsClosed A :=
      ((hcont.mono Set.Icc_subset_Ici_self).norm).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Ici
    have hAne : A.Nonempty := ⟨t₁, ⟨ht₁, le_rfl⟩, hle⟩
    have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
    have hτ : sInf A ∈ A := hAcl.csInf_mem hAne hAbdd
    have hbefore : ∀ t ∈ Set.Ioo 0 (sInf A), ‖e t‖ < 1 / 100 := by
      intro t ht
      by_contra h
      push Not at h
      have h' : sInf A ≤ t := csInf_le hAbdd ⟨⟨ht.1.le, ht.2.le.trans hτ.1.2⟩, h⟩
      linarith [ht.2]
    have hmaps := MathlibExt.Analysis.ODE.finite_interval_mapsTo_sublevel
      (V := longitudinalLyapunov) (f := fun _ x => nonlinearReducedField x) hτ.1.1
      (differentiable_longitudinalLyapunov.continuous.comp_continuousOn
        (hcont.mono Set.Icc_subset_Ici_self))
      (fun t ht => hderiv t ht.1) (fun t _ => differentiable_longitudinalLyapunov _)
      (fun t ht => hdV _ (hbefore t ht).le) h₀
    exact absurd hτ.2 (not_le.2 (hsub _ (hmaps ⟨hτ.1.1, le_rfl⟩)))
  exact he.mapsTo_sublevel_of_lyapunov (s := {x | ‖x‖ < 1 / 100})
    (V' := fderiv ℝ longitudinalLyapunov) hball
    (fun x _ => (differentiable_longitudinalLyapunov x).hasFDerivAt)
    (fun _ _ x hx => hdV x (le_of_lt hx)) h₀

/-- **Conditional decay from the Lyapunov inequality.** A forward solution of the nonlinear
reduced field that stays in the ball `‖e‖ ≤ 1/100` for `t ≥ 0` satisfies
`‖e t‖ ≤ √8 * exp (-t / 8) * ‖e 0‖`: by the direct method with `V' ≤ -V / 4`, `V` decays at least
as `exp (-t / 4)`, and the comparison bounds give `√(2 / (1/4)) = √8`. The hypothesis that the
solution stays in the ball is not implied by its starting there. -/
lemma norm_le_of_isIntegralCurveOn_nonlinearReducedField_of_norm_le
    {e : ℝ → EuclideanSpace ℝ (Fin 4)}
    (he : IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0))
    (hs : ∀ t, 0 ≤ t → ‖e t‖ ≤ 1 / 100) {t : ℝ} (ht : 0 ≤ t) :
    ‖e t‖ ≤ Real.sqrt 8 * Real.exp (-t / 8) * ‖e 0‖ := by
  have h := he.norm_sub_le_of_lyapunov (s := {x | ‖x‖ ≤ 1 / 100}) (V := longitudinalLyapunov)
    (V' := fderiv ℝ longitudinalLyapunov) (a := 1 / 4) (x₀ := 0) (c₁ := 1 / 4) (c₂ := 2) hs
    (fun x _ => (differentiable_longitudinalLyapunov x).hasFDerivAt)
    (fun _ _ x hx => by
      have h := fderiv_longitudinalLyapunov_nonlinearReducedField_le hx
      linarith [h.1, h.2])
    (by norm_num)
    (fun x _ => by simpa using (longitudinalLyapunov_bounds x).1)
    (fun x _ => by simpa using (longitudinalLyapunov_bounds x).2) ht
  have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
  have hexp : -(1 / 4 / 2) * t = -t / 8 := by ring
  rw [sub_zero, sub_zero, h8, hexp] at h
  exact h

/-- **Local exponential decay.** Every forward solution of the nonlinear reduced field on
`[0, ∞)` with `‖e 0‖ ≤ r / 4 = 1/400` satisfies `‖e t‖ ≤ √8 * exp (-t / 8) * ‖e 0‖` for `t ≥ 0`:
it starts in the invariant sublevel set `{V ≤ 1/80000}`, which lies in the ball of radius
`1/100`. From the trim, `e 0 = 0`, the bound forces `e t = 0`: no decay is claimed there. -/
lemma norm_le_of_isIntegralCurveOn_nonlinearReducedField {e : ℝ → EuclideanSpace ℝ (Fin 4)}
    (he : IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0))
    (he₀ : ‖e 0‖ ≤ 1 / 400) {t : ℝ} (ht : 0 ≤ t) :
    ‖e t‖ ≤ Real.sqrt 8 * Real.exp (-t / 8) * ‖e 0‖ := by
  obtain ⟨-, hball, hin⟩ := longitudinalLyapunov_sublevel_spec
  have hmaps := mapsTo_sublevel_of_isIntegralCurveOn_nonlinearReducedField he le_rfl
    (hball _ he₀)
  refine norm_le_of_isIntegralCurveOn_nonlinearReducedField_of_norm_le he (fun s hs => ?_) ht
  nlinarith [(hin _ (hmaps (Set.mem_Ici.2 hs))).1, norm_nonneg (e s)]

/-- **Existence by compact-exit continuation.** From every initial state `e₀` with
`‖e₀‖ ≤ r / 4 = 1/400` the nonlinear reduced field has a forward solution on `[0, ∞)` whose
coordinates stay in the actuator box. The maximal solution in the open set `ℝ × {‖e‖ < 1/100}`,
built from local Picard–Lindelöf solutions, keeps `V ≤ 1/80000` on its interval by sublevel
invariance, so it never leaves the compact set `[0, T] × {V ≤ 1/80000}`: by the compact-exit
theorem its interval contains `[0, ∞)`. -/
lemma exists_nonlinearReducedField_solution (e₀ : EuclideanSpace ℝ (Fin 4))
    (he₀ : ‖e₀‖ ≤ 1 / 400) :
    ∃ e : ℝ → EuclideanSpace ℝ (Fin 4), e 0 = e₀ ∧
      IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0) ∧
      ∀ t, 0 ≤ t → WithLp.ofLp (e t) ∈ actuatorBox := by
  obtain ⟨hK, hball, hin⟩ := longitudinalLyapunov_sublevel_spec
  set U : Set (ℝ × EuclideanSpace ℝ (Fin 4)) := Set.univ ×ˢ Metric.ball 0 (1 / 100) with hUdef
  have hU : IsOpen U := isOpen_univ.prod Metric.isOpen_ball
  have hmem : ((0 : ℝ), e₀) ∈ U := ⟨trivial, mem_ball_zero_iff.2 (by linarith)⟩
  have hcd : ContDiff ℝ 1 nonlinearReducedField :=
    contDiff_nonlinearReducedField.of_le (by norm_num)
  have hf : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin 4) => nonlinearReducedField p.2) U :=
    (hcd.continuous.comp continuous_snd).continuousOn
  have hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p, ∀ t : ℝ, ∀ x y : EuclideanSpace ℝ (Fin 4),
      (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (nonlinearReducedField (t, x).2) (nonlinearReducedField (t, y).2) ≤ C * dist x y := by
    intro p _
    obtain ⟨K, s, hs, hKs⟩ := (hcd.contDiffAt (x := p.2)).exists_lipschitzOnWith
    exact ⟨K, Set.univ ×ˢ s, prod_mem_nhds Filter.univ_mem hs,
      fun t x y hx hy => hKs.dist_le_mul x hx.1.2 y hy.1.2⟩
  obtain ⟨I, x, hx0, -, h0I, hIc, hsol, hexit⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact U
      (fun p => nonlinearReducedField p.2) 0 e₀ hU hmem hf hlip
  have hinv : ∀ t ∈ I, 0 ≤ t → longitudinalLyapunov (x t) ≤ 1 / 80000 := by
    intro t ht ht0
    have hsub : Set.Icc 0 t ⊆ I := hIc 0 h0I t ht
    have hmaps := MathlibExt.Analysis.ODE.finite_interval_mapsTo_sublevel
      (V := longitudinalLyapunov) (f := fun _ y => nonlinearReducedField y) (c := 1 / 80000) ht0
      (differentiable_longitudinalLyapunov.continuous.comp_continuousOn
        (fun s hs => (hsol s (hsub hs)).2.continuousAt.continuousWithinAt))
      (fun s hs => (hsol s (hsub (Set.Ioo_subset_Icc_self hs))).2)
      (fun _ _ => differentiable_longitudinalLyapunov _)
      (fun s hs => by
        have hU' := (hsol s (hsub (Set.Ioo_subset_Icc_self hs))).1.2
        have hn : ‖x s‖ ≤ 1 / 100 := (mem_ball_zero_iff.1 hU').le
        nlinarith [(fderiv_longitudinalLyapunov_nonlinearReducedField_le hn).1,
          sq_nonneg ‖x s‖])
      (by rw [hx0]; exact hball e₀ he₀)
    exact hmaps ⟨ht0, le_rfl⟩
  have hIci : Set.Ici 0 ⊆ I := by
    intro T hT
    by_contra hTI
    have hlt : ∀ t ∈ I, t < T := fun t ht =>
      lt_of_not_ge fun h => hTI (hIc 0 h0I t ht ⟨hT, h⟩)
    have hKc : IsCompact (Set.Icc 0 T ×ˢ {y : EuclideanSpace ℝ (Fin 4) |
        longitudinalLyapunov y ≤ 1 / 80000}) := isCompact_Icc.prod hK
    have hKU : Set.Icc 0 T ×ˢ {y : EuclideanSpace ℝ (Fin 4) |
        longitudinalLyapunov y ≤ 1 / 80000} ⊆ U := fun p hp =>
      ⟨trivial, mem_ball_zero_iff.2 (by nlinarith [(hin _ hp.2).1, norm_nonneg p.2])⟩
    obtain ⟨c, hcI, hc⟩ := (hexit _ hKc hKU).1
    have htI : max c 0 ∈ I := by
      rcases max_choice c 0 with h | h <;> rw [h]
      · exact hcI
      · exact h0I
    exact hc (max c 0) htI (le_max_left _ _)
      ⟨⟨le_max_right _ _, (hlt _ htI).le⟩, hinv _ htI (le_max_right _ _)⟩
  exact ⟨x, hx0, fun t ht => (hsol t (hIci ht)).2.hasDerivWithinAt,
    fun t ht => (hin _ (hinv t (hIci ht) ht)).2⟩

/-- **Local existence and decay.** For every initial state `e₀` with `‖e₀‖ ≤ r / 4 = 1/400`
there is a forward solution `e` of the nonlinear reduced field on `[0, ∞)`, `e 0 = e₀`, whose
coordinates stay in the actuator box and which satisfies `‖e t‖ ≤ √8 * exp (-t / 8) * ‖e₀‖` for
every `t ≥ 0`. -/
lemma nonlinearReducedField_solution_decay (e₀ : EuclideanSpace ℝ (Fin 4))
    (he₀ : ‖e₀‖ ≤ 1 / 400) :
    ∃ e : ℝ → EuclideanSpace ℝ (Fin 4), e 0 = e₀ ∧
      IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0) ∧
      ∀ t, 0 ≤ t → WithLp.ofLp (e t) ∈ actuatorBox ∧
        ‖e t‖ ≤ Real.sqrt 8 * Real.exp (-t / 8) * ‖e₀‖ := by
  obtain ⟨e, h0, he, hbox⟩ := exists_nonlinearReducedField_solution e₀ he₀
  refine ⟨e, h0, he, fun t ht => ⟨hbox t ht, ?_⟩⟩
  rw [← h0]
  exact norm_le_of_isIntegralCurveOn_nonlinearReducedField he (h0 ▸ he₀) ht

end Mechanics.FlightPlant
