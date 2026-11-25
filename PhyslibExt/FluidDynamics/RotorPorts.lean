/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Order.Interval.Set.Defs
public import PhyslibExt.ContinuumMechanics.ControlVolumes
public import PhyslibExt.Thermodynamics.ProcessPorts
public import PhyslibExt.Units.EngineeringFrames

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rotor ports: Euler torque and power on the fluid, the ideal actuator disk and hover

Two lumped rotor models: the Euler turbomachine relation for a rotor with lumped ports (sections
A-C), and the ideal actuator disk of one-dimensional momentum theory with the Betz limit
(sections D-F) and the hovering rotor (section G).

## i. Overview

A rotor turns about a fixed shaft axis through the point `o` along the third inertial axis
`e₃`, at the signed angular speed `ω` (positive counterclockwise about `e₃`). Steady flow enters
its control volume through one port and leaves through another. The ports are lumped, as in the
meanline description of a turbomachine: a port is its flow state at one representative point, of
azimuth `φ`, radius `r` and axial station `z`, with the port area `A`; no surface integral over a
port is taken. In the local cylindrical frame at the representative point, the rotation
`rotZ φ` by `φ` about `e₃` of `PhyslibExt.Units.EngineeringFrames`, the inertial fluid velocity
has the components `(c_r, c_θ, c_z)` and the outward unit normal the meridional components
`(n_r, 0, n_z)`. The lumped mass flow is `ṁ_out = ρ A (c ⬝ n)`, positive out of the control
volume, and the area-weighted local momentum flux is `ṁ_out c + p A n`: the port area times the
momentum flux of `PhyslibExt.ContinuumMechanics.ControlVolumes` at the representative point, with
the pressure-only stress `σ = -p 1`, taken through the outward normal. It is a local value, not
the vector momentum outflow of a port surface: over a band of revolution with radial velocity and
normal that outflow integrates `e_r` over the azimuth, and over a full band it vanishes.

The axial moment about `o` of the area-weighted local momentum flux is `ṁ_out r c_θ`: the
pressure term `p A n` has no axial moment, because the outward normal lies in the meridional
plane, and neither the azimuth nor the axial station enters. The steady angular-momentum balance
about the shaft, a model input, is applied to these lumped port values, so `r` is an effective
moment radius: the radius for which `ṁ_out r c_θ` is the port's angular-momentum outflow. For
uniform data on a band of constant radius it is that radius; across an annulus the radius varies
and `r` is an average fixed by the model. The balance states that the axial torque `τ` exerted on
the fluid by the rotor plus every other external axial moment `M_ext` equals the lumped axial
angular-momentum flux of the two ports. With the steady mass balance (lumped mass flows `-ṁ` at
the inlet and `ṁ` at the outlet) it gives the Euler torque on the fluid
`τ = ṁ (r₂ c_θ₂ - r₁ c_θ₁) - M_ext`.

When the rotor torque is exerted by forces `F_k` on the fluid at points `x_k` of the rotor, each
moving with the rotor velocity `ω e₃ ⨯₃ (x_k - o)`, the power of these forces is `ω τ`, so with
`M_ext = 0` the power on the fluid is `P = ω τ = ṁ (U₂ c_θ₂ - U₁ c_θ₁)` with the signed blade
speeds `U = ω r`. If the rotor turns steadily without bearing torque, the shaft torque on it
balances the reaction `-τ` of the fluid; the shaft torque is then `τ` and the engineering shaft
power out, `workOut (ω τ_shaft)`, is `-P`. With `ṁ > 0` a compressor or pump has
`U₁ c_θ₁ < U₂ c_θ₂` (`P > 0`, shaft power absorbed) and a turbine has `U₂ c_θ₂ < U₁ c_θ₁`
(positive shaft power out). Every power and shaft-power result states these force and shaft
hypotheses. The swirl in these formulas is the inertial one: the fluid velocity relative to the
rotor has the tangential component `c_θ - ω r`.

Model inputs of sections A-C: steady flow; one inlet and one outlet port, each lumped at one
representative point with a nonnegative density, port area and effective moment radius and a unit
normal; the steady mass and angular-momentum balances about the shaft applied to the lumped port
values, with every external axial moment other than the rotor torque collected in `M_ext`; for the
power, the rotor torque exerted by forces at points moving with the rigid rotor, and `M_ext = 0`;
for the shaft power, a steadily turning rotor with no bearing torque. No port-surface integral,
blade-element, loss, slip or performance-map model is used, and no empirical adequacy or machine
safety claim is made.

The actuator disk of sections D-F. An ideal actuator disk of area `A` stands normal to a steady
incompressible stream of density `ρ`. Axial speeds are positive along the flow: `U∞` far upstream,
`U_d` at the disk (the same on both faces of the thin disk, by continuity) and `U_w` in the far
wake. The static pressure is the ambient `p∞` far upstream and in the far wake, `p⁺` on the upstream
face and `p⁻` on the downstream face of the disk; `T` is the axial force of the fluid on the disk,
positive along the flow. The port laws, the model inputs, are Bernoulli separately on the two sides
of the disk, `p∞ + ρ U∞² / 2 = p⁺ + ρ U_d² / 2` and `p⁻ + ρ U_d² / 2 = p∞ + ρ U_w² / 2`, the
momentum balance of the thin disk, `T = A (p⁺ - p⁻)`, and the momentum balance of the streamtube
through it, `T = ṁ (U∞ - U_w)` with the mass flow `ṁ = ρ A U_d`. Bernoulli is not applied across the
disk, where the pressure jumps.

Bernoulli on the two sides gives the pressure jump `p⁺ - p⁻ = ρ (U∞² - U_w²) / 2`; with the two
momentum balances, `ρ A (U∞ - U_w) (U_d - (U∞ + U_w) / 2) = 0`, so `U_d = (U∞ + U_w) / 2`
whenever the wake speed differs from the freestream speed. On the extraction side `0 ≤ U_w < U∞`,
the wind-extraction branch below together with its wake-degenerate endpoint `U_w = 0`, the total
pressure drops across the disk by `ρ (U∞² - U_w²) / 2 > 0`, which is why Bernoulli cannot be applied
across it. The extracted power `T U_d` equals the loss of kinetic
power `ṁ (U∞² - U_w²) / 2`. With the axial induction factor `a = 1 - U_d / U∞` (`U∞ > 0`),
`U_d = (1 - a) U∞`, `U_w = (1 - 2 a) U∞` and, normalized by the freestream kinetic power through
the disk area `ρ A U∞³ / 2`, the power coefficient is `C_P = 4 a (1 - a)²`. Since
`16/27 - 4 a (1 - a)² = 4 (a - 1/3)² (4/3 - a)`, on `0 ≤ a < 1/2` `C_P ≤ 16/27`, with equality
exactly at `a = 1/3`, the Betz limit. The wind-extraction branch `0 < U_w < U∞` is
`0 < a < 1/2`. Its endpoints are limits of the branch: the zero-extraction limit `a → 0`
(`U_w → U∞`, where the force tends to zero) and the wake-degenerate limit `a → 1/2` (`U_w → 0`),
which the extraction side includes. `U∞ = 0` is not a valid normalization: the hovering rotor is a
separate branch.

Model inputs of sections D-F: steady incompressible inviscid flow through an ideal disk of uniform
loading, with no swirl and no tip loss; ambient pressure far upstream and in the far wake; no net
axial pressure force on the streamtube boundary. No blade-element, wake-rotation or turbulent-wake
model is used, and no empirical adequacy or turbine safety claim is made.

The hovering rotor of section G is the same ideal actuator-disk model, on the separate hover
branch: the same state and the same port laws, in still air. Axial speeds are
positive along the flow through the disk: the far-upstream speed is `U∞ = 0`, the induced velocity
is the speed `v_i = U_d` at the disk and `U_w` is the far-wake speed. The port laws are Bernoulli
separately on the two sides of the disk, `p∞ + ρ U∞² / 2 = p⁺ + ρ v_i² / 2` and
`p⁻ + ρ v_i² / 2 = p∞ + ρ U_w² / 2`, the momentum balance of the thin disk, `F = A (p⁺ - p⁻)`, and
the momentum balance of the streamtube, `F = ρ A v_i (U∞ - U_w)`, where `F` is the axial force of
the fluid on the disk, positive along the flow. A powered disk pushes the fluid along the flow, so
`F < 0`, and the rotor thrust is `T = -F > 0`, directed against the flow (upward for a rotor blowing
downward).

With `U∞ = 0`, Bernoulli on the two sides gives `F = -ρ A U_w² / 2` and the streamtube gives
`F = -ρ A v_i U_w`; a nonzero force makes `U_w ≠ 0`, so `U_w = 2 v_i`. Then `T = 2 ρ A v_i²`.
The induced power, the kinetic power `ṁ (U_w² - U∞²) / 2` that the disk adds to the stream
(`ṁ = ρ A v_i`), is the negative of the extracted power for every state satisfying the port laws,
`P = T v_i`, the power `-F v_i` of the disk on the stream, with no still-air, sign or powered
assumption. A powered disk
delivers positive power, `T v_i > 0`; then `v_i > 0`, so the far wake moves at
`U_w = 2 v_i > U∞ = 0`, outside the wind-extraction branch, which has `U_w < U∞`, and
`v_i = √(T / (2 ρ A))` and `P = T √(T / (2 ρ A))`. The port laws do not change when every speed
changes sign, and the reversed state takes power from the stream instead, so the powered
hypothesis cannot be dropped. The
freestream normalization `ρ A U∞³ / 2` of the wind-extraction power coefficient vanishes at
`U∞ = 0`, so no such coefficient describes hover.

Model inputs of section G: steady incompressible inviscid flow through an ideal disk of uniform
loading in still air, with no swirl and no tip loss; ambient pressure far upstream and in the far
wake; no net axial pressure force on the streamtube boundary. No blade-element, vortex-ring, stall
or motor model is used, and no empirical adequacy or vehicle safety claim is made.

## ii. Key results

- `FluidDynamics.RotorPorts.localMomentumFlux_eq_momentumFlux`: the area-weighted local momentum
  flux of a port is the area times the momentum flux through the outward normal.
- `FluidDynamics.RotorPorts.axialMomentFlux_eq`: the lumped axial angular-momentum flux of a port
  is `ṁ_out r c_θ`.
- `FluidDynamics.RotorPorts.torqueOnFluid_eq`: the Euler torque on the fluid.
- `FluidDynamics.RotorPorts.rotorPower_eq`, `FluidDynamics.RotorPorts.powerOnFluid_eq`: the power
  of rotor forces on the fluid is `ω τ = ṁ (U₂ c_θ₂ - U₁ c_θ₁)`.
- `FluidDynamics.RotorPorts.shaftPowerOut_eq`: the shaft power out of a steadily turning rotor is
  its negative.
- `FluidDynamics.RotorPorts.torqueOnFluid_eq_zero_of_specificAngularMomentum_eq`: equal specific
  axial angular momentum `r c_θ` at both ports, no torque, power or shaft power.
- `FluidDynamics.RotorPorts.compressor_iff`, `FluidDynamics.RotorPorts.turbine_iff`: the
  compressor and turbine signs of the power and the shaft power.
- `FluidDynamics.RotorPorts.relativeSwirl_eq`: the swirl relative to the rotor is `c_θ - ω r`.
- `FluidDynamics.RotorPorts.ActuatorDisk.PortLaws`: the four port laws of the ideal actuator disk.
- `FluidDynamics.RotorPorts.pressureJump_eq`, `FluidDynamics.RotorPorts.uDisk_eq`: the pressure
  jump and `U_d = (U∞ + U_w) / 2`.
- `FluidDynamics.RotorPorts.extractedPower_eq`, `FluidDynamics.RotorPorts.totalPressure_drop`:
  the energy reading of the jump, and the total-pressure drop across the disk.
- `FluidDynamics.RotorPorts.powerCoefficient_eq`, `FluidDynamics.RotorPorts.betz_bound`,
  `FluidDynamics.RotorPorts.powerCoefficient_le_betz`: `C_P = 4 a (1 - a)² ≤ 16/27`, equality at
  `a = 1/3`.
- `FluidDynamics.RotorPorts.ofInduction_spec`: every induction factor is realized by a state
  satisfying the port laws.
- `FluidDynamics.RotorPorts.hover_uWake_eq`, `FluidDynamics.RotorPorts.hover_thrust_eq`: in
  still air the far wake moves at `U_w = 2 v_i` and `T = 2 ρ A v_i²`.
- `FluidDynamics.RotorPorts.inducedPower_eq`: for every state satisfying the port laws the induced
  power is the negative of the extracted power, `-F U_d`, or `T U_d` with the thrust `T = -F`.
- `FluidDynamics.RotorPorts.hover_inducedVelocity_eq`, `FluidDynamics.RotorPorts.hover_power_eq`:
  for a powered disk `v_i = √(T / (2 ρ A))`, and the induced power is `T v_i = -F v_i`.
- A compressor with a nonzero swirl change, the same ports with the throughflow reversed, blade
  forces that realize their torques and the rotor-relative swirl of the ports, and the
  Betz-optimal disk, the invalid zero freestream and the undetermined disk speed without
  extraction, and nonzero hover thrust and power, the undefined freestream normalization in hover
  and the reversed unpowered state, are checked in `PhyslibExtTest.FluidDynamics.RotorPorts`.

## iii. Table of contents

- A. Lumped ports about the shaft
- B. The Euler torque on the fluid
- C. Power on the fluid and shaft power out
- D. The actuator disk and its port laws
- E. Disk speed and pressure jump
- F. Power coefficient and the Betz limit
- G. The hovering rotor

## iv. References

- S. L. Dixon and C. A. Hall, *Fluid Mechanics and Thermodynamics of Turbomachinery*,
  Butterworth-Heinemann, ch. 2: the moment of momentum and the Euler work equation
  `τ = ṁ (r₂ c_θ₂ - r₁ c_θ₁)`, `Ẇ = ṁ (U₂ c_θ₂ - U₁ c_θ₁)` for compressors and turbines.
- F. M. White, *Fluid Mechanics*, McGraw-Hill, ch. 3 (the angular-momentum relation for a fixed
  control volume) and ch. 11 (turbomachinery: the Euler turbomachine equation).
- Y. A. Çengel and J. M. Cimbala, *Fluid Mechanics: Fundamentals and Applications*,
  McGraw-Hill, ch. 6 (the angular-momentum equation and radial-flow devices).
- A. Betz, *Das Maximum der theoretisch möglichen Ausnützung des Windes durch Windmotoren*,
  Zeitschrift für das gesamte Turbinenwesen 26 (1920): the limit `16/27`.
- J. F. Manwell, J. G. McGowan and A. L. Rogers, *Wind Energy Explained*, Wiley, ch. 3: the
  one-dimensional momentum theory of the ideal rotor, Bernoulli upstream and downstream of the
  disk, the induction factor and `C_P = 4 a (1 - a)²`.
- T. Burton, N. Jenkins, D. Sharpe and E. Bossanyi, *Wind Energy Handbook*, Wiley, ch. 3: the
  actuator disk concept and the Betz limit.
- J. G. Leishman, *Principles of Helicopter Aerodynamics*, Cambridge University Press, ch. 2:
  momentum theory of the hovering rotor, `T = 2 ρ A v_i²`, `v_i = √(T / (2 ρ A))`, the far wake
  at `2 v_i` and the ideal power `T v_i`.
- W. Johnson, *Helicopter Theory*, Princeton University Press, ch. 2: actuator disk momentum
  theory in hover.
-/

@[expose] public section

open scoped Matrix

namespace FluidDynamics.RotorPorts

open Units.EngineeringFrames

/-! ## A. Lumped ports about the shaft -/

/-- The unit vector `e₃` of the shaft axis, the third inertial axis. -/
def shaftAxis : Fin 3 → ℝ := ![0, 0, 1]

/-- The local cylindrical frame at azimuth `φ` about the shaft: the rotation by `φ` about the third
axis, whose columns are the radial, tangential and axial unit vectors `e_r = (cos φ, sin φ, 0)`,
`e_θ = (-sin φ, cos φ, 0)` and `e₃`. -/
noncomputable def cylFrame (φ : ℝ) : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨rotZ φ, rotZ_mem_specialOrthogonalGroup φ⟩

/-- A lumped (meanline) port of a rotor control volume: the flow state at one representative
point of azimuth `φ`, radius `r` and axial station `z`, with the port area `A`. No port surface is
modelled, and `r` is the port's effective moment radius (see `axialMomentFlux`). In the local
cylindrical frame at the representative point the inertial fluid velocity has the components
`(cr, cθ, cz)`, so `cθ` is the inertial swirl velocity, positive along `e_θ`, and the outward
unit normal has the meridional components `(nr, 0, nz)`, `nr ^ 2 + nz ^ 2 = 1`. The density `ρ`,
the area `A` and the radius `r` are nonnegative. -/
structure RotorPort where
  /-- The density `ρ`. -/
  ρ : ℝ
  /-- The port area `A`. -/
  A : ℝ
  /-- The static pressure `p`. -/
  p : ℝ
  /-- The azimuth `φ` of the representative point. -/
  φ : ℝ
  /-- The radius `r` of the representative point, the effective moment radius of the port. -/
  r : ℝ
  /-- The axial station `z` of the representative point. -/
  z : ℝ
  /-- The radial component of the inertial velocity. -/
  cr : ℝ
  /-- The tangential (swirl) component of the inertial velocity. -/
  cθ : ℝ
  /-- The axial component of the inertial velocity. -/
  cz : ℝ
  /-- The radial component of the outward unit normal. -/
  nr : ℝ
  /-- The axial component of the outward unit normal. -/
  nz : ℝ
  /-- The outward normal is a unit vector. -/
  normal_unit : nr ^ 2 + nz ^ 2 = 1
  /-- The density is nonnegative. -/
  ρ_nonneg : 0 ≤ ρ
  /-- The port area is nonnegative. -/
  A_nonneg : 0 ≤ A
  /-- The radius is nonnegative: the representative point lies on the radial ray `e_r` of its
  azimuth, the direction of the radial components of the velocity and the normal. -/
  r_nonneg : 0 ≤ r

namespace RotorPort

/-- The inertial position `o + r e_r + z e₃` of the representative point, for the origin `o` of
the shaft axis. -/
noncomputable def point (o : Fin 3 → ℝ) (P : RotorPort) : Fin 3 → ℝ :=
  bodyToInertial o (cylFrame P.φ) ![P.r, 0, P.z]

/-- The inertial velocity `cr e_r + cθ e_θ + cz e₃` at the representative point. -/
noncomputable def velocity (P : RotorPort) : Fin 3 → ℝ :=
  bodyToInertialVec (cylFrame P.φ) ![P.cr, P.cθ, P.cz]

/-- The outward unit normal `nr e_r + nz e₃` at the representative point. -/
noncomputable def normal (P : RotorPort) : Fin 3 → ℝ :=
  bodyToInertialVec (cylFrame P.φ) ![P.nr, 0, P.nz]

/-- The lumped mass flow `ρ A (c ⬝ n)`: the local mass flux through the outward normal at the
representative point times the port area. As `ρ` and `A` are nonnegative, it is nonnegative for
flow out of the control volume (`c ⬝ n ≥ 0`) and nonpositive for flow into it, strictly when
`ρ A > 0`. -/
noncomputable def lumpedMassFlow (P : RotorPort) : ℝ :=
  P.ρ * P.A * (P.velocity ⬝ᵥ P.normal)

/-- The area-weighted local momentum flux `ṁ c + p A n`, with `ṁ` the lumped mass flow: the port
area times the convective-plus-pressure momentum flux through the outward normal at the
representative point. A local value, not the vector momentum outflow of a port surface. -/
noncomputable def localMomentumFlux (P : RotorPort) : Fin 3 → ℝ :=
  P.lumpedMassFlow • P.velocity + (P.p * P.A) • P.normal

end RotorPort

/-- Every cylindrical frame fixes the shaft axis. -/
private lemma bodyToInertialVec_shaftAxis (φ : ℝ) :
    bodyToInertialVec (cylFrame φ) ![0, 0, 1] = shaftAxis := by
  ext i
  fin_cases i <;>
    simp [bodyToInertialVec, cylFrame, rotZ, shaftAxis, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- The lumped axial angular-momentum flux of a port about the shaft: the moment
`(x - o) ⨯₃ (ṁ c + p A n)` of its area-weighted local momentum flux about the point `o` of the
shaft axis, projected on `e₃`, at the representative point `x`. It does not depend on the azimuth
or the station of `x` (`axialMomentFlux_eq`); the lumped angular-momentum balance uses it as the
port's angular-momentum outflow, which makes the radius of `x` an effective moment radius. -/
noncomputable def axialMomentFlux (o : Fin 3 → ℝ) (P : RotorPort) : ℝ :=
  shaftAxis ⬝ᵥ ((P.point o - o) ⨯₃ P.localMomentumFlux)

/-- **The local momentum flux is the momentum flux of the control-volume module.** The
area-weighted local momentum flux `ṁ c + p A n` is the port area times the momentum flux of the
state at the representative point (as constant fields, so the evaluation point `x` is immaterial)
with the pressure-only stress `σ = -p 1`, taken through the outward normal. -/
lemma localMomentumFlux_eq_momentumFlux (P : RotorPort) (x : Fin 3 → ℝ) :
    P.localMomentumFlux = P.A • fun j : Fin 3 => ∑ i : Fin 3,
      ControlVolumes.momentumFlux (n := 2) (fun _ => P.ρ) (fun _ => P.velocity)
        (fun _ => -(P.p • (1 : Matrix (Fin 3) (Fin 3) ℝ))) j x i * P.normal i := by
  ext j
  simp only [RotorPort.localMomentumFlux, RotorPort.lumpedMassFlow, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  fin_cases j <;>
    simp [ControlVolumes.momentumFlux, Matrix.vec3_dotProduct, Fin.sum_univ_three,
      Matrix.one_apply] <;>
    ring

/-- The normal velocity is frame independent: the lumped mass flow is `ρ A (cr nr + cz nz)`. -/
lemma lumpedMassFlow_eq (P : RotorPort) :
    P.lumpedMassFlow = P.ρ * P.A * (P.cr * P.nr + P.cz * P.nz) := by
  simp only [RotorPort.lumpedMassFlow, RotorPort.velocity, RotorPort.normal,
    bodyToInertialVec_dotProduct, Matrix.vec3_dotProduct']
  ring

/-- **Lumped axial angular-momentum flux.** About the point `o` of the shaft axis the lumped axial
angular-momentum flux of a port is `ṁ r cθ`. The pressure term `p A n` has no axial moment, since
the outward normal lies in the meridional plane, and neither the azimuth `φ` nor the axial station
`z` of the representative point enters. -/
lemma axialMomentFlux_eq (o : Fin 3 → ℝ) (P : RotorPort) :
    axialMomentFlux o P = P.lumpedMassFlow * (P.r * P.cθ) := by
  have hmom : P.localMomentumFlux = bodyToInertialVec (cylFrame P.φ)
      (P.lumpedMassFlow • ![P.cr, P.cθ, P.cz] + (P.p * P.A) • ![P.nr, 0, P.nz]) := by
    simp only [RotorPort.localMomentumFlux, RotorPort.velocity, RotorPort.normal,
      bodyToInertialVec, Matrix.mulVec_add, Matrix.mulVec_smul]
  simp only [axialMomentFlux, RotorPort.point]
  rw [(bodyToInertialVec_shaftAxis P.φ).symm, hmom, ← bodyToInertialVec_moment,
    bodyToInertialVec_dotProduct]
  simp only [cross_apply, Matrix.vec3_dotProduct', Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## B. The Euler torque on the fluid -/

/-- **Euler torque on the fluid.** Model inputs: steady flow through a rotor control volume with
one inlet and one outlet lumped port; the steady mass balance, lumped mass flows `-ṁ` at the inlet
and `ṁ` at the outlet; and the steady angular-momentum balance about the shaft applied to the
lumped ports: the axial torque `τ` exerted on the fluid by the rotor plus every other external
axial moment `M_ext` equals the lumped axial angular-momentum flux of the two ports. Then
`τ = ṁ (r₂ cθ₂ - r₁ cθ₁) - M_ext`. -/
lemma torqueOnFluid_eq {o : Fin 3 → ℝ} {inlet outlet : RotorPort} {mdot τ Mext : ℝ}
    (hin : inlet.lumpedMassFlow = -mdot) (hout : outlet.lumpedMassFlow = mdot)
    (hbal : τ + Mext = axialMomentFlux o inlet + axialMomentFlux o outlet) :
    τ = mdot * (outlet.r * outlet.cθ - inlet.r * inlet.cθ) - Mext := by
  rw [axialMomentFlux_eq, axialMomentFlux_eq, hin, hout] at hbal
  linear_combination hbal

/-! ## C. Power on the fluid and shaft power out -/

/-- The axial torque about the shaft of forces `F k` exerted on the fluid at the points `x k`. -/
noncomputable def axialTorque {ι : Type*} [Fintype ι] (o : Fin 3 → ℝ) (x F : ι → Fin 3 → ℝ) :
    ℝ :=
  shaftAxis ⬝ᵥ ∑ k, (x k - o) ⨯₃ F k

/-- The power of forces `F k` exerted on the fluid at the points `x k` of a rotor turning at the
signed angular speed `ω` about the shaft axis through `o`: the point `x k` moves with the rotor
velocity `ω e₃ ⨯₃ (x k - o)`. -/
noncomputable def rotorPower {ι : Type*} [Fintype ι] (ω : ℝ) (o : Fin 3 → ℝ)
    (x F : ι → Fin 3 → ℝ) : ℝ :=
  ∑ k, F k ⬝ᵥ (ω • (shaftAxis ⨯₃ (x k - o)))

/-- **The power on the fluid is `ω τ`.** Forces exerted on the fluid at points of a rotor turning
at `ω` about the shaft deliver the power `ω` times their axial torque. -/
lemma rotorPower_eq {ι : Type*} [Fintype ι] (ω : ℝ) (o : Fin 3 → ℝ) (x F : ι → Fin 3 → ℝ) :
    rotorPower ω o x F = ω * axialTorque o x F := by
  simp only [rotorPower, axialTorque, dotProduct_smul, triple_product_permutation,
    smul_eq_mul, Finset.mul_sum, dotProduct_sum]

/-- **Euler torque and power on the fluid.** If the rotor torque on the fluid is exerted by forces
at points moving with the rotor, no other external moment acts and the steady lumped mass and
angular-momentum balances hold, the torque on the fluid is `τ = ṁ (r₂ cθ₂ - r₁ cθ₁)` and the
power on the fluid is `P = ω τ = ṁ (U₂ cθ₂ - U₁ cθ₁)` with the signed blade speeds `U = ω r`. -/
lemma powerOnFluid_eq {ι : Type*} [Fintype ι] {ω : ℝ} {o : Fin 3 → ℝ} {x F : ι → Fin 3 → ℝ}
    {inlet outlet : RotorPort} {mdot : ℝ}
    (hin : inlet.lumpedMassFlow = -mdot) (hout : outlet.lumpedMassFlow = mdot)
    (hbal : axialTorque o x F = axialMomentFlux o inlet + axialMomentFlux o outlet) :
    axialTorque o x F = mdot * (outlet.r * outlet.cθ - inlet.r * inlet.cθ) ∧
      rotorPower ω o x F = ω * axialTorque o x F ∧
      rotorPower ω o x F = mdot * (ω * outlet.r * outlet.cθ - ω * inlet.r * inlet.cθ) := by
  have htorq := torqueOnFluid_eq (Mext := 0) hin hout (by simpa using hbal)
  rw [sub_zero] at htorq
  refine ⟨htorq, rotorPower_eq ω o x F, ?_⟩
  rw [rotorPower_eq, htorq]
  ring

/-- **Shaft power out is the negative of the power on the fluid.** Model inputs: the rotor torque
on the fluid is exerted by forces `F k` at points `x k` moving with the rotor, with the steady
lumped balances of `powerOnFluid_eq`; the rotor turns steadily, so the axial torques on it balance,
`τ_shaft + τ_reaction = 0` (no bearing torque), and the fluid reacts on the rotor with
`τ_reaction = -τ`, `τ` the axial torque of those forces. Then the shaft torque on the rotor is
`τ`, and the engineering shaft power out `workOut (ω τ_shaft)` is minus the power of the forces on
the fluid, `ṁ (U₁ cθ₁ - U₂ cθ₂)`. -/
lemma shaftPowerOut_eq {ι : Type*} [Fintype ι] {ω : ℝ} {o : Fin 3 → ℝ} {x F : ι → Fin 3 → ℝ}
    {inlet outlet : RotorPort} {mdot τShaft τReaction : ℝ}
    (hin : inlet.lumpedMassFlow = -mdot) (hout : outlet.lumpedMassFlow = mdot)
    (hbal : axialTorque o x F = axialMomentFlux o inlet + axialMomentFlux o outlet)
    (hrotor : τShaft + τReaction = 0) (hreact : τReaction = -axialTorque o x F) :
    τShaft = axialTorque o x F ∧ ProcessPorts.workOut (ω * τShaft) = -rotorPower ω o x F ∧
      ProcessPorts.workOut (ω * τShaft) =
        mdot * (ω * inlet.r * inlet.cθ - ω * outlet.r * outlet.cθ) := by
  have hS : τShaft = axialTorque o x F := by linarith
  obtain ⟨htorq, hpow, -⟩ := powerOnFluid_eq (ω := ω) hin hout hbal
  refine ⟨hS, by simp only [hpow, hS, ProcessPorts.workOut], ?_⟩
  simp only [hS, htorq, ProcessPorts.workOut]
  ring

/-- **Equal specific angular momentum.** If the inlet and outlet carry the same specific axial
angular momentum (axial angular momentum per unit mass), `r₁ cθ₁ = r₂ cθ₂`, the rotor torque on the
fluid is exerted by forces at points moving with the rotor, no other external moment acts and the
steady lumped balances hold, then the torque of those forces on the fluid and their power vanish,
for every throughflow and every rotor speed, and a steadily turning rotor without bearing torque
has no shaft power out. The swirl velocities themselves may differ: only `r cθ` enters. -/
lemma torqueOnFluid_eq_zero_of_specificAngularMomentum_eq {ι : Type*} [Fintype ι] {ω : ℝ}
    {o : Fin 3 → ℝ} {x F : ι → Fin 3 → ℝ} {inlet outlet : RotorPort} {mdot τShaft τReaction : ℝ}
    (hin : inlet.lumpedMassFlow = -mdot) (hout : outlet.lumpedMassFlow = mdot)
    (hbal : axialTorque o x F = axialMomentFlux o inlet + axialMomentFlux o outlet)
    (hangMom : inlet.r * inlet.cθ = outlet.r * outlet.cθ)
    (hrotor : τShaft + τReaction = 0) (hreact : τReaction = -axialTorque o x F) :
    axialTorque o x F = 0 ∧ rotorPower ω o x F = 0 ∧ ProcessPorts.workOut (ω * τShaft) = 0 := by
  obtain ⟨htorq, hpow, -⟩ := powerOnFluid_eq (ω := ω) hin hout hbal
  obtain ⟨-, hshaft, -⟩ := shaftPowerOut_eq (ω := ω) hin hout hbal hrotor hreact
  have h0 : axialTorque o x F = 0 := by rw [htorq, hangMom, sub_self, mul_zero]
  exact ⟨h0, by rw [hpow, h0, mul_zero], by rw [hshaft, hpow, h0, mul_zero, neg_zero]⟩

/-- **Compressor or pump sign.** With positive throughflow `ṁ > 0`, the rotor torque on the fluid
exerted by forces at points moving with the rotor, the steady lumped balances, and a steadily
turning rotor without bearing torque: the power of those forces on the fluid is positive, and the
shaft power out negative, exactly when `U₁ cθ₁ < U₂ cθ₂`. -/
lemma compressor_iff {ι : Type*} [Fintype ι] {ω : ℝ} {o : Fin 3 → ℝ} {x F : ι → Fin 3 → ℝ}
    {inlet outlet : RotorPort} {mdot τShaft τReaction : ℝ} (hm : 0 < mdot)
    (hin : inlet.lumpedMassFlow = -mdot) (hout : outlet.lumpedMassFlow = mdot)
    (hbal : axialTorque o x F = axialMomentFlux o inlet + axialMomentFlux o outlet)
    (hrotor : τShaft + τReaction = 0) (hreact : τReaction = -axialTorque o x F) :
    (0 < rotorPower ω o x F ↔ ω * inlet.r * inlet.cθ < ω * outlet.r * outlet.cθ) ∧
      (ProcessPorts.workOut (ω * τShaft) < 0 ↔
        ω * inlet.r * inlet.cθ < ω * outlet.r * outlet.cθ) := by
  obtain ⟨-, -, hpow⟩ := powerOnFluid_eq (ω := ω) hin hout hbal
  obtain ⟨-, -, hshaft⟩ := shaftPowerOut_eq (ω := ω) hin hout hbal hrotor hreact
  have hpos : ∀ X : ℝ, (0 < mdot * X ↔ 0 < X) :=
    fun X => ⟨fun h => pos_of_mul_pos_right h hm.le, fun h => mul_pos hm h⟩
  have hneg : ∀ X : ℝ, (mdot * X < 0 ↔ X < 0) :=
    fun X => ⟨fun h => neg_of_mul_neg_right h hm.le, fun h => mul_neg_of_pos_of_neg hm h⟩
  rw [hpow, hshaft, hpos, hneg]
  constructor <;> constructor <;> intro h <;> linarith

/-- **Turbine sign.** With positive throughflow `ṁ > 0`, the rotor torque on the fluid exerted by
forces at points moving with the rotor, the steady lumped balances, and a steadily turning rotor
without bearing torque: the shaft power out is positive, and the power of those forces on the
fluid negative, exactly when `U₂ cθ₂ < U₁ cθ₁`. -/
lemma turbine_iff {ι : Type*} [Fintype ι] {ω : ℝ} {o : Fin 3 → ℝ} {x F : ι → Fin 3 → ℝ}
    {inlet outlet : RotorPort} {mdot τShaft τReaction : ℝ} (hm : 0 < mdot)
    (hin : inlet.lumpedMassFlow = -mdot) (hout : outlet.lumpedMassFlow = mdot)
    (hbal : axialTorque o x F = axialMomentFlux o inlet + axialMomentFlux o outlet)
    (hrotor : τShaft + τReaction = 0) (hreact : τReaction = -axialTorque o x F) :
    (0 < ProcessPorts.workOut (ω * τShaft) ↔
        ω * outlet.r * outlet.cθ < ω * inlet.r * inlet.cθ) ∧
      (rotorPower ω o x F < 0 ↔ ω * outlet.r * outlet.cθ < ω * inlet.r * inlet.cθ) := by
  obtain ⟨-, -, hpow⟩ := powerOnFluid_eq (ω := ω) hin hout hbal
  obtain ⟨-, -, hshaft⟩ := shaftPowerOut_eq (ω := ω) hin hout hbal hrotor hreact
  have hpos : ∀ X : ℝ, (0 < mdot * X ↔ 0 < X) :=
    fun X => ⟨fun h => pos_of_mul_pos_right h hm.le, fun h => mul_pos hm h⟩
  have hneg : ∀ X : ℝ, (mdot * X < 0 ↔ X < 0) :=
    fun X => ⟨fun h => neg_of_mul_neg_right h hm.le, fun h => mul_neg_of_pos_of_neg hm h⟩
  rw [hshaft, hpow, hpos, hneg]
  constructor <;> constructor <;> intro h <;> linarith

/-- **The swirl in Euler's formula is inertial.** At a port point the fluid velocity relative to
the rotor is `w = c - ω e₃ ⨯₃ (x - o)`; its tangential component is `cθ - ω r`, not the inertial
swirl `cθ`. -/
lemma relativeSwirl_eq (ω : ℝ) (o : Fin 3 → ℝ) (P : RotorPort) :
    (P.velocity - ω • (shaftAxis ⨯₃ (P.point o - o))) ⬝ᵥ
        bodyToInertialVec (cylFrame P.φ) ![0, 1, 0] = P.cθ - ω * P.r := by
  have hpoint : P.point o - o = bodyToInertialVec (cylFrame P.φ) ![P.r, 0, P.z] := by
    simp [RotorPort.point, bodyToInertial, bodyToInertialVec]
  rw [hpoint, (bodyToInertialVec_shaftAxis P.φ).symm, ← bodyToInertialVec_cross,
    RotorPort.velocity, sub_dotProduct, smul_dotProduct, bodyToInertialVec_dotProduct,
    bodyToInertialVec_dotProduct, smul_eq_mul]
  simp only [cross_apply, Matrix.vec3_dotProduct', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## D. The actuator disk and its port laws -/

/-- The state of an ideal actuator disk in a steady stream: density, disk area, axial speeds far
upstream, at the disk and in the far wake (positive along the flow), the ambient pressure, the
static pressures on the upstream and downstream faces of the disk, and the axial force of the
fluid on the disk, positive along the flow. -/
structure ActuatorDisk where
  /-- The density `ρ`. -/
  ρ : ℝ
  /-- The disk area `A`. -/
  A : ℝ
  /-- The far-upstream axial speed `U∞`. -/
  uInf : ℝ
  /-- The axial speed `U_d` at the disk. -/
  uDisk : ℝ
  /-- The far-wake axial speed `U_w`. -/
  uWake : ℝ
  /-- The ambient pressure `p∞`, far upstream and in the far wake. -/
  pAmb : ℝ
  /-- The static pressure `p⁺` on the upstream face of the disk. -/
  pUp : ℝ
  /-- The static pressure `p⁻` on the downstream face of the disk. -/
  pDown : ℝ
  /-- The axial force `T` of the fluid on the disk, positive along the flow. -/
  force : ℝ

namespace ActuatorDisk

/-- The port laws of the ideal actuator disk, the model inputs: Bernoulli separately upstream and
downstream of the disk (not across it), the momentum balance of the thin disk and the momentum
balance of the streamtube. -/
structure PortLaws (d : ActuatorDisk) : Prop where
  /-- Bernoulli from far upstream to the upstream face of the disk. -/
  bernoulli_up : d.pAmb + d.ρ * d.uInf ^ 2 / 2 = d.pUp + d.ρ * d.uDisk ^ 2 / 2
  /-- Bernoulli from the downstream face of the disk to the far wake. -/
  bernoulli_down : d.pDown + d.ρ * d.uDisk ^ 2 / 2 = d.pAmb + d.ρ * d.uWake ^ 2 / 2
  /-- Momentum balance of the thin disk: the force is the pressure jump times the area. -/
  momentum_disk : d.force = d.A * (d.pUp - d.pDown)
  /-- Momentum balance of the streamtube: the force is the mass flow `ρ A U_d` times the loss of
  axial speed. -/
  momentum_tube : d.force = d.ρ * d.A * d.uDisk * (d.uInf - d.uWake)

end ActuatorDisk

/-- The freestream kinetic power `ρ A U³ / 2` through the area `A`, the normalization of the power
coefficient. -/
noncomputable def powerNormalization (ρ A U : ℝ) : ℝ := ρ * A * U ^ 3 / 2

/-! ## E. Disk speed and pressure jump -/

/-- **Pressure jump from Bernoulli on each side.** The port laws give
`p⁺ - p⁻ = ρ (U∞² - U_w²) / 2` and the force `T = ρ A (U∞² - U_w²) / 2`. -/
lemma pressureJump_eq {d : ActuatorDisk} (h : d.PortLaws) :
    d.pUp - d.pDown = d.ρ * (d.uInf ^ 2 - d.uWake ^ 2) / 2 ∧
      d.force = d.ρ * d.A * (d.uInf ^ 2 - d.uWake ^ 2) / 2 := by
  have h1 : d.pUp - d.pDown = d.ρ * (d.uInf ^ 2 - d.uWake ^ 2) / 2 := by
    linear_combination (-1 : ℝ) * h.bernoulli_up - h.bernoulli_down
  refine ⟨h1, ?_⟩
  rw [h.momentum_disk, h1]
  ring

/-- **Disk speed.** With positive density and area, the port laws give `U_d = (U∞ + U_w) / 2`
whenever the wake speed differs from the freestream speed. -/
lemma uDisk_eq {d : ActuatorDisk} (h : d.PortLaws) (hρ : 0 < d.ρ) (hA : 0 < d.A)
    (hw : d.uWake ≠ d.uInf) : d.uDisk = (d.uInf + d.uWake) / 2 := by
  have hT := (pressureJump_eq h).2
  have key : d.ρ * d.A * (d.uInf - d.uWake) * (d.uDisk - (d.uInf + d.uWake) / 2) = 0 := by
    linear_combination hT - h.momentum_tube
  have hne : d.ρ * d.A * (d.uInf - d.uWake) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hρ.ne' hA.ne') (sub_ne_zero.mpr (Ne.symm hw))
  have h2 := (mul_eq_zero.mp key).resolve_left hne
  linarith

/-- The power `T U_d` extracted from the stream by the disk. -/
noncomputable def extractedPower (d : ActuatorDisk) : ℝ := d.force * d.uDisk

/-- **Energy reading of the pressure jump.** The extracted power is the loss of kinetic power of
the stream through the disk: `T U_d = ρ A U_d (U∞² - U_w²) / 2 = ṁ (U∞² - U_w²) / 2`. -/
lemma extractedPower_eq {d : ActuatorDisk} (h : d.PortLaws) :
    extractedPower d = d.ρ * d.A * d.uDisk * (d.uInf ^ 2 - d.uWake ^ 2) / 2 := by
  unfold extractedPower
  rw [(pressureJump_eq h).2]
  ring

/-- **No Bernoulli across the disk.** On the extraction side `0 ≤ U_w < U∞`, the wind-extraction
branch together with its wake-degenerate endpoint `U_w = 0`, with `ρ > 0`, the total pressure drops
across the disk by `ρ (U∞² - U_w²) / 2 > 0`, so Bernoulli applied across the pressure jump, which
would equate the two total pressures, contradicts extraction. -/
lemma totalPressure_drop {d : ActuatorDisk} (h : d.PortLaws) (hρ : 0 < d.ρ) (hw : 0 ≤ d.uWake)
    (hext : d.uWake < d.uInf) :
    (d.pUp + d.ρ * d.uDisk ^ 2 / 2) - (d.pDown + d.ρ * d.uDisk ^ 2 / 2) =
        d.ρ * (d.uInf ^ 2 - d.uWake ^ 2) / 2 ∧
      d.pDown + d.ρ * d.uDisk ^ 2 / 2 < d.pUp + d.ρ * d.uDisk ^ 2 / 2 := by
  have h1 := (pressureJump_eq h).1
  have hsq : 0 < d.uInf ^ 2 - d.uWake ^ 2 := by nlinarith
  have hpos : 0 < d.ρ * (d.uInf ^ 2 - d.uWake ^ 2) / 2 := div_pos (mul_pos hρ hsq) two_pos
  constructor
  · linarith
  · linarith

/-! ## F. Power coefficient and the Betz limit -/

/-- The axial induction factor `a = 1 - U_d / U∞`. -/
noncomputable def inductionFactor (d : ActuatorDisk) : ℝ := 1 - d.uDisk / d.uInf

/-- The power coefficient `C_P = T U_d / (ρ A U∞³ / 2)`, meaningful for `U∞ > 0` only. -/
noncomputable def powerCoefficient (d : ActuatorDisk) : ℝ :=
  extractedPower d / powerNormalization d.ρ d.A d.uInf

/-- **Power coefficient.** With `ρ, A, U∞ > 0` and `U_w ≠ U∞`, the port laws give
`C_P = 4 a (1 - a)²` for the axial induction factor `a = 1 - U_d / U∞`. -/
lemma powerCoefficient_eq {d : ActuatorDisk} (h : d.PortLaws) (hρ : 0 < d.ρ) (hA : 0 < d.A)
    (hU : 0 < d.uInf) (hw : d.uWake ≠ d.uInf) :
    powerCoefficient d = 4 * inductionFactor d * (1 - inductionFactor d) ^ 2 := by
  have hd := uDisk_eq h hρ hA hw
  unfold powerCoefficient extractedPower powerNormalization inductionFactor
  rw [h.momentum_tube, hd]
  field_simp
  ring

/-- **Betz bound.** For an induction factor `a ∈ [0, 1/2)`, `4 a (1 - a)² ≤ 16/27`, with equality
exactly at `a = 1/3`. -/
lemma betz_bound {a : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) (1 / 2)) :
    4 * a * (1 - a) ^ 2 ≤ 16 / 27 ∧ (4 * a * (1 - a) ^ 2 = 16 / 27 ↔ a = 1 / 3) := by
  have hfac : 16 / 27 - 4 * a * (1 - a) ^ 2 = 4 * (a - 1 / 3) ^ 2 * (4 / 3 - a) := by ring
  have h43 : 0 < 4 / 3 - a := by linarith [ha.2]
  have hnn : 0 ≤ 4 * (a - 1 / 3) ^ 2 * (4 / 3 - a) := by positivity
  refine ⟨by linarith, ⟨fun heq => ?_, fun ha3 => by rw [ha3]; norm_num⟩⟩
  have h0 : 4 * (a - 1 / 3) ^ 2 * (4 / 3 - a) = 0 := by linarith
  have hsq : (a - 1 / 3) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact h
    · linarith
  have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hsq
  linarith

/-- **Betz limit of the ideal wind turbine.** On the wind-extraction branch `0 < U_w < U∞`, with
positive density and area, the induction factor lies in `(0, 1/2)`, the power coefficient is at
most `16/27`, and it equals `16/27` exactly when `a = 1/3`. -/
lemma powerCoefficient_le_betz {d : ActuatorDisk} (h : d.PortLaws) (hρ : 0 < d.ρ)
    (hA : 0 < d.A) (hw : 0 < d.uWake) (hext : d.uWake < d.uInf) :
    0 < inductionFactor d ∧ inductionFactor d < 1 / 2 ∧ powerCoefficient d ≤ 16 / 27 ∧
      (powerCoefficient d = 16 / 27 ↔ inductionFactor d = 1 / 3) := by
  have hU : 0 < d.uInf := hw.trans hext
  have hd := uDisk_eq h hρ hA hext.ne
  have ha : inductionFactor d = (d.uInf - d.uWake) / (2 * d.uInf) := by
    unfold inductionFactor
    rw [hd]
    field_simp
    ring
  have ha0 : 0 < inductionFactor d := by
    rw [ha]
    exact div_pos (by linarith) (by linarith)
  have ha1 : inductionFactor d < 1 / 2 := by
    rw [ha, div_lt_iff₀ (by linarith)]
    linarith
  have hcp := powerCoefficient_eq h hρ hA hU hext.ne
  obtain ⟨hle, hiff⟩ := betz_bound ⟨ha0.le, ha1⟩
  refine ⟨ha0, ha1, by rw [hcp]; exact hle, by rw [hcp]; exact hiff⟩

/-- The ideal disk state with axial induction factor `a`, for density `ρ`, disk area `A`,
freestream speed `U∞` and ambient pressure `p∞`: `U_d = (1 - a) U∞`, `U_w = (1 - 2 a) U∞`, the
face pressures from Bernoulli on each side and the force `2 ρ A U∞² a (1 - a)`. -/
noncomputable def ActuatorDisk.ofInduction (ρ A uInf pAmb a : ℝ) : ActuatorDisk where
  ρ := ρ
  A := A
  uInf := uInf
  uDisk := (1 - a) * uInf
  uWake := (1 - 2 * a) * uInf
  pAmb := pAmb
  pUp := pAmb + ρ * (uInf ^ 2 - ((1 - a) * uInf) ^ 2) / 2
  pDown := pAmb + ρ * (((1 - 2 * a) * uInf) ^ 2 - ((1 - a) * uInf) ^ 2) / 2
  force := 2 * ρ * A * uInf ^ 2 * a * (1 - a)

/-- **Every induction factor is realized.** For every `a` the state `ofInduction` satisfies the
port laws; for `U∞ ≠ 0` its induction factor is `a`, and for `ρ, A, U∞ > 0` its power coefficient
is `4 a (1 - a)²`. This includes both limits of the wind-extraction branch: the zero-extraction
state `a = 0` (`U_d = U_w = U∞`, no force) and the wake-degenerate state `a = 1/2` (`U_w = 0`). -/
lemma ofInduction_spec (ρ A uInf pAmb a : ℝ) :
    (ActuatorDisk.ofInduction ρ A uInf pAmb a).PortLaws ∧
      (uInf ≠ 0 → inductionFactor (ActuatorDisk.ofInduction ρ A uInf pAmb a) = a) ∧
      (0 < ρ → 0 < A → 0 < uInf →
        powerCoefficient (ActuatorDisk.ofInduction ρ A uInf pAmb a) = 4 * a * (1 - a) ^ 2) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun hU => ?_, fun hρ hA hU => ?_⟩
  · simp only [ActuatorDisk.ofInduction]; ring
  · simp only [ActuatorDisk.ofInduction]; ring
  · simp only [ActuatorDisk.ofInduction]; ring
  · simp only [ActuatorDisk.ofInduction]; ring
  · simp only [inductionFactor, ActuatorDisk.ofInduction]
    field_simp
    ring
  · simp only [powerCoefficient, extractedPower, powerNormalization, ActuatorDisk.ofInduction]
    field_simp
    ring

/-! ## G. The hovering rotor -/

/-- The induced power `ṁ (U_w² - U∞²) / 2` with the mass flow `ṁ = ρ A U_d`: the kinetic power the
disk adds to the stream through it. -/
noncomputable def inducedPower (d : ActuatorDisk) : ℝ :=
  d.ρ * d.A * d.uDisk * (d.uWake ^ 2 - d.uInf ^ 2) / 2

/-- **Energy balance of the disk.** For every state satisfying the port laws, the induced power is
the negative of the extracted power `F U_d`, with `F` the axial force of the fluid on the disk: it
is the power `-F U_d` of the disk on the stream and, with the rotor thrust `T = -F`, it equals
`T U_d`. No still air, sign or powered assumption is needed, so the identities also cover the
reversed and zero-thrust states outside `hover_power_eq`. -/
lemma inducedPower_eq {d : ActuatorDisk} (h : d.PortLaws) {T : ℝ} (hT : d.force = -T) :
    inducedPower d = -extractedPower d ∧ inducedPower d = T * d.uDisk ∧
      inducedPower d = -(d.force * d.uDisk) := by
  have hE : inducedPower d = -extractedPower d := by
    rw [extractedPower_eq h]
    unfold inducedPower
    ring
  have hF : inducedPower d = -(d.force * d.uDisk) := by rw [hE, extractedPower]
  exact ⟨hE, by rw [hF, hT]; ring, hF⟩

/-- **Hover wake.** For a disk in still air (`U∞ = 0`) carrying a nonzero force, with positive
density and area, the port laws give the far-wake speed `U_w = 2 v_i`, twice the induced velocity
`v_i = U_d`. -/
lemma hover_uWake_eq {d : ActuatorDisk} (h : d.PortLaws) (hρ : 0 < d.ρ) (hA : 0 < d.A)
    (h0 : d.uInf = 0) (hF : d.force ≠ 0) : d.uWake = 2 * d.uDisk := by
  obtain ⟨bu, bd, md, mt⟩ := h
  simp only [h0] at bu mt
  have e1 : d.force = -(d.ρ * d.A * d.uWake ^ 2 / 2) := by
    linear_combination md - d.A * bu - d.A * bd
  have h2 : d.ρ * d.A * (d.uWake ^ 2 - 2 * d.uWake * d.uDisk) = 0 := by
    linear_combination 2 * e1 - 2 * mt
  have hρA : d.ρ * d.A ≠ 0 := ne_of_gt (mul_pos hρ hA)
  have hsq : d.uWake ^ 2 - 2 * d.uWake * d.uDisk = 0 := by
    rcases mul_eq_zero.mp h2 with hcon | hsq
    · exact absurd hcon hρA
    · exact hsq
  have hfac : d.uWake * (d.uWake - 2 * d.uDisk) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with hw0 | h2v
  · exfalso
    apply hF
    calc d.force = -(d.ρ * d.A * d.uWake ^ 2 / 2) := e1
      _ = 0 := by rw [hw0]; ring
  · exact sub_eq_zero.mp h2v

/-- **Hover thrust.** For a disk in still air with positive density and area whose rotor thrust
`T = -F` (the force of the fluid on the disk points against the flow) is positive,
`T = 2 ρ A v_i²`. -/
lemma hover_thrust_eq {d : ActuatorDisk} (h : d.PortLaws) (hρ : 0 < d.ρ) (hA : 0 < d.A)
    (h0 : d.uInf = 0) {T : ℝ} (hT : d.force = -T) (hTpos : 0 < T) :
    T = 2 * d.ρ * d.A * d.uDisk ^ 2 := by
  have hF : d.force ≠ 0 := by
    rw [hT]
    exact neg_ne_zero.mpr (ne_of_gt hTpos)
  have hw := hover_uWake_eq h hρ hA h0 hF
  obtain ⟨bu, bd, md, _⟩ := h
  simp only [h0] at bu
  have e1 : d.force = -(d.ρ * d.A * d.uWake ^ 2 / 2) := by
    linear_combination md - d.A * bu - d.A * bd
  rw [hT, hw] at e1
  linear_combination -e1

/-- **Induced velocity.** For a powered hovering disk, one whose thrust does positive work on the
stream (`T v_i > 0`), the induced velocity is `v_i = √(T / (2 ρ A))`. -/
lemma hover_inducedVelocity_eq {d : ActuatorDisk} (h : d.PortLaws) (hρ : 0 < d.ρ)
    (hA : 0 < d.A) (h0 : d.uInf = 0) {T : ℝ} (hT : d.force = -T) (hTpos : 0 < T)
    (hpow : 0 < T * d.uDisk) : d.uDisk = Real.sqrt (T / (2 * d.ρ * d.A)) := by
  have hT2 := hover_thrust_eq h hρ hA h0 hT hTpos
  have hv : 0 < d.uDisk := pos_of_mul_pos_right hpow hTpos.le
  have h2ρA : (0:ℝ) < 2 * d.ρ * d.A := by positivity
  have hsq : d.uDisk ^ 2 = T / (2 * d.ρ * d.A) := by
    rw [eq_div_iff (ne_of_gt h2ρA)]
    linear_combination -hT2
  calc d.uDisk = Real.sqrt (d.uDisk ^ 2) := (Real.sqrt_sq hv.le).symm
    _ = Real.sqrt (T / (2 * d.ρ * d.A)) := by rw [hsq]

/-- **Hover power.** The induced power of the hovering disk is `P = T v_i`; it equals the power
`-F v_i` of the disk on the stream and, for a powered disk (`T v_i > 0`),
`P = T √(T / (2 ρ A))`. -/
lemma hover_power_eq {d : ActuatorDisk} (h : d.PortLaws) (hρ : 0 < d.ρ) (hA : 0 < d.A)
    (h0 : d.uInf = 0) {T : ℝ} (hT : d.force = -T) (hTpos : 0 < T) (hpow : 0 < T * d.uDisk) :
    inducedPower d = T * d.uDisk ∧ inducedPower d = -(d.force * d.uDisk) ∧
      inducedPower d = T * Real.sqrt (T / (2 * d.ρ * d.A)) := by
  have hF : d.force ≠ 0 := by
    rw [hT]
    exact neg_ne_zero.mpr (ne_of_gt hTpos)
  have hw := hover_uWake_eq h hρ hA h0 hF
  have hT2 := hover_thrust_eq h hρ hA h0 hT hTpos
  have hvi := hover_inducedVelocity_eq h hρ hA h0 hT hTpos hpow
  have eP1 : inducedPower d = T * d.uDisk := by
    simp only [inducedPower, h0, hw]
    linear_combination (-d.uDisk) * hT2
  have eP2 : inducedPower d = -(d.force * d.uDisk) := by
    linear_combination eP1 + d.uDisk * hT
  have eP3 : inducedPower d = T * Real.sqrt (T / (2 * d.ρ * d.A)) := by
    rw [← hvi]
    exact eP1
  exact ⟨eP1, eP2, eP3⟩

end FluidDynamics.RotorPorts
