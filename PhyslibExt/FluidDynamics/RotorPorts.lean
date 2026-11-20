/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import PhyslibExt.ContinuumMechanics.ControlVolumes
public import PhyslibExt.Thermodynamics.ProcessPorts
public import PhyslibExt.Units.EngineeringFrames

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rotor ports: Euler torque and power on the fluid

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

Model inputs: steady flow; one inlet and one outlet port, each lumped at one representative point
with a nonnegative density, port area and effective moment radius and a unit normal; the steady
mass and angular-momentum balances about the shaft applied to the lumped port values, with every
external axial moment other than the rotor torque collected in `M_ext`; for the power, the rotor
torque exerted by forces at points moving with the rigid rotor, and `M_ext = 0`; for the shaft
power, a steadily turning rotor with no bearing torque. No port-surface integral, blade-element,
loss, slip or performance-map model is used, and no empirical adequacy or machine safety claim is
made.

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
- A compressor with a nonzero swirl change, the same ports with the throughflow reversed, blade
  forces that realize their torques and the rotor-relative swirl of the ports are checked in
  `PhyslibExtTest.FluidDynamics.RotorPorts`.

## iii. Table of contents

- A. Lumped ports about the shaft
- B. The Euler torque on the fluid
- C. Power on the fluid and shaft power out

## iv. References

- S. L. Dixon and C. A. Hall, *Fluid Mechanics and Thermodynamics of Turbomachinery*,
  Butterworth-Heinemann, ch. 2: the moment of momentum and the Euler work equation
  `τ = ṁ (r₂ c_θ₂ - r₁ c_θ₁)`, `Ẇ = ṁ (U₂ c_θ₂ - U₁ c_θ₁)` for compressors and turbines.
- F. M. White, *Fluid Mechanics*, McGraw-Hill, ch. 3 (the angular-momentum relation for a fixed
  control volume) and ch. 11 (turbomachinery: the Euler turbomachine equation).
- Y. A. Çengel and J. M. Cimbala, *Fluid Mechanics: Fundamentals and Applications*,
  McGraw-Hill, ch. 6 (the angular-momentum equation and radial-flow devices).
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

end FluidDynamics.RotorPorts
