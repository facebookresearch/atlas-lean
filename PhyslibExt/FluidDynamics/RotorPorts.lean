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
its control volume through one port and leaves through another. Each port is a surface of
revolution about the shaft (an annulus or a cylindrical band) carrying uniform data, and is
represented at the point of azimuth `φ`, radius `r` and axial station `z`. In the local
cylindrical frame at that point, the rotation `rotZ φ` by `φ` about `e₃` of
`PhyslibExt.Units.EngineeringFrames`, the inertial fluid velocity has the components
`(c_r, c_θ, c_z)` and the outward unit normal of the port surface the meridional components
`(n_r, 0, n_z)`. The signed mass outflow is `ṁ_out = ρ A (c ⬝ n)` and the momentum outflow is
`ṁ_out c + p A n`: the momentum carried out plus the pressure term, the port term of the
two-port momentum balance of `PhyslibExt.ContinuumMechanics.ControlVolumes` on its outflow side.
It is the port area times that module's momentum flux of the uniform port state with the
pressure-only stress `σ = -p 1`, taken through the outward normal.

The moment of the momentum outflow about `o`, projected on `e₃`, is `ṁ_out r c_θ`: the pressure
term `p A n` has no axial moment, because the outward normal lies in the meridional plane, and
neither the azimuth nor the axial station enters. The steady angular-momentum balance about the
shaft, a model input, states that the axial torque `τ` exerted on the fluid by the rotor plus
every other external axial moment `M_ext` equals the axial angular-momentum outflow of the two
ports. With the steady mass balance (signed outflows `-ṁ` at the inlet and `ṁ` at the outlet) it
gives the Euler torque on the fluid `τ = ṁ (r₂ c_θ₂ - r₁ c_θ₁) - M_ext`.

When the rotor torque is exerted by forces `F_k` on the fluid at points `x_k` of the rotor, each
moving with the rotor velocity `ω e₃ ⨯₃ (x_k - o)`, the power of these forces is `ω τ`, so with
`M_ext = 0` the power on the fluid is `P = ω τ = ṁ (U₂ c_θ₂ - U₁ c_θ₁)` with the signed blade
speeds `U = ω r`. The rotor turns steadily, so the shaft torque on it balances the reaction
`-τ` of the fluid; the shaft torque is therefore `τ` and the engineering shaft power out,
`workOut (ω τ)`, is `-P`. With `ṁ > 0` a compressor or pump has `U₁ c_θ₁ < U₂ c_θ₂`
(`P > 0`, shaft power absorbed) and a turbine has `U₂ c_θ₂ < U₁ c_θ₁` (positive shaft power
out). The swirl in these formulas is the inertial one: the fluid velocity relative to the rotor
has the tangential component `c_θ - ω r`.

Model inputs: steady flow; one inlet and one outlet port, each a surface of revolution about the
shaft with uniform data; the steady mass and angular-momentum balances about the shaft, with
every external axial moment other than the rotor torque collected in `M_ext`; for the power, the
rotor torque exerted by forces at points moving with the rigid rotor, and `M_ext = 0`; for the
shaft power, a steadily turning rotor with no bearing torque. No blade-element, loss, slip or
performance-map model is used, and no empirical adequacy or machine safety claim is made.

## ii. Key results

- `FluidDynamics.RotorPorts.momentumOutflow_eq_momentumFlux`: the port momentum outflow is the
  area times the momentum flux through the outward normal.
- `FluidDynamics.RotorPorts.axialMomentOutflow_eq`: the axial angular-momentum outflow of a port
  is `ṁ_out r c_θ`.
- `FluidDynamics.RotorPorts.torqueOnFluid_eq`: the Euler torque on the fluid.
- `FluidDynamics.RotorPorts.rotorPower_eq`, `FluidDynamics.RotorPorts.powerOnFluid_eq`: the power
  on the fluid is `ω τ = ṁ (U₂ c_θ₂ - U₁ c_θ₁)`.
- `FluidDynamics.RotorPorts.shaftPowerOut_eq`: the shaft power out is its negative.
- `FluidDynamics.RotorPorts.compressor_iff`, `FluidDynamics.RotorPorts.turbine_iff`: the
  compressor and turbine signs.
- `FluidDynamics.RotorPorts.relativeSwirl_eq`: the swirl relative to the rotor is `c_θ - ω r`.
- `FluidDynamics.RotorPorts.torqueOnFluid_eq_zero_of_swirl`: no swirl change, no torque, power or
  shaft power.
- A compressor with a nonzero swirl change, the same ports with the throughflow reversed, a blade
  force that realizes the compressor's torque and the rotor-relative swirl of its ports are
  checked in `PhyslibExtTest.FluidDynamics.RotorPorts`.

## iii. Table of contents

- A. Ports about the shaft
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

/-! ## A. Ports about the shaft -/

/-- The unit vector `e₃` of the shaft axis, the third inertial axis. -/
def shaftAxis : Fin 3 → ℝ := ![0, 0, 1]

/-- The local cylindrical frame at azimuth `φ` about the shaft: the rotation by `φ` about the third
axis, whose columns are the radial, tangential and axial unit vectors `e_r = (cos φ, sin φ, 0)`,
`e_θ = (-sin φ, cos φ, 0)` and `e₃`. -/
noncomputable def cylFrame (φ : ℝ) : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨rotZ φ, rotZ_mem_specialOrthogonalGroup φ⟩

/-- A flow port of a rotor control volume: a surface of revolution about the shaft carrying
uniform data, represented at the point of azimuth `φ`, radius `r` and axial station `z`. In the
local cylindrical frame at that point the inertial fluid velocity has the components
`(cr, cθ, cz)`, so `cθ` is the inertial swirl velocity, positive along `e_θ`, and the outward
unit normal of the port surface has the meridional components `(nr, 0, nz)`. -/
structure RotorPort where
  /-- The density `ρ`. -/
  ρ : ℝ
  /-- The port area `A`. -/
  A : ℝ
  /-- The static pressure `p`. -/
  p : ℝ
  /-- The azimuth `φ` of the representative point. -/
  φ : ℝ
  /-- The radius `r` of the port. -/
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

namespace RotorPort

/-- The inertial position `o + r e_r + z e₃` of the representative point, for the origin `o` of
the shaft axis. -/
noncomputable def point (o : Fin 3 → ℝ) (P : RotorPort) : Fin 3 → ℝ :=
  bodyToInertial o (cylFrame P.φ) ![P.r, 0, P.z]

/-- The inertial velocity `cr e_r + cθ e_θ + cz e₃`. -/
noncomputable def velocity (P : RotorPort) : Fin 3 → ℝ :=
  bodyToInertialVec (cylFrame P.φ) ![P.cr, P.cθ, P.cz]

/-- The outward unit normal `nr e_r + nz e₃`. -/
noncomputable def normal (P : RotorPort) : Fin 3 → ℝ :=
  bodyToInertialVec (cylFrame P.φ) ![P.nr, 0, P.nz]

/-- The signed mass outflow `ρ A (c ⬝ n)`: positive through an outlet, negative through an
inlet. -/
noncomputable def massOutflow (P : RotorPort) : ℝ :=
  P.ρ * P.A * (P.velocity ⬝ᵥ P.normal)

/-- The momentum outflow `ṁ_out c + p A n`: the momentum carried out of the control volume plus
the pressure term of the port. -/
noncomputable def momentumOutflow (P : RotorPort) : Fin 3 → ℝ :=
  P.massOutflow • P.velocity + (P.p * P.A) • P.normal

end RotorPort

/-- Every cylindrical frame fixes the shaft axis. -/
private lemma bodyToInertialVec_shaftAxis (φ : ℝ) :
    bodyToInertialVec (cylFrame φ) ![0, 0, 1] = shaftAxis := by
  ext i
  fin_cases i <;>
    simp [bodyToInertialVec, cylFrame, rotZ, shaftAxis, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- The axial angular-momentum outflow of a port about the shaft: the moment
`(x - o) ⨯₃ (ṁ_out c + p A n)` of its momentum outflow about the point `o` of the shaft axis,
projected on `e₃`. -/
noncomputable def axialMomentOutflow (o : Fin 3 → ℝ) (P : RotorPort) : ℝ :=
  shaftAxis ⬝ᵥ ((P.point o - o) ⨯₃ P.momentumOutflow)

/-- **The port momentum outflow is the momentum flux through the port.** The momentum outflow
`ṁ_out c + p A n` is the port area times the momentum flux of the uniform port state with the
pressure-only stress `σ = -p 1`, taken through the outward normal, at every point `x`. -/
lemma momentumOutflow_eq_momentumFlux (P : RotorPort) (x : Fin 3 → ℝ) :
    P.momentumOutflow = P.A • fun j : Fin 3 => ∑ i : Fin 3,
      ControlVolumes.momentumFlux (n := 2) (fun _ => P.ρ) (fun _ => P.velocity)
        (fun _ => -(P.p • (1 : Matrix (Fin 3) (Fin 3) ℝ))) j x i * P.normal i := by
  ext j
  simp only [RotorPort.momentumOutflow, RotorPort.massOutflow, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  fin_cases j <;>
    simp [ControlVolumes.momentumFlux, Matrix.vec3_dotProduct, Fin.sum_univ_three,
      Matrix.one_apply] <;>
    ring

/-- The normal velocity is frame independent: the signed mass outflow is
`ρ A (cr nr + cz nz)`. -/
lemma massOutflow_eq (P : RotorPort) :
    P.massOutflow = P.ρ * P.A * (P.cr * P.nr + P.cz * P.nz) := by
  simp only [RotorPort.massOutflow, RotorPort.velocity, RotorPort.normal,
    bodyToInertialVec_dotProduct, Matrix.vec3_dotProduct']
  ring

/-- **Axial moment of a port's momentum outflow.** About the point `o` of the shaft axis the axial
angular-momentum outflow of a port is `ṁ_out r cθ`. The pressure term `p A n` has no axial moment,
since the outward normal lies in the meridional plane, and neither the azimuth `φ` nor the axial
station `z` enters. -/
lemma axialMomentOutflow_eq (o : Fin 3 → ℝ) (P : RotorPort) :
    axialMomentOutflow o P = P.massOutflow * (P.r * P.cθ) := by
  have hmom : P.momentumOutflow = bodyToInertialVec (cylFrame P.φ)
      (P.massOutflow • ![P.cr, P.cθ, P.cz] + (P.p * P.A) • ![P.nr, 0, P.nz]) := by
    simp only [RotorPort.momentumOutflow, RotorPort.velocity, RotorPort.normal,
      bodyToInertialVec, Matrix.mulVec_add, Matrix.mulVec_smul]
  simp only [axialMomentOutflow, RotorPort.point]
  rw [(bodyToInertialVec_shaftAxis P.φ).symm, hmom, ← bodyToInertialVec_moment,
    bodyToInertialVec_dotProduct]
  simp only [cross_apply, Matrix.vec3_dotProduct', Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## B. The Euler torque on the fluid -/

/-- **Euler torque on the fluid.** Model inputs: steady flow through a rotor control volume with
one inlet and one outlet port; the steady mass balance, signed mass outflows `-ṁ` at the inlet and
`ṁ` at the outlet; and the steady angular-momentum balance about the shaft: the axial torque `τ`
exerted on the fluid by the rotor plus every other external axial moment `M_ext` equals the axial
angular-momentum outflow of the two ports. Then `τ = ṁ (r₂ cθ₂ - r₁ cθ₁) - M_ext`. -/
lemma torqueOnFluid_eq {o : Fin 3 → ℝ} {inlet outlet : RotorPort} {mdot τ Mext : ℝ}
    (hin : inlet.massOutflow = -mdot) (hout : outlet.massOutflow = mdot)
    (hbal : τ + Mext = axialMomentOutflow o inlet + axialMomentOutflow o outlet) :
    τ = mdot * (outlet.r * outlet.cθ - inlet.r * inlet.cθ) - Mext := by
  rw [axialMomentOutflow_eq, axialMomentOutflow_eq, hin, hout] at hbal
  linear_combination hbal

/-- **Zero swirl change.** If the inlet and outlet carry the same angular momentum per unit mass,
`r₁ cθ₁ = r₂ cθ₂`, and no other external moment acts, the torque on the fluid, the power `ω τ`
on it and the shaft power out vanish, for every throughflow and every rotor speed. -/
lemma torqueOnFluid_eq_zero_of_swirl {o : Fin 3 → ℝ} {inlet outlet : RotorPort}
    {mdot τ ω : ℝ} (hin : inlet.massOutflow = -mdot) (hout : outlet.massOutflow = mdot)
    (hbal : τ = axialMomentOutflow o inlet + axialMomentOutflow o outlet)
    (hswirl : inlet.r * inlet.cθ = outlet.r * outlet.cθ) :
    τ = 0 ∧ ω * τ = 0 ∧ ProcessPorts.workOut (ω * τ) = 0 := by
  rw [axialMomentOutflow_eq, axialMomentOutflow_eq, hin, hout, hswirl] at hbal
  have hτ : τ = 0 := by linear_combination hbal
  refine ⟨hτ, by rw [hτ, mul_zero], by simp [hτ, ProcessPorts.workOut]⟩

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
at points moving with the rotor, no other external moment acts and the steady mass and
angular-momentum balances hold, the torque on the fluid is `τ = ṁ (r₂ cθ₂ - r₁ cθ₁)` and the
power on the fluid is `P = ω τ = ṁ (U₂ cθ₂ - U₁ cθ₁)` with the signed blade speeds `U = ω r`. -/
lemma powerOnFluid_eq {ι : Type*} [Fintype ι] {ω : ℝ} {o : Fin 3 → ℝ} {x F : ι → Fin 3 → ℝ}
    {inlet outlet : RotorPort} {mdot : ℝ}
    (hin : inlet.massOutflow = -mdot) (hout : outlet.massOutflow = mdot)
    (hbal : axialTorque o x F = axialMomentOutflow o inlet + axialMomentOutflow o outlet) :
    axialTorque o x F = mdot * (outlet.r * outlet.cθ - inlet.r * inlet.cθ) ∧
      rotorPower ω o x F = ω * axialTorque o x F ∧
      rotorPower ω o x F = mdot * (ω * outlet.r * outlet.cθ - ω * inlet.r * inlet.cθ) := by
  have htorq := torqueOnFluid_eq (Mext := 0) hin hout (by simpa using hbal)
  rw [sub_zero] at htorq
  refine ⟨htorq, rotorPower_eq ω o x F, ?_⟩
  rw [rotorPower_eq, htorq]
  ring

/-- **Shaft power out is the negative of the power on the fluid.** Model inputs: the rotor turns
steadily, so the axial torques on it balance, `τ_shaft + τ_reaction = 0` (no bearing torque), and
the fluid reacts on the rotor with `τ_reaction = -τ`. Then the shaft torque on the rotor equals
the torque `τ` on the fluid, and the engineering shaft power out `workOut (ω τ_shaft)` is `-ω τ`,
which for the Euler torque is `ṁ (U₁ cθ₁ - U₂ cθ₂)`. -/
lemma shaftPowerOut_eq {ω τ τShaft τReaction mdot r₁ cθ₁ r₂ cθ₂ : ℝ}
    (hrotor : τShaft + τReaction = 0) (hreact : τReaction = -τ)
    (heuler : τ = mdot * (r₂ * cθ₂ - r₁ * cθ₁)) :
    τShaft = τ ∧ ProcessPorts.workOut (ω * τShaft) = -(ω * τ) ∧
      ProcessPorts.workOut (ω * τShaft) = mdot * (ω * r₁ * cθ₁ - ω * r₂ * cθ₂) := by
  have hS : τShaft = τ := by linarith
  refine ⟨hS, by simp only [hS, ProcessPorts.workOut], ?_⟩
  simp only [hS, heuler, ProcessPorts.workOut]
  ring

/-- **Compressor or pump sign.** With positive throughflow `ṁ > 0`, the Euler power on the fluid
`ṁ (U₂ cθ₂ - U₁ cθ₁)` is positive, and the shaft power out negative, exactly when
`U₁ cθ₁ < U₂ cθ₂`. -/
lemma compressor_iff {mdot ω r₁ cθ₁ r₂ cθ₂ : ℝ} (hm : 0 < mdot) :
    (0 < mdot * (ω * r₂ * cθ₂ - ω * r₁ * cθ₁) ↔ ω * r₁ * cθ₁ < ω * r₂ * cθ₂) ∧
      (ProcessPorts.workOut (mdot * (ω * r₂ * cθ₂ - ω * r₁ * cθ₁)) < 0 ↔
        ω * r₁ * cθ₁ < ω * r₂ * cθ₂) := by
  have hpos : ∀ X : ℝ, (0 < mdot * X ↔ 0 < X) :=
    fun X => ⟨fun h => pos_of_mul_pos_right h hm.le, fun h => mul_pos hm h⟩
  constructor
  · rw [hpos]
    constructor <;> intro h <;> linarith
  · simp only [ProcessPorts.workOut, neg_lt_zero, hpos]
    constructor <;> intro h <;> linarith

/-- **Turbine sign.** With positive throughflow `ṁ > 0`, the shaft power out is positive, and the
power on the fluid negative, exactly when `U₂ cθ₂ < U₁ cθ₁`. -/
lemma turbine_iff {mdot ω r₁ cθ₁ r₂ cθ₂ : ℝ} (hm : 0 < mdot) :
    (0 < ProcessPorts.workOut (mdot * (ω * r₂ * cθ₂ - ω * r₁ * cθ₁)) ↔
        ω * r₂ * cθ₂ < ω * r₁ * cθ₁) ∧
      (mdot * (ω * r₂ * cθ₂ - ω * r₁ * cθ₁) < 0 ↔ ω * r₂ * cθ₂ < ω * r₁ * cθ₁) := by
  have hneg : ∀ X : ℝ, (mdot * X < 0 ↔ X < 0) :=
    fun X => ⟨fun h => neg_of_mul_neg_right h hm.le, fun h => mul_neg_of_pos_of_neg hm h⟩
  constructor
  · simp only [ProcessPorts.workOut, neg_pos, hneg]
    constructor <;> intro h <;> linarith
  · rw [hneg]
    constructor <;> intro h <;> linarith

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
