/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Tactic.Abel
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension

open scoped Matrix

/-!
# Rotating-frame acceleration decomposition

For a constant-rate rotating frame with angular velocity `Ω`, the inertial
acceleration decomposes, with the declared sign convention, as

`a_inertial = a_rot + 2 Ω × v_rot + Ω × (Ω × r)`,

where `a_rot` is the acceleration measured in the rotating frame, `v_rot`
the rotating-frame velocity, and `r` the position. The Coriolis term is
`2 Ω × v_rot` and the centripetal term is `Ω × (Ω × r)`, which points
toward the rotation axis; its negative is the centrifugal acceleration of
the rotating-frame equation of motion. The Euler term `Ω̇ × r` vanishes for
constant `Ω` and does not appear. Formally, the
inertial acceleration is the rotating-frame derivative of the inertial
velocity `w = v + Ω × r` plus the transport correction `Ω × w`; expanding
that correction gives the decomposition. The transport law (the
derivative of `Ω × r` is `Ω × v`) follows from the derivative of `r`
because `Ω × ·` is linear.

## i. Overview

`Ω × ·` is the Mathlib cross product `⨯₃`, a bilinear map, so it
distributes over addition and scalar multiplication.

## ii. Key results

- `EarthScience.rotating_acceleration_decomposition`: the algebraic
  decomposition.
- `EarthScience.rotating_acceleration_hasDerivAt`: the decomposition
  with derivatives, from the derivatives of `r` and `v`.

## iii. Table of contents

- A. Acceleration decomposition

## iv. References

- `Matrix.crossProduct` / `cross_apply` in Mathlib.
- `HasDerivAt.add`, `HasFDerivAt.comp_hasDerivAt`, and
  `LinearMap.toContinuousLinearMap` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Constant-rate rotating-frame acceleration decomposition (algebraic form,
declared sign convention: inertial acceleration = rotating-frame derivative
of the inertial velocity plus the transport correction `Ω × w`):
`(a + Ω × v) + Ω × (v + Ω × r) = a + 2 • (Ω × v) + Ω × (Ω × r)`,
where `a` is the rotating-frame acceleration, `v` the rotating-frame
velocity, `r` the position, and `Ω × ·` is the Mathlib cross product `⨯₃`.
The first term on the right is the rotating-frame acceleration, the
second is Coriolis, the third centripetal (its negative is the
centrifugal acceleration). The Euler term `Ω̇ × r` vanishes for constant
`Ω` and does not appear. -/
theorem rotating_acceleration_decomposition (Ω v a r : Fin 3 → ℝ) :
    (a + Ω ⨯₃ v) + Ω ⨯₃ (v + Ω ⨯₃ r) =
      a + 2 • (Ω ⨯₃ v) + Ω ⨯₃ (Ω ⨯₃ r) := by
  simp only [map_add, two_smul]
  abel

/-- Decomposition with derivatives: let `w t = v t + Ω × r t` be the
inertial velocity. If `r` has rotating-frame velocity `v` and `v` has
rotating-frame acceleration `a` at `t`, then `w` has rotating-frame
derivative `a + Ω × v` (the transport law `HasDerivAt (fun t => Ω × r t)
(Ω × v) t` follows from linearity of `Ω × ·`), and adding the transport
correction `Ω × w` gives the decomposition
`a + 2 • (Ω × v) + Ω × (Ω × r)`. -/
theorem rotating_acceleration_hasDerivAt (Ω : Fin 3 → ℝ)
    (r v : ℝ → Fin 3 → ℝ) (a : Fin 3 → ℝ) (t : ℝ)
    (hr : HasDerivAt (fun t : ℝ => r t) (v t) t)
    (hv : HasDerivAt (fun t : ℝ => v t) a t) :
    HasDerivAt (fun t : ℝ => v t + Ω ⨯₃ r t) (a + Ω ⨯₃ v t) t ∧
      (a + Ω ⨯₃ v t) + Ω ⨯₃ (v t + Ω ⨯₃ r t) =
        a + 2 • (Ω ⨯₃ v t) + Ω ⨯₃ (Ω ⨯₃ r t) := by
  have htransport : HasDerivAt (fun t : ℝ => Ω ⨯₃ r t) (Ω ⨯₃ v t) t :=
    (LinearMap.toContinuousLinearMap (crossProduct Ω)).hasFDerivAt.comp_hasDerivAt t hr
  exact ⟨hv.add htransport, rotating_acceleration_decomposition Ω (v t) a (r t)⟩
end EarthScience
