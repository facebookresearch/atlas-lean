/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Central forces have zero torque

A central force is parallel to the position vector: `F = c • r` for a
scalar `c`. Its torque `r ⨯₃ F` vanishes, because the cross product of a
vector with a scalar multiple of itself is zero.

## i. Overview

The torque of a force `F` applied at position `r` is `r ⨯₃ F`. For a
central force `F = c • r`, linearity of the cross product gives
`r ⨯₃ (c • r) = c • (r ⨯₃ r) = c • 0 = 0`. The same argument covers a
radial central force `F = φ (|r|) • r`, whose coefficient depends only on the
Euclidean distance `|r|` from the origin, and the signed linear central force
`F = -k • r`, which is attractive for `0 < k` and repulsive for `k < 0`.

Positions are vectors `r : Fin 3 → ℝ`. Mathlib equips this type with the
supremum norm, so the Euclidean distance is written `‖WithLp.toLp 2 r‖`, the
norm of `r` in `EuclideanSpace ℝ (Fin 3)`.

## ii. Key results

- `EarthScience.torque`: torque as a cross product.
- `EarthScience.central_force_torque_eq_zero`: a central force has zero
  torque.
- `EarthScience.radial_central_force_torque_eq_zero`: a radial central
  force, with coefficient a function of the Euclidean distance, has zero
  torque.
- `EarthScience.linear_central_force_torque_eq_zero`: a signed linear
  central force `F = -k • r` has zero torque.

## iii. References

- `cross_self` in `Mathlib/LinearAlgebra/CrossProduct.lean`, with linearity of
  the cross product (`map_smul`).
-/

@[expose] public section

namespace EarthScience

open Matrix

/-- Torque `r ⨯₃ F` of a force `F` applied at position `r`. -/
noncomputable def torque (r F : Fin 3 → ℝ) : Fin 3 → ℝ := r ⨯₃ F

/-- A central force is parallel to the position: `F = c • r` for a scalar `c`. -/
theorem central_force_torque_eq_zero (r : Fin 3 → ℝ) (c : ℝ) :
    torque r (c • r) = 0 := by
  unfold torque
  rw [map_smul, cross_self, smul_zero]

/-- A radial central force `F = φ (|r|) • r`, with any radial profile `φ` of the
Euclidean distance `|r| = ‖WithLp.toLp 2 r‖`, has zero torque. -/
theorem radial_central_force_torque_eq_zero (r : Fin 3 → ℝ) (φ : ℝ → ℝ) :
    torque r (φ ‖WithLp.toLp 2 r‖ • r) = 0 := by
  exact central_force_torque_eq_zero r (φ ‖WithLp.toLp 2 r‖)

/-- A signed linear central force `F = -k • r` has zero torque. It is attractive
for `0 < k`, repulsive for `k < 0`, and zero for `k = 0`. -/
theorem linear_central_force_torque_eq_zero (r : Fin 3 → ℝ) (k : ℝ) :
    torque r ((-k) • r) = 0 := by
  exact central_force_torque_eq_zero r (-k)

end EarthScience
