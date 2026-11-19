/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import MathlibExt.LinearAlgebra.Matrix.FullRankLinearSystem
public import PhyslibExt.EarthScience.GnssPseudorange

/-!
# Observation ports: stacked GNSS geometry at one epoch

The pseudorange of satellite `j` at receiver position `x` is `‖x - s_j‖ + b`, the geometric range
plus the receiver clock bias `b`, the clock offset times the speed of light, so `b` is a length.
At one epoch, in one common Cartesian frame, with the receiver at the origin and satellites at
`-e₁, -e₂, -e₃, +e₁`, the derivatives of the four pseudoranges along the affine perturbation
`(x, b) = (t • d, b₀ + t * db)` stack into the linear observation operator with rows
`(e₁, 1), (e₂, 1), (e₃, 1), (-e₁, 1)`. Its determinant is `2`, so it is injective and every
residual vector has exactly one state correction.

## i. Overview

* Rows. At `x₀ ≠ s` the directional derivative of `t ↦ ‖x₀ + t • d - s‖ + (b₀ + t * db)` at `0`
  is `⟪x₀ - s, d⟫ / ‖x₀ - s‖ + db`, by `EarthScience.gnss_directional_derivative`: the unit
  vector from the satellite toward the receiver, dotted with the position direction, plus the
  clock rate. At `x₀ = 0` and `s = -e₁` the unit vector is `e₁`; at `s = +e₁` it is `-e₁`.
* Stacking. The four rows form `observationMatrix`; the derivative of the stacked pseudorange
  map along `(d, db)` is `observationMatrix *ᵥ (d₁, d₂, d₃, db)`.
* Rank. `det observationMatrix = 2`, so `mulVec` is injective and each residual has a unique
  preimage (`Matrix.exists_unique_mulVec_eq`).
* Boundaries, checked in the test module. At a receiver coinciding with a satellite the range
  `‖t • d‖ = |t| ‖d‖` is not differentiable at `0` for `d ≠ 0`, so that row does not exist.
  Repeating a satellite repeats a row; the determinant is then `0` and a nonzero direction is
  invisible.

Model inputs: one epoch, one common Cartesian frame, error-free pseudoranges with the clock bias
in length units; the receiver differs from every satellite. This is the derivative of the
displayed affine perturbation and a finite row geometry. It is not a Fréchet Jacobian, not
global nonlinear localization, and no estimator, noise model or accuracy claim.

## ii. Key results

- `satellite`, `stackedPseudorange`, `observationMatrix`, `stateDirection` : the geometry.
- `satellite_ne_receiver`, `pseudorange_hasDerivAt`, `jacobianRow_eq` : the four instantiated
  rows.
- `stackedPseudorange_hasDerivAt` : the stacked derivative is the observation operator.
- `observationMatrix_det`, `observationMatrix_mulVec_injective`,
  `observationMatrix_existsUnique` : determinant `2`, injectivity, unique corrections.

## iii. Table of contents

- A. Geometry and rows
- B. The stacked operator and its rank

## iv. References

- E. D. Kaplan and C. J. Hegarty (eds.), *Understanding GPS: Principles and Applications*,
  2nd ed., Artech House (2006), Sections 2.4.1-2.4.2 and 7.3.1: pseudoranges and their
  linearization with rows `(a_i, 1)`.
- `PhyslibExt.EarthScience.GnssPseudorange` (`gnss_directional_derivative`) and
  `MathlibExt.LinearAlgebra.Matrix.FullRankLinearSystem` (`exists_unique_mulVec_eq`).
-/

@[expose] public section

open scoped InnerProductSpace Matrix

namespace Navigation.ObservationPorts

/-! ## A. Geometry and rows -/

/-- The four satellite positions `-e₁, -e₂, -e₃, +e₁` (unit distance from the receiver at the
origin), in one common Cartesian frame at one epoch. -/
noncomputable def satellite : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![-EuclideanSpace.single 0 1, -EuclideanSpace.single 1 1, -EuclideanSpace.single 2 1,
    EuclideanSpace.single 0 1]

/-- The four pseudoranges along the affine perturbation `x = 0 + t • d`, `b = b₀ + t * db` of the
receiver at the origin; `b` is the clock bias in length units. -/
noncomputable def stackedPseudorange (d : EuclideanSpace ℝ (Fin 3)) (b₀ db t : ℝ) : Fin 4 → ℝ :=
  fun j => ‖(0 : EuclideanSpace ℝ (Fin 3)) + t • d - satellite j‖ + (b₀ + t * db)

/-- The stacked linearized observation operator, rows `(e₁, 1), (e₂, 1), (e₃, 1), (-e₁, 1)`:
three position columns, then the clock column. -/
def observationMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1; -1, 0, 0, 1]

/-- The state direction `(d, db)` in `ℝ⁴`, position components first, clock rate last. -/
def stateDirection (d : EuclideanSpace ℝ (Fin 3)) (db : ℝ) : Fin 4 → ℝ :=
  ![d 0, d 1, d 2, db]

/-- The receiver at the origin differs from every satellite. -/
lemma satellite_ne_receiver (j : Fin 4) : (0 : EuclideanSpace ℝ (Fin 3)) ≠ satellite j := by
  fin_cases j
  · intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
    simp [satellite] at h2
  · intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
    simp [satellite] at h2
  · intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
    simp [satellite] at h2
  · intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
    simp [satellite] at h2

/-- Each row is the directional derivative of its pseudorange at `t = 0`:
`⟪0 - s_j, d⟫ / ‖0 - s_j‖ + db`. -/
lemma pseudorange_hasDerivAt (j : Fin 4) (d : EuclideanSpace ℝ (Fin 3)) (b₀ db : ℝ) :
    HasDerivAt (fun t : ℝ => ‖(0 : EuclideanSpace ℝ (Fin 3)) + t • d - satellite j‖ + (b₀ + t * db))
      (⟪(0 : EuclideanSpace ℝ (Fin 3)) - satellite j, d⟫_ℝ /
        ‖(0 : EuclideanSpace ℝ (Fin 3)) - satellite j‖ + db) 0 := by
  exact EarthScience.gnss_directional_derivative 0 (satellite j) d b₀ db (satellite_ne_receiver j)

/-- The rows of `observationMatrix` are the instantiated Jacobian rows: the unit vector from
satellite `j` toward the receiver, then `1` for the clock. -/
lemma jacobianRow_eq (j : Fin 4) (d : EuclideanSpace ℝ (Fin 3)) (db : ℝ) :
    ⟪(0 : EuclideanSpace ℝ (Fin 3)) - satellite j, d⟫_ℝ /
        ‖(0 : EuclideanSpace ℝ (Fin 3)) - satellite j‖ + db =
      (observationMatrix *ᵥ stateDirection d db) j := by
  fin_cases j <;> simp [satellite, EuclideanSpace.inner_single_left, observationMatrix,
    stateDirection, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]

/-! ## B. The stacked operator and its rank -/

/-- The derivative of the stacked pseudorange map along `(d, db)` at `t = 0` is the observation
operator applied to the state direction. -/
lemma stackedPseudorange_hasDerivAt (d : EuclideanSpace ℝ (Fin 3)) (b₀ db : ℝ) :
    HasDerivAt (stackedPseudorange d b₀ db) (observationMatrix *ᵥ stateDirection d db) 0 := by
  rw [hasDerivAt_pi]
  intro j
  have h := pseudorange_hasDerivAt j d b₀ db
  rwa [jacobianRow_eq j d db] at h

/-- The observation operator has determinant `2`. -/
lemma observationMatrix_det : observationMatrix.det = 2 := by
  rw [observationMatrix, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  norm_num

/-- The observation operator is injective: distinct state directions give distinct stacked
derivatives. -/
lemma observationMatrix_mulVec_injective : Function.Injective observationMatrix.mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, observationMatrix_det]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- Every residual vector has exactly one state correction. -/
lemma observationMatrix_existsUnique (r : Fin 4 → ℝ) :
    ∃! v : Fin 4 → ℝ, observationMatrix *ᵥ v = r := by
  exact Matrix.exists_unique_mulVec_eq observationMatrix_mulVec_injective r

end Navigation.ObservationPorts
