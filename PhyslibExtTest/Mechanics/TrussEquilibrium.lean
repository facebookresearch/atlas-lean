/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.TrussEquilibrium
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Truss-equilibrium checks

Concrete consumers of
`PhyslibExt.Mechanics.TrussEquilibrium`: a 3-4-5 triangle
truss at its balancing solution, a reaction-sign control, a
determinant certificate, the inverse-form solution, and a
collinear mechanism with no balance for a transverse load.

## i. Overview

These are elaboration, sign, and non-vacuity checks, not
new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Triangle truss
- B. Mechanism control

## iv. References

- `PhyslibExt.Mechanics.TrussEquilibrium`
-/

open Matrix
open PhyslibExt.Mechanics.HarmonicMechanics
open Mechanics.TrussCompatibility
open Mechanics.TrussEquilibrium

namespace PhyslibExtTest.Mechanics.TrussEquilibrium

/-- Joints `(0,0)`, `(3,0)`, `(0,4)`. -/
private abbrev triR : Fin 3 → (Fin 2 → ℝ) :=
  ![![0, 0], ![3, 0], ![0, 4]]

/-- Member first endpoints `0, 1, 0`. -/
private abbrev triA : Fin 3 → Fin 3 := ![0, 1, 0]

/-- Member second endpoints `1, 2, 2`. -/
private abbrev triB : Fin 3 → Fin 3 := ![1, 2, 2]

/-- Pin at joint 0, vertical roller at joint 1. -/
private abbrev triSJ : Fin 3 → Fin 3 := ![0, 0, 1]

/-- Support directions `x`, `y` at the pin and `y` at the
roller. -/
private abbrev triSD : Fin 3 → (Fin 2 → ℝ) :=
  ![![1, 0], ![0, 1], ![0, 1]]

/-- Load `(5, -10)` at joint 2. -/
private def triF : Fin 3 × Fin 2 → ℝ :=
  fun q => if q = (2, 0) then 5 else if q = (2, 1) then -10 else 0

private lemma sqrt9 : Real.sqrt 9 = 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]

private lemma sqrt16 : Real.sqrt 16 = 4 := by
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]

private lemma sqrt25 : Real.sqrt 25 = 5 := by
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)]

private lemma sqrt36 : Real.sqrt 36 = 6 := by
  rw [show (36 : ℝ) = 6 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)]

/-! ## A. Triangle truss -/

/-- The 3-4-5 triangle balances at member forces
`(5, -25/3, -10/3)` and reactions `(-5, 10/3, 20/3)`. -/
private theorem tri_jointBalance :
    JointBalance triR triA triB triSJ triSD triF
      ![5, -25 / 3, -10 / 3] ![-5, 10 / 3, 20 / 3] := by
  intro j k
  fin_cases j <;> fin_cases k <;>
    simp [triF, axialEndpointForce, memberLength, endpointJoint,
      Fintype.sum_prod_type, Fin.sum_univ_three] <;>
    norm_num [sqrt9, sqrt16, sqrt25]

/-- Sign control: flipping the roller reaction breaks
balance. -/
example :
    ¬ JointBalance triR triA triB triSJ triSD triF
      ![5, -25 / 3, -10 / 3] ![-5, 10 / 3, -20 / 3] := by
  intro h
  have h11 := h 1 1
  simp [triF, axialEndpointForce, memberLength, endpointJoint,
    Fintype.sum_prod_type, Fin.sum_univ_three] at h11
  norm_num [sqrt9, sqrt25] at h11

/-- Symmetric control: load `(0, -10)` at the apex of the
`(0,0), (6,0), (3,4)` truss balances with chord tension
and rafter compression. -/
example :
    JointBalance (M := Fin 3) (R := Fin 3)
      ![![0, 0], ![6, 0], ![3, 4]] triA triB triSJ triSD
      (fun q => if q = (2, 1) then -10 else 0)
      ![15 / 4, -25 / 4, -25 / 4] ![0, 5, 5] := by
  intro j k
  fin_cases j <;> fin_cases k <;>
    simp [axialEndpointForce, memberLength, endpointJoint,
      Fintype.sum_prod_type, Fin.sum_univ_three] <;>
    norm_num [sqrt25, sqrt36]

/-- The triangle square equilibrium matrix is invertible
for every equation renumbering, via injectivity of its
`mulVec` and the six homogeneous balance equations. -/
private theorem triSquare_det_isUnit
    (e : Fin 3 ⊕ Fin 3 ≃ Fin 3 × Fin 2) :
    IsUnit (squareEquilibriumMatrix triR triA triB triSJ triSD e).det := by
  rw [← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : squareEquilibriumMatrix triR triA triB triSJ triSD e
      *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hEq : equilibriumMatrix triR triA triB triSJ triSD
      *ᵥ (x - y) = 0 := by
    funext q
    have h1 := congrFun h0 (e.symm q)
    change (equilibriumMatrix triR triA triB triSJ triSD *ᵥ (x - y))
        (e (e.symm q)) = 0 at h1
    rwa [Equiv.apply_symm_apply] at h1
  rw [← Sum.elim_comp_inl_inr (x - y)] at hEq
  have hb := (jointBalance_iff_mulVec triR triA triB triSJ triSD
    0 _ _).2 hEq
  have e00 := hb 0 0
  have e01 := hb 0 1
  have e10 := hb 1 0
  have e11 := hb 1 1
  have e20 := hb 2 0
  have e21 := hb 2 1
  simp [axialEndpointForce, memberLength, endpointJoint,
    Fintype.sum_prod_type, Fin.sum_univ_three]
    at e00 e01 e10 e11 e20 e21
  norm_num [sqrt9, sqrt16, sqrt25] at e00 e01 e10 e11 e20 e21
  funext u
  rcases u with i | i <;> fin_cases i <;> simp <;> linarith

/-- Unique-balance client at the triangle data. -/
example (e : Fin 3 ⊕ Fin 3 ≃ Fin 3 × Fin 2) :
    ∃! p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      JointBalance triR triA triB triSJ triSD triF p.1 p.2 :=
  jointBalance_existsUnique triR triA triB triSJ triSD e
    (triSquare_det_isUnit e) triF

/-- The inverse formula returns the named balancing
pair. -/
example (e : Fin 3 ⊕ Fin 3 ≃ Fin 3 × Fin 2) :
    Sum.elim ![5, -25 / 3, -10 / 3] ![-5, 10 / 3, 20 / 3]
      = (squareEquilibriumMatrix triR triA triB triSJ triSD e)⁻¹
          *ᵥ (triF ∘ e) :=
  (jointBalance_iff_eq_inv triR triA triB triSJ triSD e
    (triSquare_det_isUnit e) triF _ _).1 tri_jointBalance

/-! ## B. Mechanism control -/

/-- Collinear mechanism: a transverse load at the middle
joint has no balancing pair. -/
example :
    ¬ ∃ (N : Fin 2 → ℝ) (ρ : Fin 4 → ℝ),
      JointBalance (J := Fin 3)
        ![![0, 0], ![2, 0], ![4, 0]] ![0, 1] ![1, 2]
        ![0, 0, 2, 2] ![![1, 0], ![0, 1], ![1, 0], ![0, 1]]
        (fun q => if q = (1, 1) then -1 else 0) N ρ := by
  rintro ⟨N, ρ, h⟩
  have h11 := h 1 1
  simp [axialEndpointForce, endpointJoint, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_four] at h11

#print axioms
  Mechanics.TrussEquilibrium.reactionMatrix_mulVec_apply
#print axioms Mechanics.TrussEquilibrium.jointBalance_iff_mulVec
#print axioms Mechanics.TrussEquilibrium.jointBalance_iff_eq_inv
#print axioms Mechanics.TrussEquilibrium.jointBalance_existsUnique

end PhyslibExtTest.Mechanics.TrussEquilibrium
