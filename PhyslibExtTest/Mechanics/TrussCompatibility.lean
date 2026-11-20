/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.TrussCompatibility
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Truss-compatibility checks

Concrete consumers of
`PhyslibExt.Mechanics.TrussCompatibility` on a three-joint
table: horizontal-member elongation pairing, supported
energy value, a zero-length member contributing a zero
unit row, supported virtual work on the mechanism
(one-member) truss, the supported rigidity certificate
on a triangle and its supported null mode, and unique
supported response on triangle and focused fixtures.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Row action and supported energy
- B. Supported virtual work
- C. Supported rigidity certificate
- D. Supported unique response

## iv. References

- `PhyslibExt.Mechanics.TrussCompatibility`
-/

open Matrix
open PhyslibExt.Mechanics.HarmonicMechanics
open Mechanics.TrussCompatibility

namespace PhyslibExtTest.Mechanics.TrussCompatibility

/-- Joints at `(0,0)`, `(4,0)`, `(1,3)`; one member 0 → 1. -/
private abbrev r3 : Fin 3 → (Fin 2 → ℝ) := ![![0, 0], ![4, 0], ![1, 3]]

/-- Joint displacement: `(1, 0)` at joint 0, `(3, 0)` at
joint 1, zero else. -/
private def u6 : Fin 3 × Fin 2 → ℝ :=
  fun q => if q = (0, 0) then 1 else if q = (1, 0) then 3 else 0

/-- Identity injection on joint coordinates. -/
private abbrev S6 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ := 1

/-! ## A. Row action and supported energy -/

/-- Horizontal member of length 4: the separation row reads
`4 * (3 - 1) = 8` (separation pairing, `L` times elongation). -/
example : (axialCompatibility r3 ![0] ![1] *ᵥ u6) 0 = 8 := by
  rw [axialCompatibility_mulVec_apply]
  norm_num [Fin.sum_univ_two, u6]

/-- The unit row reads the elongation `2`. -/
example : (axialCompatibilityUnit r3 ![0] ![1] *ᵥ u6) 0 = 2 := by
  have hL : memberLength r3 ![0] ![1] 0 = 4 := by
    rw [memberLength]
    norm_num
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hrow : axialCompatibilityUnit r3 ![0] ![1]
      = (4 : ℝ)⁻¹ • axialCompatibility r3 ![0] ![1] := by
    ext e q
    fin_cases e <;> simp [axialCompatibilityUnit, hL]
  rw [hrow, Matrix.smul_mulVec]
  have h8 : (axialCompatibility r3 ![0] ![1] *ᵥ u6) 0 = 8 := by
    rw [axialCompatibility_mulVec_apply]
    norm_num [Fin.sum_univ_two, u6]
  simp [h8]
  norm_num

/-- Supported quadratic form (twice linearized stored energy)
with the identity injection and unit stiffness:
`1 * 8 ^ 2 = 64` in separation form. -/
example : u6 ⬝ᵥ (((axialCompatibility r3 ![0] ![1] * S6)ᵀ
          * Matrix.diagonal (![1] : Fin 1 → ℝ)
          * (axialCompatibility r3 ![0] ![1] * S6)) *ᵥ u6)
    = 64 := by
  rw [supported_quad_form_eq_sum]
  simp only [Matrix.mulVec_apply, Matrix.row, dotProduct,
    axialCompatibility, Matrix.of_apply, u6, Fintype.sum_prod_type, Finset.univ_product_univ,
    Finset.sum_product, Fin.sum_univ_three, Fin.sum_univ_two]
  norm_num

/-- A zero-length member contributes a zero unit row. -/
example : (axialCompatibilityUnit (![![1, 1], ![1, 1]] :
        Fin 2 → (Fin 2 → ℝ)) ![0] ![1]
      *ᵥ fun q => if q = (0, 0) then 1 else 0) 0 = 0 := by
  rw [Matrix.mulVec_apply]
  simp [axialCompatibilityUnit, axialCompatibility, memberLength,
    dotProduct, Fin.sum_univ_two]

/-- Positive semidefiniteness client at unit data. -/
example : ((axialCompatibility r3 ![0] ![1] * S6)ᵀ
    * Matrix.diagonal (![1] : Fin 1 → ℝ)
    * (axialCompatibility r3 ![0] ![1] * S6)).PosSemidef :=
  supported_posSemidef r3 ![0] ![1] S6 (![1] : Fin 1 → ℝ)
    (by intro i; fin_cases i <;> norm_num)

/-! ## B. Supported virtual work -/

/-- Supported load balanced by `s = 2` on the one-member
table: `-8` at joint 0 `x`, `8` at joint 1 `x`. -/
private def fB : Fin 3 × Fin 2 → ℝ :=
  fun q => if q = (0, 0) then -8 else if q = (1, 0) then 8 else 0

/-- The balanced-load identity `(B * 1)ᵀ *ᵥ ![2] = fB`,
coordinate by coordinate. -/
example : (axialCompatibility r3 ![0] ![1] * S6)ᵀ *ᵥ (![2] : Fin 1 → ℝ)
    = fB := by
  funext q
  obtain ⟨j, k⟩ := q
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.mulVec_apply, Matrix.transpose_apply, axialCompatibility,
      Matrix.of_apply, dotProduct, fB, r3] <;> norm_num

/-- Forward direction at the nonzero virtual displacement
`u6`: internal and external virtual work are both `16`.
The one-member table is a mechanism (its compatibility map
has a large kernel); no injectivity is needed. -/
example : (![2] : Fin 1 → ℝ)
      ⬝ᵥ ((axialCompatibility r3 ![0] ![1] * S6) *ᵥ u6) = fB ⬝ᵥ u6 ∧
    fB ⬝ᵥ u6 = 16 := by
  have heq : (axialCompatibility r3 ![0] ![1] * S6)ᵀ *ᵥ (![2] : Fin 1 → ℝ)
      = fB := by
    funext q
    obtain ⟨j, k⟩ := q
    fin_cases j <;> fin_cases k <;>
      simp [Matrix.mulVec_apply, Matrix.transpose_apply, axialCompatibility,
        Matrix.of_apply, dotProduct, fB, r3] <;> norm_num
  refine ⟨(supported_virtualWork_iff r3 ![0] ![1] S6 _ _).mp heq u6, ?_⟩
  simp only [dotProduct, u6, fB, Fintype.sum_prod_type, Fin.sum_univ_three,
    Fin.sum_univ_two]
  norm_num

/-- Reverse direction at the zero support map: virtual
work (both sides zero) gives the zero equilibrium. -/
example (s : Fin 1 → ℝ) :
    (axialCompatibility r3 ![0] ![1] * (0 : Matrix (Fin 3 × Fin 2)
        (Fin 3 × Fin 2) ℝ))ᵀ *ᵥ s = 0 :=
  (supported_virtualWork_iff r3 ![0] ![1] 0 s 0).mpr (fun v => by simp)

/-- Mechanism negative control: a transverse load at joint
0 cannot be balanced by any member coefficient, because
the transverse virtual displacement does no internal work. -/
example (s : Fin 1 → ℝ) :
    ¬ ∀ v : Fin 3 × Fin 2 → ℝ,
      s ⬝ᵥ ((axialCompatibility r3 ![0] ![1] * S6) *ᵥ v)
        = (fun q => if q = (0, 1) then (1 : ℝ) else 0) ⬝ᵥ v := by
  intro h
  have hv := h (fun q => if q = (0, 1) then (1 : ℝ) else 0)
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three,
    Fin.sum_univ_two, Fin.sum_univ_one, Matrix.mulVec_apply, Matrix.row,
    axialCompatibility, Matrix.of_apply, Matrix.one_apply,
    Matrix.mul_apply] at hv
  norm_num [r3] at hv

#print axioms
  Mechanics.TrussCompatibility.axialCompatibility_mulVec_apply
#print axioms
  Mechanics.TrussCompatibility.axialCompatibility_transpose_mulVec_apply
#print axioms
  Mechanics.TrussCompatibility.axialCompatibilityUnit_transpose_mulVec_apply
#print axioms Mechanics.TrussCompatibility.supported_quad_form_eq_sum
#print axioms Mechanics.TrussCompatibility.supported_posSemidef
#print axioms Mechanics.TrussCompatibility.supported_virtualWork_iff

/-! ## C. Supported rigidity certificate

Witness truss: joints `(0,0)`, `(4,0)`, `(4,3)`; pin at
joint 0, roller at joint 1 (only `1x` free), joint 2 free.
Free coordinates are `(1x, 2x, 2y)`. -/

/-- Joints at `(0,0)`, `(4,0)`, `(4,3)`. -/
private abbrev rT : Fin 3 → (Fin 2 → ℝ) := ![![0, 0], ![4, 0], ![4, 3]]

/-- Selection of the free coordinates `1x, 2x, 2y`. -/
private abbrev ST : Matrix (Fin 3 × Fin 2) (Fin 3) ℝ :=
  Matrix.of fun q f =>
    if (q = (1, 0) ∧ f = 0) ∨ (q = (2, 0) ∧ f = 1)
        ∨ (q = (2, 1) ∧ f = 2)
    then 1 else 0

/-- Supported row action for the triangle `0→1, 0→2, 1→2`:
`B S *ᵥ v = (4 v₀, 4 v₁ + 3 v₂, 3 v₂)`. -/
private lemma supportedActionTri (v : Fin 3 → ℝ) (e : Fin 3) :
    ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST) *ᵥ v) e
      = ![4 * v 0, 4 * v 1 + 3 * v 2, 3 * v 2] e := by
  rw [← Matrix.mulVec_mulVec, axialCompatibility_mulVec_apply]
  fin_cases e <;>
    simp [Fin.sum_univ_two, ST, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- Supported row action without member `1→2`:
`B S *ᵥ v = (4 v₀, 4 v₁ + 3 v₂)`. -/
private lemma supportedActionTwo (v : Fin 3 → ℝ) (e : Fin 2) :
    ((axialCompatibility rT ![0, 0] ![1, 2] * ST) *ᵥ v) e
      = ![4 * v 0, 4 * v 1 + 3 * v 2] e := by
  rw [← Matrix.mulVec_mulVec, axialCompatibility_mulVec_apply]
  fin_cases e <;>
    simp [Fin.sum_univ_two, ST, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- P1: the supported nondegenerate triangle is rigid:
positive definite supported stiffness through the
certificate. -/
example : ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST)ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST)).PosDef := by
  refine (supported_posDef_iff rT ![0, 0, 1] ![1, 2, 2] ST _
    (fun _ => by norm_num)).2 ?_
  intro v hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  rw [supportedActionTri] at h0 h1 h2
  simp at h0 h1 h2
  funext i
  fin_cases i <;> simp <;> linarith

/-- P2: dropping member `1→2` leaves a mechanism
`(0, 3, -4)` despite the member graph staying connected:
not positive definite. (`ST` is a coordinate selection,
so generalized coordinates are the supported joint
coordinates and the null mode is a joint mechanism.) -/
example : ¬ ((axialCompatibility rT ![0, 0] ![1, 2] * ST)ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0] ![1, 2] * ST)).PosDef := by
  rw [supported_posDef_iff rT ![0, 0] ![1, 2] ST _
    (fun _ => by norm_num)]
  intro h
  have hmech := h ![0, 3, -4] (by
    funext e
    rw [supportedActionTwo]
    fin_cases e
    · simp
    · simp
      norm_num)
  have h1 := congrFun hmech 1
  simp at h1

/-- Noncoincident endpoint positions on the witness truss. -/
private lemma endpointsNeTri :
    ∀ e, rT (![0, 0, 1] e) ≠ rT (![1, 2, 2] e) := by
  intro e
  fin_cases e
  · intro h
    exact absurd (congrFun h 0) (by simp)
  · intro h
    exact absurd (congrFun h 0) (by simp)
  · intro h
    exact absurd (congrFun h 1) (by simp)

private lemma endpointsNeTwo :
    ∀ e, rT (![0, 0] e) ≠ rT (![1, 2] e) := by
  intro e
  fin_cases e <;> · intro h
                    exact absurd (congrFun h 0) (by simp)

/-- P3: the physical instance (`E = 200`, `A = 1/100`) on
the rigid triangle. -/
example : ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST)ᵀ
      * Matrix.diagonal
        (fun e => (200 : ℝ) * (1 / 100)
          / memberLength rT ![0, 0, 1] ![1, 2, 2] e ^ 3)
      * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST)).PosDef := by
  refine (supported_posDef_iff_of_axial rT ![0, 0, 1] ![1, 2, 2] ST
    (fun _ => by norm_num) (fun _ => by norm_num)
    endpointsNeTri).2 ?_
  intro v hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  rw [supportedActionTri] at h0 h1 h2
  simp at h0 h1 h2
  funext i
  fin_cases i <;> simp <;> linarith

/-- P4: the physical instance (`E = A = 1`) on the
mechanism. -/
example : ¬ ((axialCompatibility rT ![0, 0] ![1, 2] * ST)ᵀ
      * Matrix.diagonal
        (fun e => (1 : ℝ) * 1
          / memberLength rT ![0, 0] ![1, 2] e ^ 3)
      * (axialCompatibility rT ![0, 0] ![1, 2] * ST)).PosDef := by
  rw [supported_posDef_iff_of_axial rT ![0, 0] ![1, 2] ST
    (fun _ => by norm_num) (fun _ => by norm_num) endpointsNeTwo]
  intro h
  have hmech := h ![0, 3, -4] (by
    funext e
    rw [supportedActionTwo]
    fin_cases e
    · simp
    · simp
      norm_num)
  have h1 := congrFun hmech 1
  simp at h1

/-- Joints at `(0,0)`, `(1,0)` for the zero-stiffness
control. -/
private abbrev rN : Fin 2 → (Fin 2 → ℝ) := ![![0, 0], ![1, 0]]

/-- Selection of the single free coordinate `1x`. -/
private abbrev S1 : Matrix (Fin 2 × Fin 2) (Fin 1) ℝ :=
  Matrix.of fun q f => if q = (1, 0) ∧ f = 0 then 1 else 0

/-- N1: `hk` is necessary. With `k = 0` the one-bar kernel
is trivial but the (zero) stiffness is not positive
definite. -/
example : (∀ u : Fin 1 → ℝ,
      (axialCompatibility rN ![0] ![1] * S1) *ᵥ u = 0 → u = 0)
    ∧ ¬ ((axialCompatibility rN ![0] ![1] * S1)ᵀ
      * Matrix.diagonal (fun _ => (0 : ℝ))
      * (axialCompatibility rN ![0] ![1] * S1)).PosDef := by
  have hrow : ∀ v : Fin 1 → ℝ,
      ((axialCompatibility rN ![0] ![1] * S1) *ᵥ v) 0 = v 0 := by
    intro v
    rw [← Matrix.mulVec_mulVec, axialCompatibility_mulVec_apply]
    simp [S1, Matrix.mulVec, dotProduct]
  constructor
  · intro u hu
    have h0 := congrFun hu 0
    rw [hrow] at h0
    funext i
    fin_cases i
    simpa using h0
  · intro hPD
    have hpos := Matrix.PosDef.dotProduct_mulVec_pos hPD
      (x := ![1]) (by simp)
    have hstar : star (![1] : Fin 1 → ℝ) = ![1] := by simp
    rw [hstar, supported_quad_form_eq_sum] at hpos
    simp at hpos

/-- E2: with `S = 0` both sides of the certificate fail
(`![1, 0, 0]` is a generalized-coordinate null mode; it
gives zero joint displacement, so it is not a physical
mechanism). -/
example : ¬ ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 3) ℝ))ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 3) ℝ))).PosDef := by
  rw [supported_posDef_iff rT ![0, 0, 1] ![1, 2, 2] 0 _
    (fun _ => by norm_num)]
  intro h
  have hmech := h ![1, 0, 0] (by simp)
  have h0 := congrFun hmech 0
  simp at h0

/-- E1: with no free coordinates both sides hold (the empty
stiffness is positive definite). -/
example : ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 0) ℝ))ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 0) ℝ))).PosDef := by
  refine (supported_posDef_iff rT ![0, 0, 1] ![1, 2, 2] 0 _
    (fun _ => by norm_num)).2 ?_
  intro u _
  funext i
  exact (Nat.not_lt_zero _ i.2).elim

/-- E3: with no members both sides fail (`hk` vacuous). -/
example : ¬ ((axialCompatibility (![![0, 0]] : Fin 1 → (Fin 2 → ℝ))
        ((fun _ => (0 : Fin 1)) : Fin 0 → Fin 1)
        ((fun _ => (0 : Fin 1)) : Fin 0 → Fin 1)
        * (0 : Matrix (Fin 1 × Fin 2) (Fin 1) ℝ))ᵀ
      * Matrix.diagonal (fun _ => (1 : ℝ))
      * (axialCompatibility (![![0, 0]] : Fin 1 → (Fin 2 → ℝ))
        ((fun _ => (0 : Fin 1)) : Fin 0 → Fin 1)
        ((fun _ => (0 : Fin 1)) : Fin 0 → Fin 1)
        * (0 : Matrix (Fin 1 × Fin 2) (Fin 1) ℝ))).PosDef := by
  rw [supported_posDef_iff _ _ _ 0 _
    (fun e => (Nat.not_lt_zero _ e.2).elim)]
  intro h
  have hmech := h ![1] (by
    funext e
    exact (Nat.not_lt_zero _ e.2).elim)
  have h0 := congrFun hmech 0
  simp at h0


/-! ## D. Supported unique response -/

/-- Kernel triviality on the witness triangle, reused by
the response checks below. -/
private lemma kernelTri : ∀ v : Fin 3 → ℝ,
    (axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST) *ᵥ v = 0 → v = 0 := by
  intro v hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  rw [supportedActionTri] at h0 h1 h2
  simp at h0 h1 h2
  funext i
  fin_cases i <;> simp <;> linarith

/-- Unique supported displacement on the witness triangle
at the load coming from `u = ![1, 1, 1]`. -/
example : ∃! u : Fin 3 → ℝ,
    ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST)ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST)) *ᵥ u
        = ![32, 56, 60] :=
  supported_existsUnique rT ![0, 0, 1] ![1, 2, 2] ST _
    (fun _ => by norm_num) kernelTri _

/-- Unique residual pair on the witness triangle for a
full load supported at the free coordinate `(2, 1)`. -/
example : ∃! p : (Fin 3 → ℝ) × (Fin 3 × Fin 2 → ℝ),
    ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2])ᵀ
        * Matrix.diagonal (fun _ => (2 : ℝ))
        * axialCompatibility rT ![0, 0, 1] ![1, 2, 2]) *ᵥ (ST *ᵥ p.1)
      = (fun q => if q = (2, 1) then (1 : ℝ) else 0) + p.2
      ∧ STᵀ *ᵥ p.2 = 0 := by
  have hPD : ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST)ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST)).PosDef :=
    (supported_posDef_iff rT ![0, 0, 1] ![1, 2, 2] ST _
      (fun _ => by norm_num)).mpr kernelTri
  exact supported_residual_existsUnique_of_posDef rT ![0, 0, 1]
    ![1, 2, 2] ST _ hPD _

/-- Both physical response conclusions on the P3 data. -/
example : (∀ f : Fin 3 → ℝ, ∃! u : Fin 3 → ℝ,
      ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST)ᵀ
        * Matrix.diagonal
          (fun e => (200 : ℝ) * (1 / 100)
            / memberLength rT ![0, 0, 1] ![1, 2, 2] e ^ 3)
        * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2] * ST)) *ᵥ u = f)
    ∧ (∀ g : Fin 3 × Fin 2 → ℝ,
      ∃! p : (Fin 3 → ℝ) × (Fin 3 × Fin 2 → ℝ),
        ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2])ᵀ
            * Matrix.diagonal
              (fun e => (200 : ℝ) * (1 / 100)
                / memberLength rT ![0, 0, 1] ![1, 2, 2] e ^ 3)
            * axialCompatibility rT ![0, 0, 1] ![1, 2, 2]) *ᵥ (ST *ᵥ p.1)
          = g + p.2 ∧ STᵀ *ᵥ p.2 = 0) :=
  supported_response_of_axial rT ![0, 0, 1] ![1, 2, 2] ST
    (fun _ => by norm_num) (fun _ => by norm_num)
    endpointsNeTri kernelTri

/-- Joints for the focused two-coordinate check. -/
private abbrev rF : Fin 3 → (Fin 2 → ℝ) := ![![0, 0], ![2, 0], ![1, 1]]

/-- Selection of joint 1's two coordinates. -/
private abbrev SF : Matrix (Fin 3 × Fin 2) (Fin 2) ℝ :=
  Matrix.of fun q f =>
    if (q = (1, 0) ∧ f = 0) ∨ (q = (1, 1) ∧ f = 1) then 1 else 0

/-- Supported action on the focused fixture:
`B S *ᵥ v = (2 v₀, v₀ - v₁)`. -/
private lemma supportedActionF (v : Fin 2 → ℝ) (e : Fin 2) :
    ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ v) e
      = ![2 * v 0, v 0 - v 1] e := by
  rw [← Matrix.mulVec_mulVec, axialCompatibility_mulVec_apply]
  fin_cases e
  · simp [Fin.sum_univ_two, SF, Matrix.mulVec, dotProduct]
  · simp [Fin.sum_univ_two, SF, Matrix.mulVec, dotProduct]
    ring

private lemma kernelF : ∀ v : Fin 2 → ℝ,
    (axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ v = 0 → v = 0 := by
  intro v hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  rw [supportedActionF] at h0 h1
  simp at h0 h1
  funext i
  fin_cases i <;> simp <;> linarith

/-- The focused stiffness is `[[5, -3], [-3, 3]]`. -/
private lemma supportedStiffnessF :
    (axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)
      = !![5, -3; -3, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal,
      axialCompatibility, SF, Matrix.of_apply, Fin.sum_univ_two] <;> norm_num

/-- Focused check as a truss instance:
`K *ᵥ ![3, 5] = ![0, 6]`, with `![3, 5]` the unique
response and the inverse image of the load. -/
example : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![3, 5]
        = ![0, 6]
    ∧ ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF))⁻¹ *ᵥ ![0, 6]
        = ![3, 5]
    ∧ ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![3, 5]
        ≠ ![0, -6] := by
  have hdirect : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![3, 5]
      = ![0, 6] := by
    rw [supportedStiffnessF]
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hPD : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF)).PosDef :=
    (supported_posDef_iff rF ![0, 1] ![1, 2] SF _
      (by intro e; fin_cases e <;> norm_num)).mpr kernelF
  refine ⟨hdirect, ?_, ?_⟩
  · exact ((supported_mulVec_eq_iff_inv_mulVec rF ![0, 1] ![1, 2]
      SF _ hPD).mp hdirect).symm
  · rw [hdirect]
    norm_num

/-- The mechanism `(0, 3, -4)` rules out unique response
for the two-member triangle. -/
example : ¬ ∃! u : Fin 3 → ℝ,
    ((axialCompatibility rT ![0, 0] ![1, 2] * ST)ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0] ![1, 2] * ST)) *ᵥ u = ![1, 0, 0] :=
  supported_not_existsUnique_of_kernel rT ![0, 0] ![1, 2] ST _
    (z := ![0, 3, -4]) (by simp) (by
      funext e
      rw [supportedActionTwo]
      fin_cases e
      · simp
      · simp
        norm_num) _

/-- A rigid `x`-translation rules out unique response on
the one-member table with `S = 1`. -/
example : ¬ ∃! u : Fin 3 × Fin 2 → ℝ,
    ((axialCompatibility r3 ![0] ![1] * S6)ᵀ
      * Matrix.diagonal (![1] : Fin 1 → ℝ)
      * (axialCompatibility r3 ![0] ![1] * S6)) *ᵥ u = 0 :=
  supported_not_existsUnique_of_kernel r3 ![0] ![1] S6 _
    (z := fun q => if q.2 = 0 then (1 : ℝ) else 0)
    (by
      intro h
      have h00 := congrFun h (0, 0)
      simp at h00)
    (by
      funext e
      fin_cases e
      simp only [Matrix.mulVec_apply, Matrix.row, dotProduct,
        Matrix.mul_apply, Matrix.one_apply, axialCompatibility,
        Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
        Fin.sum_univ_two, r3]
      norm_num) _

/-- With `S = 0`, every generalized coordinate is a null
mode, so there is no unique response. -/
example : ¬ ∃! u : Fin 3 → ℝ,
    ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 3) ℝ))ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 3) ℝ))) *ᵥ u = ![1, 0, 0] :=
  supported_not_existsUnique_of_kernel rT ![0, 0, 1] ![1, 2, 2] 0 _
    (z := ![1, 0, 0]) (by simp) (by simp) _

/-- With no members, a nonzero supported coordinate is a
null mode. -/
example : ¬ ∃! u : Fin 1 → ℝ,
    ((axialCompatibility (![![0, 0]] : Fin 1 → (Fin 2 → ℝ))
        ((fun _ => (0 : Fin 1)) : Fin 0 → Fin 1)
        ((fun _ => (0 : Fin 1)) : Fin 0 → Fin 1)
        * (0 : Matrix (Fin 1 × Fin 2) (Fin 1) ℝ))ᵀ
      * Matrix.diagonal (fun _ => (1 : ℝ))
      * (axialCompatibility (![![0, 0]] : Fin 1 → (Fin 2 → ℝ))
        ((fun _ => (0 : Fin 1)) : Fin 0 → Fin 1)
        ((fun _ => (0 : Fin 1)) : Fin 0 → Fin 1)
        * (0 : Matrix (Fin 1 × Fin 2) (Fin 1) ℝ))) *ᵥ u = ![1] :=
  supported_not_existsUnique_of_kernel _ _ _ 0 _
    (z := ![1]) (by simp)
    (by
      funext e
      exact (Nat.not_lt_zero _ e.2).elim) _

/-- Zero weights: no supported displacement solves the
nonzero one-coordinate load. -/
example : ¬ ∃! u : Fin 1 → ℝ,
    ((axialCompatibility rN ![0] ![1] * S1)ᵀ
      * Matrix.diagonal (fun _ => (0 : ℝ))
      * (axialCompatibility rN ![0] ![1] * S1)) *ᵥ u = ![1] := by
  rintro ⟨u, hu, -⟩
  have h0 : ((axialCompatibility rN ![0] ![1] * S1)ᵀ
      * Matrix.diagonal (fun _ => (0 : ℝ))
      * (axialCompatibility rN ![0] ![1] * S1)) *ᵥ u = 0 := by
    simp
  rw [h0] at hu
  have h00 := congrFun hu 0
  simp at h00

/-- Degenerate boundary: with no free coordinates the
unique (empty) response exists. -/
example : ∀ f : Fin 0 → ℝ, ∃! u : Fin 0 → ℝ,
    ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 0) ℝ))ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 0) ℝ))) *ᵥ u = f := by
  intro f
  refine supported_existsUnique rT ![0, 0, 1] ![1, 2, 2] 0 _ ?_ ?_ f
  · intro e
    norm_num
  · intro u _
    funext i
    exact (Nat.not_lt_zero _ i.2).elim

/-- Coincident endpoints fail the physical admission
`hne`; the abstract stiffness identity still applies. -/
example : ¬ ∀ e, (![![1, 1], ![1, 1]] : Fin 2 → (Fin 2 → ℝ)) (![0] e)
      ≠ (![![1, 1], ![1, 1]] : Fin 2 → (Fin 2 → ℝ)) (![1] e) := by
  intro h
  exact h 0 rfl

/-- Duplicate reaction columns send different coefficient
vectors to one joint vector, beside the unique residual
vector statement. -/
example : (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 0]
      = ![1, 0]
    ∧ (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 1]
      = ![1, 0] := by
  constructor <;>
    · funext i
      fin_cases i <;>
        norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

#print axioms Mechanics.TrussCompatibility.supported_posDef_iff
#print axioms
  Mechanics.TrussCompatibility.supported_posDef_iff_ker_eq_bot
#print axioms
  Mechanics.TrussCompatibility.supported_posDef_iff_of_axial
#print axioms Mechanics.TrussCompatibility.supported_stiffness_eq
#print axioms
  Mechanics.TrussCompatibility.supported_existsUnique_of_posDef
#print axioms
  Mechanics.TrussCompatibility.supported_mulVec_eq_iff_inv_mulVec
#print axioms Mechanics.TrussCompatibility.supported_existsUnique
#print axioms
  Mechanics.TrussCompatibility.supported_residual_existsUnique_of_posDef
#print axioms
  Mechanics.TrussCompatibility.supported_not_existsUnique_of_kernel
#print axioms Mechanics.TrussCompatibility.supported_response_of_axial

end PhyslibExtTest.Mechanics.TrussCompatibility
