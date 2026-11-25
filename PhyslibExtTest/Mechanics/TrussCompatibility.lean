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
supported response on triangle and focused fixtures,
and reciprocal work on the focused fixture, and
load-parameter identifiability checks, unit-load response checks, finite load hull checks, absolute envelope checks, and reduced determinate statics checks.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Row action and supported energy
- B. Supported virtual work
- C. Supported rigidity certificate
- D. Supported unique response
- E. Reciprocal work
- F. Load-parameter identifiability
- G. Unit-load response
- H. Finite load hull
- I. Reduced determinate statics

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
      Matrix.of_apply, dotProduct, fB, r3, -Matrix.transpose_of] <;> norm_num

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
        Matrix.of_apply, dotProduct, fB, r3, -Matrix.transpose_of] <;> norm_num
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
      axialCompatibility, SF, Matrix.of_apply, Fin.sum_univ_two, -Matrix.transpose_of] <;> norm_num

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


/-! ## E. Reciprocal work -/

/-- Second focused solution: `K *ᵥ ![1, 1] = ![2, 0]`. -/
private lemma focusedActionOne :
    ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![1, 1]
        = ![2, 0] := by
  rw [supportedStiffnessF]
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Reciprocal work on the focused fixture through the
symmetry-certificate form: the two independent loads
`![0, 6]` and `![2, 0]` have equal cross work. -/
example : (![0, 6] : Fin 2 → ℝ) ⬝ᵥ ![1, 1]
    = (![2, 0] : Fin 2 → ℝ) ⬝ᵥ ![3, 5] := by
  have hu : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![3, 5]
      = ![0, 6] := by
    rw [supportedStiffnessF]
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact supported_reciprocalWork rF ![0, 1] ![1, 2] SF _ hu
    focusedActionOne

/-- The common cross-work value is `6 ≠ 0`, and the two
loads are independent. -/
example : (![0, 6] : Fin 2 → ℝ) ⬝ᵥ ![1, 1] = 6 ∧
    Matrix.det !![0, 2; 6, 0] = -12 := by
  norm_num [dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]

/-- The bilinear pairing form on the same data, without
naming loads. -/
example : ![3, 5] ⬝ᵥ (((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![1, 1])
    = ![1, 1] ⬝ᵥ (((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![3, 5]) :=
  supported_dotProduct_mulVec_comm rF ![0, 1] ![1, 2] SF _ _ _

/-- Physical axial weights `E A / L ^ 3` on the focused
fixture: reciprocal work for arbitrary supported
displacements, loads taken as the stiffness images. -/
example (u v : Fin 2 → ℝ) :
    (((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal
          (fun e => (200 : ℝ) * (1 / 100)
            / memberLength rF ![0, 1] ![1, 2] e ^ 3)
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ u) ⬝ᵥ v
      = (((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal
          (fun e => (200 : ℝ) * (1 / 100)
            / memberLength rF ![0, 1] ![1, 2] e ^ 3)
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ v) ⬝ᵥ u := by
  exact supported_reciprocalWork rF ![0, 1] ![1, 2] SF _ rfl rfl

/-- Different stiffness control: cross work against a
load vector produced by a different operator need not
agree (`6 ≠ 11`). -/
example : (![0, 6] : Fin 2 → ℝ) ⬝ᵥ ![1, 1] = 6 ∧
    (![2, 1] : Fin 2 → ℝ) ⬝ᵥ ![3, 5] = 11 ∧ (6 : ℝ) ≠ 11 := by
  norm_num [dotProduct, Fin.sum_univ_two]

/-- Nonsymmetric control: `!![5, -3; 0, 3]` is not
symmetric and its two pairings differ (`15 ≠ 21`). -/
example : ¬ (!![5, -3; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ).IsSymm := by
  intro h
  have h01 := Matrix.IsSymm.apply h 0 1
  norm_num at h01

example : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ
      ((!![5, -3; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 5]) = 15 ∧
    (![3, 5] : Fin 2 → ℝ) ⬝ᵥ
      ((!![5, -3; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 1]) = 21 ∧
    (15 : ℝ) ≠ 21 := by
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Zero-load boundary: the zero solution against the
second focused solution. -/
example : (0 : Fin 2 → ℝ) ⬝ᵥ ![1, 1]
    = (![2, 0] : Fin 2 → ℝ) ⬝ᵥ 0 :=
  supported_reciprocalWork rF ![0, 1] ![1, 2] SF _
    (by simp) focusedActionOne

/-- Singular-stiffness control: with `S = 0` the
supported stiffness is zero (not positive definite), and
reciprocal work still holds for the solutions in range
(zero loads). -/
example (u v : Fin 3 → ℝ) :
    (0 : Fin 3 → ℝ) ⬝ᵥ v = (0 : Fin 3 → ℝ) ⬝ᵥ u :=
  supported_reciprocalWork rT ![0, 0, 1] ![1, 2, 2] 0 (fun _ => (2 : ℝ))
    (by simp) (by simp)

/-- Empty-coordinate boundary. -/
example (u v f g : Fin 0 → ℝ)
    (hu : ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 0) ℝ))ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 0) ℝ))) *ᵥ u = f)
    (hv : ((axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 0) ℝ))ᵀ
      * Matrix.diagonal (fun _ => (2 : ℝ))
      * (axialCompatibility rT ![0, 0, 1] ![1, 2, 2]
        * (0 : Matrix (Fin 3 × Fin 2) (Fin 0) ℝ))) *ᵥ v = g) :
    f ⬝ᵥ v = g ⬝ᵥ u :=
  supported_reciprocalWork rT ![0, 0, 1] ![1, 2, 2] 0 _ hu hv

/-- Sign-flip control: negating one load negates exactly
one side. -/
example : (![0, -6] : Fin 2 → ℝ) ⬝ᵥ ![1, 1] = -6 ∧ (-6 : ℝ) ≠ 6 := by
  norm_num [dotProduct, Fin.sum_univ_two]


/-! ## F. Load-parameter identifiability -/

/-- Positive definiteness of the focused supported
stiffness, from the rigidity certificate. -/
private lemma posDefF :
    ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF)).PosDef :=
  (supported_posDef_iff rF ![0, 1] ![1, 2] SF _
    (by intro e; fin_cases e <;> norm_num)).mpr kernelF

/-- Forward observation on the focused fixture: the
supported displacement `![3, 5]` at load `![0, 6]` is
observed through the identity sensor as the observation
matrix applied to the load parameter. -/
example : (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 5]
    = loadObservationMatrix rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
        1 1 *ᵥ ![0, 6] := by
  have hu : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![3, 5]
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 6] := by
    rw [Matrix.one_mulVec, supportedStiffnessF]
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact loadObservation_eq_of_supported_eq rF ![0, 1] ![1, 2] SF _
    posDefF _ _ hu

/-- Known stiffness, unknown loads: with identity sensor
and load basis, load parameters are identifiable on the
full affine space through the focused observation
matrix. -/
example : Statistics.UncertaintyPropagation.IdentifiableOnAffine
    (loadObservationMatrix rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (AffineSubspace.mk' (0 : Fin 2 → ℝ) ⊤) :=
  loadObservation_identifiableOnAffine_of_kernels rF ![0, 1] ![1, 2] SF _
    posDefF _ _ _ _
    (by intro w hw; simpa using hw) (by intro v _ hw; simpa using hw)

/-- Rank-deficient sensor, zero map: every parameter
direction is killed, so a distinct parameter shares the
observation. -/
example : ∃ θ' : Fin 2 → ℝ, θ' ≠ ![0, 6] ∧
    loadObservationMatrix rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
        (0 : Matrix (Fin 2) (Fin 2) ℝ) 1 *ᵥ θ' = 0 := by
  refine ⟨![1, 0], by norm_num, ?_⟩
  simp [loadObservationMatrix]

/-- Rank-deficient sensor, duplicated rows: the realized
displacement direction `![0, 1]` is invisible, and the
load `![-3, 3]` producing it is a kernel direction of
the observation matrix. -/
example : loadObservationMatrix rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
      !![1, 0; 1, 0] 1 *ᵥ ![-3, 3] = 0 := by
  have hu : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![0, 1]
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![-3, 3] := by
    rw [Matrix.one_mulVec, supportedStiffnessF]
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h := loadObservation_eq_of_supported_eq rF ![0, 1] ![1, 2] SF _
    posDefF !![1, 0; 1, 0] 1 hu
  rw [← h]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Zero load-basis column: the second load parameter
never reaches the structure. -/
example : loadObservationMatrix rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
      (1 : Matrix (Fin 2) (Fin 2) ℝ) !![1, 0; 0, 0] *ᵥ ![0, 1] = 0 := by
  have h0 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 1] = 0 := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  unfold loadObservationMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h0,
    Matrix.mulVec_zero, Matrix.mulVec_zero]

/-- Under-sensed: one sensor against two basis degrees
of freedom is not identifiable. -/
example : ¬ Statistics.UncertaintyPropagation.Identifiable
    (loadObservationMatrix rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
      (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      * (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
  Statistics.UncertaintyPropagation.not_identifiable_of_lt (by norm_num) _

/-- Stiffness scope guard values: the scalar response
`1, 1/2, 1/3` at stiffnesses `1, 2, 3` is not an affine
function of stiffness (the guard theorem). -/
example : (1 : ℝ)⁻¹ = 1 ∧ (2 : ℝ)⁻¹ = 1 / 2 ∧ (3 : ℝ)⁻¹ = 1 / 3 := by
  norm_num

/-! ## G. Unit-load response -/

/-- Positive definiteness of the focused supported
stiffness, from the rigidity certificate. -/
private lemma posDefUnitLoad :
    ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF)).PosDef :=
  (supported_posDef_iff rF ![0, 1] ![1, 2] SF _
    (by intro e; fin_cases e <;> norm_num)).mpr kernelF

/-- Focused solve `K *ᵥ ![3, 5] = ![0, 6]`. -/
private lemma huUnitLoad :
    ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![3, 5]
        = ![0, 6] := by
  rw [supportedStiffnessF]
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The influence vector for output `![2, 0]` on the
focused fixture is `![1, 1]`. -/
private lemma etaUnitLoad :
    influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
      = ![1, 1] := by
  have h : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![1, 1]
      = ![2, 0] := by
    rw [supportedStiffnessF]
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h2 := (supported_mulVec_eq_iff_inv_mulVec rF ![0, 1] ![1, 2] SF _
    posDefUnitLoad).mp h
  exact h2.symm

/-- Flexibility recovery at the focused data. -/
example : Matrix.diagonal (fun e => (![1 / 2, 3] e)⁻¹)
      *ᵥ (Matrix.diagonal ![1 / 2, 3]
        *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![3, 5]))
    = (axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![3, 5] :=
  supported_invDiagonal_mulVec_memberCoefficient rF ![0, 1] ![1, 2] SF _
    (by intro e; fin_cases e <;> norm_num) _

/-- The influence vector solves the unit-load system. -/
example : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF))
    *ᵥ influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
      = ![2, 0] :=
  supported_influenceVector_mulVec rF ![0, 1] ![1, 2] SF _
    posDefUnitLoad _

/-- Response at the focused load: common value `6`. -/
example : unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
      ![0, 6] = ![2, 0] ⬝ᵥ ![3, 5]
    ∧ unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
      ![0, 6] = 6 := by
  have h := supported_unitLoadResponse_eq rF ![0, 1] ![1, 2] SF _
    posDefUnitLoad ![2, 0] huUnitLoad
  refine ⟨h, ?_⟩
  rw [h]
  norm_num [dotProduct, Fin.sum_univ_two]

/-- Elongation and flexibility forms of the unit-load
identity at the focused data. -/
example : ![2, 0] ⬝ᵥ ![3, 5]
    = (Matrix.diagonal ![1 / 2, 3]
        *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF)
          *ᵥ influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]))
      ⬝ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![3, 5]) := by
  have h := supported_unitLoad_identity_separationForm rF ![0, 1] ![1, 2] SF _
    posDefUnitLoad ![2, 0] huUnitLoad
  exact h

example : ![2, 0] ⬝ᵥ ![3, 5]
    = (Matrix.diagonal ![1 / 2, 3]
        *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF)
          *ᵥ influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]))
      ⬝ᵥ (Matrix.diagonal (fun e => (![1 / 2, 3] e)⁻¹)
        *ᵥ (Matrix.diagonal ![1 / 2, 3]
          *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![3, 5]))) := by
  have h := supported_unitLoad_identity rF ![0, 1] ![1, 2] SF _
    (by intro e; fin_cases e <;> norm_num) posDefUnitLoad ![2, 0] huUnitLoad
  exact h

/-- The certified (kernel) form at the same data. -/
example : ![2, 0] ⬝ᵥ ![3, 5]
    = (Matrix.diagonal ![1 / 2, 3]
        *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF)
          *ᵥ influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]))
      ⬝ᵥ (Matrix.diagonal (fun e => (![1 / 2, 3] e)⁻¹)
        *ᵥ (Matrix.diagonal ![1 / 2, 3]
          *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![3, 5]))) := by
  have h := supported_unitLoad_identity_of_kernel rF ![0, 1] ![1, 2] SF _
    (by intro e; fin_cases e <;> norm_num) kernelF ![2, 0] huUnitLoad
  exact h

/-- Superposition at the fixed output: responses
`6`, `2`, summed response `8`. -/
example : unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
      (![0, 6] + ![2, 0]) = 8
    ∧ unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
      (![0, 6] + ![2, 0])
    = unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0] ![0, 6]
      + unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        ![2, 0] := by
  refine ⟨?_, map_add _ _ _⟩
  rw [unitLoadResponse_apply]
  rw [etaUnitLoad]
  norm_num [dotProduct, Fin.sum_univ_two]

/-- Coordinate outputs extract displacement components
`u 0 = 3`, `u 1 = 5`; the second is the wrong-output
control against `6`. -/
example : unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![1, 0]
      ![0, 6] = 3
    ∧ unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![0, 1]
      ![0, 6] = 5
    ∧ (5 : ℝ) ≠ 6 := by
  refine ⟨?_, ?_, by norm_num⟩
  · rw [supported_unitLoadResponse_eq rF ![0, 1] ![1, 2] SF _
      posDefUnitLoad _ huUnitLoad]
    norm_num [dotProduct, Fin.sum_univ_two]
  · rw [supported_unitLoadResponse_eq rF ![0, 1] ![1, 2] SF _
      posDefUnitLoad _ huUnitLoad]
    norm_num [dotProduct, Fin.sum_univ_two]

/-- Scaled output: response `12`. -/
example : unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
      ((2 : ℝ) • ![2, 0]) ![0, 6] = 12 := by
  have heta2 : influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
        ((2 : ℝ) • ![2, 0]) = ![2, 2] := by
    have h := supported_influenceVector_smul rF ![0, 1] ![1, 2] SF
      ![1 / 2, 3] 2 ![2, 0]
    rw [etaUnitLoad] at h
    refine h.trans ?_
    funext i
    fin_cases i <;> simp
  rw [unitLoadResponse_apply]
  rw [heta2]
  norm_num [dotProduct, Fin.sum_univ_two]

/-- Physical axial-force conversion at the focused data:
coefficients `![3, -6]` and unit-load coefficients
`![1, 0]` rescale by member lengths `2`, `√2` to physical
forces `![6, -6 √2]` and `![2, 0]`, and the physical
identity holds through the conversion theorem. -/
example : (![2, 0] : Fin 2 → ℝ) ⬝ᵥ ![3, 5]
    = (fun e => (Matrix.diagonal ![1 / 2, 3]
          *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF)
            *ᵥ influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
              ![2, 0])) e * memberLength rF ![0, 1] ![1, 2] e)
      ⬝ᵥ (fun e => ((Matrix.diagonal ![1 / 2, 3]
            *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF)
              *ᵥ ![3, 5])) e * memberLength rF ![0, 1] ![1, 2] e)
          / (![1 / 2, 3] e * memberLength rF ![0, 1] ![1, 2] e ^ 2)) := by
  have h := supported_unitLoad_axialForce_identity rF ![0, 1] ![1, 2] SF _
    (by intro e; fin_cases e <;> norm_num) posDefUnitLoad
    (by intro e; fin_cases e <;> norm_num [rF]) ![2, 0] huUnitLoad
  exact h

example : (fun e => (Matrix.diagonal ![1 / 2, 3]
        *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![3, 5])) e
      * memberLength rF ![0, 1] ![1, 2] e)
    = ![6, -6 * Real.sqrt 2] := by
  funext e
  fin_cases e
  · simp only [Matrix.mulVec_diagonal]
    rw [supportedActionF]
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num [memberLength, h4]
  · simp only [Matrix.mulVec_diagonal]
    rw [supportedActionF]
    norm_num [memberLength]

/-- Zero load: response `0`, and the degenerate identity
at `f = u = 0`. -/
example : unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0] 0
    = 0 :=
  map_zero _

example : (![2, 0] : Fin 2 → ℝ) ⬝ᵥ 0
    = (Matrix.diagonal ![1 / 2, 3]
        *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF)
          *ᵥ influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]))
      ⬝ᵥ (Matrix.diagonal (fun e => (![1 / 2, 3] e)⁻¹)
        *ᵥ (Matrix.diagonal ![1 / 2, 3]
          *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ 0))) := by
  have h := supported_unitLoad_identity rF ![0, 1] ![1, 2] SF _
    (by intro e; fin_cases e <;> norm_num) posDefUnitLoad ![2, 0]
    (f := 0) (u := 0) (by simp)
  exact h

/-- Zero-diagonal control: without positivity the
pointwise inverse diagonal does not recover the vector
(`![0, -2] ≠ ![6, -2]`). -/
example : Matrix.diagonal (fun e => ((![0, 3] : Fin 2 → ℝ) e)⁻¹)
      *ᵥ (Matrix.diagonal ![0, 3] *ᵥ ![6, -2]) = ![0, -2]
    ∧ (![0, -2] : Fin 2 → ℝ) ≠ ![6, -2] := by
  refine ⟨?_, by norm_num⟩
  funext i
  fin_cases i <;> norm_num [Matrix.mulVec_diagonal]

/-- Mechanism premise guard: the two-member triangle
stiffness is not positive definite. -/
example : ¬ ((axialCompatibility rT ![0, 0] ![1, 2] * ST)ᵀ
    * Matrix.diagonal (fun _ => (2 : ℝ))
    * (axialCompatibility rT ![0, 0] ![1, 2] * ST)).PosDef := by
  rw [supported_posDef_iff _ _ _ _ _ (fun _ => by norm_num)]
  intro h
  have hBz : (axialCompatibility rT ![0, 0] ![1, 2] * ST)
      *ᵥ ![0, 3, -4] = 0 := by
    funext e
    rw [supportedActionTwo]
    fin_cases e
    · simp
    · simp
      norm_num
  exact (by norm_num : ![0, 3, -4] ≠ (0 : Fin 3 → ℝ)) (h _ hBz)

/-- Different stiffness behind the influence vector:
unit weights give response `3 ≠ 6` at the same load. -/
example : unitLoadResponse rF ![0, 1] ![1, 2] SF ![1, 1] ![2, 0]
      ![0, 6] = 3 ∧ (3 : ℝ) ≠ 6 := by
  have hPD1 : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1, 1]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)).PosDef :=
    (supported_posDef_iff rF ![0, 1] ![1, 2] SF _
      (by intro e; fin_cases e <;> norm_num)).mpr kernelF
  have hu1 : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1, 1]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![3 / 2, 15 / 2]
      = ![0, 6] := by
    have hK : (axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
          * Matrix.diagonal ![1, 1]
          * (axialCompatibility rF ![0, 1] ![1, 2] * SF)
        = !![5, -1; -1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal,
          axialCompatibility, SF, Matrix.of_apply, Fin.sum_univ_two, -Matrix.transpose_of] <;>
        norm_num
    rw [hK]
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨?_, by norm_num⟩
  rw [supported_unitLoadResponse_eq rF ![0, 1] ![1, 2] SF _ hPD1 _
    hu1]
  norm_num [dotProduct, Fin.sum_univ_two]

/-- Sign flip: negating the load negates the response. -/
example : unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
      (-![0, 6]) = -6 ∧ (-6 : ℝ) ≠ 6 := by
  refine ⟨?_, by norm_num⟩
  rw [unitLoadResponse_apply]
  rw [etaUnitLoad]
  norm_num [dotProduct, Fin.sum_univ_two]

/-- Empty-coordinate boundary: the response over no
coordinates is `0`. -/
example (aout f : Fin 0 → ℝ) :
    unitLoadResponse rT ![0, 0, 1] ![1, 2, 2]
      (0 : Matrix (Fin 3 × Fin 2) (Fin 0) ℝ) (fun _ => (2 : ℝ))
      aout f = 0 := by
  simp [unitLoadResponse, dotProduct]

/-! ## H. Finite load hull -/

/-- Three scenario loads on the focused fixture, with
responses `6`, `2`, `0` at output `![2, 0]`. -/
private abbrev hullLoads : Fin 3 → (Fin 2 → ℝ) :=
  ![![0, 6], ![2, 0], ![0, 0]]

/-- The corresponding supported solutions. -/
private abbrev hullSols : Fin 3 → (Fin 2 → ℝ) :=
  ![![3, 5], ![1, 1], ![0, 0]]

/-- Convex weights `(1/2, 1/3, 1/6)` on the three
scenarios. -/
private noncomputable abbrev hullWeights : Fin 3 → ℝ := ![1 / 2, 1 / 3, 1 / 6]

private lemma hullNonempty :
    (Finset.univ : Finset (Fin 3)).Nonempty :=
  ⟨0, Finset.mem_univ 0⟩

private lemma hullResp : ∀ i : Fin 3,
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (hullLoads i)
      = ![6, 2, 0] i := by
  intro i
  fin_cases i <;> rw [unitLoadResponse_apply, etaUnitLoad] <;>
    norm_num [dotProduct, Fin.sum_univ_two, hullLoads]

private lemma hullOut : ∀ i : Fin 3,
    ![2, 0] ⬝ᵥ hullSols i = ![6, 2, 0] i := by
  intro i
  fin_cases i <;>
    norm_num [dotProduct, Fin.sum_univ_two, hullSols]

private lemma hullWeights_nonneg :
    ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ hullWeights i := by
  intro i _
  fin_cases i <;> norm_num [hullWeights]

private lemma hullWeights_sum :
    ∑ i ∈ (Finset.univ : Finset (Fin 3)), hullWeights i = 1 := by
  norm_num [Fin.sum_univ_three, hullWeights]

private lemma hullSolve :
    ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF))
        *ᵥ hullSols i
      = hullLoads i := by
  intro i _
  fin_cases i
  · simpa [hullSols, hullLoads] using huUnitLoad
  · rw [supportedStiffnessF]
    funext j
    fin_cases j <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        hullSols, hullLoads]
  · funext j
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        hullSols, hullLoads]

private lemma hullCombinedSolve :
    ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF))
      *ᵥ ![11 / 6, 17 / 6]
    = ∑ i ∈ (Finset.univ : Finset (Fin 3)),
        hullWeights i • hullLoads i := by
  rw [supportedStiffnessF]
  funext j
  fin_cases j <;>
    norm_num [Fin.sum_univ_three, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, hullWeights, hullLoads, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]

private lemma hullCombined :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          hullWeights i • hullLoads i)
      = 11 / 3 := by
  rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_three]
  simp only [hullResp]
  norm_num [hullWeights]

private lemma hullInf :
    (Finset.univ : Finset (Fin 3)).inf' hullNonempty
        (fun i => unitLoadResponse rF ![0, 1] ![1, 2] SF
          ![1 / 2, 3] ![2, 0] (hullLoads i))
      = 0 := by
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i => unitLoadResponse rF ![0, 1] ![1, 2] SF
        ![1 / 2, 3] ![2, 0] (hullLoads i)) (Finset.mem_univ 2)
    rwa [hullResp 2] at h
  · apply Finset.le_inf'
    intro i _
    rw [hullResp i]
    fin_cases i <;> norm_num

private lemma hullSup :
    (Finset.univ : Finset (Fin 3)).sup' hullNonempty
        (fun i => unitLoadResponse rF ![0, 1] ![1, 2] SF
          ![1 / 2, 3] ![2, 0] (hullLoads i))
      = 6 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rw [hullResp i]
    fin_cases i <;> norm_num
  · have h := Finset.le_sup'
      (fun i => unitLoadResponse rF ![0, 1] ![1, 2] SF
        ![1 / 2, 3] ![2, 0] (hullLoads i)) (Finset.mem_univ 0)
    rwa [hullResp 0] at h

/-- W1: the three-way agreement at response `11 / 3`,
strictly inside the hull `[0, 6]`, in response form and
in fixed-output form. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          hullWeights i • hullLoads i)
      = 11 / 3
    ∧ (0 : ℝ)
      ≤ unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          (∑ i ∈ (Finset.univ : Finset (Fin 3)),
            hullWeights i • hullLoads i)
    ∧ unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          (∑ i ∈ (Finset.univ : Finset (Fin 3)),
            hullWeights i • hullLoads i)
      ≤ 6
    ∧ (![2, 0] : Fin 2 → ℝ) ⬝ᵥ (![11 / 6, 17 / 6] : Fin 2 → ℝ) = 11 / 3 := by
  have h := supported_unitLoadResponse_convexCombination_bounds
    rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0] Finset.univ hullNonempty
    hullWeights hullLoads hullWeights_nonneg hullWeights_sum
  rw [hullInf, hullSup] at h
  exact ⟨hullCombined, h.1, h.2, by
    norm_num [dotProduct, Fin.sum_univ_two]⟩

/-- W1 in fixed-output form, through the bridge theorem. -/
example :
    (Finset.univ : Finset (Fin 3)).inf' hullNonempty
        (fun i => ![2, 0] ⬝ᵥ hullSols i)
        ≤ ![2, 0] ⬝ᵥ ![11 / 6, 17 / 6]
      ∧ ![2, 0] ⬝ᵥ ![11 / 6, 17 / 6]
        ≤ (Finset.univ : Finset (Fin 3)).sup' hullNonempty
          (fun i => ![2, 0] ⬝ᵥ hullSols i) :=
  supported_unitLoadResponse_convexCombination_output_bounds
    rF ![0, 1] ![1, 2] SF ![1 / 2, 3] posDefUnitLoad ![2, 0]
    Finset.univ
    hullNonempty hullWeights hullLoads hullSols _
    hullWeights_nonneg hullWeights_sum hullSolve
    hullCombinedSolve

/-- Boundary attainment: weights `(1, 0, 0)` attain the
upper hull endpoint, so the bound is non-strict. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          (![1, 0, 0] : Fin 3 → ℝ) i • hullLoads i)
      = 6 := by
  rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_three]
  simp only [hullResp]
  norm_num

/-- Singleton table: the response equality and the hull
collapse to the single vertex response. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (∑ j ∈ ({0} : Finset (Fin 3)),
          (![1, 0, 0] : Fin 3 → ℝ) j • hullLoads j)
      = unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0] (hullLoads 0)
    ∧ ({0} : Finset (Fin 3)).inf' (Finset.singleton_nonempty 0)
        (fun i => unitLoadResponse rF ![0, 1] ![1, 2] SF
          ![1 / 2, 3] ![2, 0] (hullLoads i))
      = unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0] (hullLoads 0)
    ∧ ({0} : Finset (Fin 3)).sup' (Finset.singleton_nonempty 0)
        (fun i => unitLoadResponse rF ![0, 1] ![1, 2] SF
          ![1 / 2, 3] ![2, 0] (hullLoads i))
      = unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0] (hullLoads 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact supported_unitLoadResponse_singleton rF
      ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0] 0
      (![1, 0, 0] : Fin 3 → ℝ) hullLoads
      (by norm_num [Finset.sum_singleton])
  · rw [Finset.inf'_singleton]
  · rw [Finset.sup'_singleton]

/-- Empty table rejected: no nonempty proof and no
coefficients summing to one. -/
example : ¬ (∅ : Finset (Fin 3)).Nonempty
    ∧ ∀ w : Fin 3 → ℝ,
      ¬ (∑ i ∈ (∅ : Finset (Fin 3)), w i = 1) := by
  simp

/-- Negative control against nonnegativity: weights
`(2, -1, 0)` still sum to one and superposition still
holds, but the response `10` escapes the hull top `6`. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          (![2, -1, 0] : Fin 3 → ℝ) i • hullLoads i)
      = 10
    ∧ ¬ unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          (∑ i ∈ (Finset.univ : Finset (Fin 3)),
            (![2, -1, 0] : Fin 3 → ℝ) i • hullLoads i)
      ≤ (Finset.univ : Finset (Fin 3)).sup' hullNonempty
          (fun i => unitLoadResponse rF ![0, 1] ![1, 2] SF
            ![1 / 2, 3] ![2, 0] (hullLoads i)) := by
  have hv :
      unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          (∑ i ∈ (Finset.univ : Finset (Fin 3)),
            (![2, -1, 0] : Fin 3 → ℝ) i • hullLoads i)
        = 10 := by
    rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_three]
    simp only [hullResp]
    norm_num
  rw [hv, hullSup]
  norm_num

/-- Negative control against normalization: weights
`(1, 1, 0)` are nonnegative and superposition still
holds, but the response `8` escapes the hull top `6`. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          (![1, 1, 0] : Fin 3 → ℝ) i • hullLoads i)
      = 8 := by
  rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_three]
  simp only [hullResp]
  norm_num

/-- Duplicate scenarios keep distinct coefficients: loads
`(f₀, f₀, f₁)` with weights `(1/4, 1/4, 1/2)` respond
`4`, inside the same hull. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          (![1 / 4, 1 / 4, 1 / 2] : Fin 3 → ℝ) i
            • hullLoads ((![0, 0, 1] : Fin 3 → Fin 3) i))
      = 4 := by
  have hresp : ∀ i : Fin 3,
      unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0] (hullLoads ((![0, 0, 1] : Fin 3 → Fin 3) i))
        = ![6, 6, 2] i := by
    intro i
    fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, hullResp] <;> norm_num
  rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_three]
  simp only [hresp]
  norm_num

/-- Degenerate output space `F = Fin 0`: every pairing is
the empty sum. -/
example (eta f : Fin 0 → ℝ) : eta ⬝ᵥ f = 0 := by
  simp [dotProduct]

/-- Opposite-sign scenario loads on the focused fixture,
with responses `6`, `-4`, `0`. -/
private abbrev absLoads : Fin 3 → (Fin 2 → ℝ) :=
  ![![0, 6], ![-10, 6], ![0, 0]]

/-- The corresponding supported solutions. -/
private abbrev absSols : Fin 3 → (Fin 2 → ℝ) :=
  ![![3, 5], ![-2, 0], ![0, 0]]

private lemma absResp : ∀ i : Fin 3,
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (absLoads i)
      = ![6, -4, 0] i := by
  intro i
  fin_cases i <;> rw [unitLoadResponse_apply, etaUnitLoad] <;>
    norm_num [dotProduct, Fin.sum_univ_two, absLoads]

private lemma absSolve :
    ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF))
        *ᵥ absSols i
      = absLoads i := by
  intro i _
  fin_cases i
  · simpa [absSols, absLoads] using huUnitLoad
  · rw [supportedStiffnessF]
    funext j
    fin_cases j <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        absSols, absLoads]
  · funext j
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        absSols, absLoads]

private lemma absCombinedSolve :
    ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF))
      *ᵥ ![5 / 6, 5 / 2]
    = ∑ i ∈ (Finset.univ : Finset (Fin 3)),
        hullWeights i • absLoads i := by
  rw [supportedStiffnessF]
  funext j
  fin_cases j <;>
    norm_num [Fin.sum_univ_three, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, hullWeights, absLoads, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]

private lemma absSup :
    (Finset.univ : Finset (Fin 3)).sup' hullNonempty
        (fun i => |unitLoadResponse rF ![0, 1] ![1, 2] SF
          ![1 / 2, 3] ![2, 0] (absLoads i)|)
      = 6 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rw [absResp i]
    fin_cases i <;> norm_num
  · have h := Finset.le_sup'
      (fun i => |unitLoadResponse rF ![0, 1] ![1, 2] SF
        ![1 / 2, 3] ![2, 0] (absLoads i)|) (Finset.mem_univ 0)
    rw [absResp 0] at h
    have h6 : (6 : ℝ) = |![6, -4, 0] 0| := by norm_num
    rw [h6]
    exact h

private lemma absCombined :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          hullWeights i • absLoads i)
      = 5 / 3 := by
  rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_three]
  simp only [absResp]
  norm_num [hullWeights]

/-- W1: opposite signs with a zero response; the combined
response `5 / 3` is inside the absolute envelope `6`. -/
example :
    |unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
        ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          hullWeights i • absLoads i)|
      ≤ 6 := by
  have h := supported_abs_unitLoadResponse_sum_smul_le_sup'_abs
    rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0] Finset.univ
    hullNonempty hullWeights absLoads hullWeights_nonneg
    hullWeights_sum
  rwa [absSup] at h

/-- W1 in fixed-output form, through the bridge theorem;
the combined output is `5 / 3`. -/
example :
    |![2, 0] ⬝ᵥ ![5 / 6, 5 / 2]|
      ≤ (Finset.univ : Finset (Fin 3)).sup' hullNonempty
          (fun i => |![2, 0] ⬝ᵥ absSols i|)
    ∧ (![2, 0] : Fin 2 → ℝ) ⬝ᵥ (![5 / 6, 5 / 2] : Fin 2 → ℝ)
      = 5 / 3 := by
  refine ⟨supported_abs_convexCombination_output_le_sup'_abs
    rF ![0, 1] ![1, 2] SF ![1 / 2, 3] posDefUnitLoad ![2, 0]
    Finset.univ hullNonempty hullWeights absLoads absSols _
    hullWeights_nonneg hullWeights_sum absSolve
    absCombinedSolve, by
    norm_num [dotProduct, Fin.sum_univ_two]⟩

/-- W1b: responses `(2, -6)` with weights `(1/4, 3/4)`
give combined response `-4`; its absolute value `4`
exceeds the signed maximum `2` and is bounded by the
absolute envelope `6`. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 2)),
          (![1 / 4, 3 / 4] : Fin 2 → ℝ) i
            • (![![2, 0], ![-15, 9]] : Fin 2 → (Fin 2 → ℝ)) i)
      = -4
    ∧ ¬ |unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          (∑ i ∈ (Finset.univ : Finset (Fin 2)),
            (![1 / 4, 3 / 4] : Fin 2 → ℝ) i
              • (![![2, 0], ![-15, 9]] : Fin 2 → (Fin 2 → ℝ)) i)|
      ≤ 2 := by
  have hresp : ∀ i : Fin 2,
      unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          ((![![2, 0], ![-15, 9]] : Fin 2 → (Fin 2 → ℝ)) i)
        = ![2, -6] i := by
    intro i
    fin_cases i <;> rw [unitLoadResponse_apply, etaUnitLoad] <;>
      norm_num [dotProduct, Fin.sum_univ_two]
  have hv :
      unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          (∑ i ∈ (Finset.univ : Finset (Fin 2)),
            (![1 / 4, 3 / 4] : Fin 2 → ℝ) i
              • (![![2, 0], ![-15, 9]] : Fin 2 → (Fin 2 → ℝ)) i)
        = -4 := by
    rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_two]
    simp only [hresp]
    norm_num
  rw [hv]
  norm_num

/-- Boundary attainment on the positive side: weights
`(1, 0, 0)` attain the absolute envelope. -/
example :
    |unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
        ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          (![1, 0, 0] : Fin 3 → ℝ) i • absLoads i)|
      = 6 := by
  have hv :
      unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          (∑ i ∈ (Finset.univ : Finset (Fin 3)),
            (![1, 0, 0] : Fin 3 → ℝ) i • absLoads i)
        = 6 := by
    rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_three]
    simp only [absResp]
    norm_num
  rw [hv]
  norm_num

/-- Zero responses from a nonzero load: both vertex
responses are `0`, the absolute envelope is `0`, and the
combined response is forced to `0`. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 2)),
          (![2 / 5, 3 / 5] : Fin 2 → ℝ) i
            • (![![-3, 3], ![0, 0]] : Fin 2 → (Fin 2 → ℝ)) i)
      = 0 := by
  have hresp : ∀ i : Fin 2,
      unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          ((![![-3, 3], ![0, 0]] : Fin 2 → (Fin 2 → ℝ)) i)
        = 0 := by
    intro i
    fin_cases i <;> rw [unitLoadResponse_apply, etaUnitLoad] <;>
      norm_num [dotProduct, Fin.sum_univ_two]
  rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_two]
  simp only [hresp]
  norm_num

/-- Negative control against nonnegativity for the
absolute bound: weights `(2, -1, 0)` on responses
`(6, 2, 0)` give absolute response `10 > 6`. -/
example :
    |unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
        ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          (![2, -1, 0] : Fin 3 → ℝ) i • hullLoads i)|
      = 10 := by
  have hv :
      unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          (∑ i ∈ (Finset.univ : Finset (Fin 3)),
            (![2, -1, 0] : Fin 3 → ℝ) i • hullLoads i)
        = 10 := by
    rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_three]
    simp only [hullResp]
    norm_num
  rw [hv]
  norm_num

/-- Negative control against normalization for the
absolute bound: weights `(1, 1, 0)` on responses
`(6, 2, 0)` give absolute response `8 > 6`. -/
example :
    |unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
        ![2, 0]
        (∑ i ∈ (Finset.univ : Finset (Fin 3)),
          (![1, 1, 0] : Fin 3 → ℝ) i • hullLoads i)|
      = 8 := by
  have hv :
      unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![2, 0]
          (∑ i ∈ (Finset.univ : Finset (Fin 3)),
            (![1, 1, 0] : Fin 3 → ℝ) i • hullLoads i)
        = 8 := by
    rw [supported_unitLoadResponse_sum_smul, Fin.sum_univ_three]
    simp only [hullResp]
    norm_num
  rw [hv]
  norm_num

/-! ## I. Reduced determinate statics -/

/-- W1 data: `Bs = !![2, 0; 1, -1]` is invertible. -/
private lemma detBsW1 :
    IsUnit (!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_fin_two]
  norm_num

/-- W1 first solution: weights `![1/2, 3]`, displacement
`![3, 5]`, load `![0, 6]`. -/
private lemma w1SolutionOne :
    ((!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ
      * Matrix.diagonal ![1 / 2, 3] * !![2, 0; 1, -1]) *ᵥ ![3, 5]
        = ![0, 6] := by
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.diagonal]

/-- W1 second solution: weights `![1, 1]`, displacement
`![3/2, 15/2]`, same load. -/
private lemma w1SolutionTwo :
    ((!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ
      * Matrix.diagonal ![1, 1] * !![2, 0; 1, -1]) *ᵥ ![3 / 2, 15 / 2]
        = ![0, 6] := by
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.diagonal]

/-- Both W1 elastic force vectors are `![3, -6]`, while
the displacements differ. -/
example : Matrix.diagonal ![1 / 2, 3]
      *ᵥ ((!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 5])
        = ![3, -6]
    ∧ Matrix.diagonal ![1, 1]
      *ᵥ ((!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3 / 2, 15 / 2])
        = ![3, -6]
    ∧ (![3, 5] : Fin 2 → ℝ) ≠ ![3 / 2, 15 / 2] := by
  refine ⟨?_, ?_, by norm_num⟩ <;>
    · funext i
      fin_cases i <;>
        norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Matrix.mulVec_diagonal]

/-- W1 through the statics identification: the elastic
force is `(Bsᵀ)⁻¹ *ᵥ f`. -/
example : Matrix.diagonal ![1 / 2, 3]
      *ᵥ ((!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 5])
    = ((!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)⁻¹ *ᵥ ![0, 6] :=
  reduced_memberForce_eq_inv_mulVec _ detBsW1 _ w1SolutionOne

/-- W1 force independence of the axial weights. -/
example : Matrix.diagonal ![1 / 2, 3]
      *ᵥ ((!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 5])
    = Matrix.diagonal ![1, 1]
      *ᵥ ((!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3 / 2, 15 / 2]) :=
  reduced_memberForce_indep_of_diagonal _ detBsW1 _ _
    w1SolutionOne w1SolutionTwo

/-- W1 unique supported solution. -/
example : ∃! u : Fin 2 → ℝ,
    ((!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ
      * Matrix.diagonal ![1 / 2, 3] * !![2, 0; 1, -1]) *ᵥ u = ![0, 6] :=
  reduced_stiffness_existsUnique _ detBsW1 _
    (by intro e; fin_cases e <;> norm_num) _

/-- Transpose guard at W1: equilibrium uses `Bsᵀ`, not
`Bs` (`Bs *ᵥ N = ![6, 9] ≠ f`). -/
example : (!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, -6]
      = ![6, 9]
    ∧ (!![2, 0; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ ![3, -6]
      = ![0, 6] := by
  constructor <;>
    · funext i
      fin_cases i <;>
        norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Matrix.transpose_apply]

/-- The focused supported compatibility matrix is the
W1 matrix `!![2, 0; 1, -1]`. -/
private lemma supportedBsF :
    axialCompatibility rF ![0, 1] ![1, 2] * SF = !![2, 0; 1, -1] := by
  ext e f
  fin_cases e <;> fin_cases f <;>
    simp [Matrix.mul_apply, axialCompatibility, SF, Matrix.of_apply] <;>
    norm_num

/-- W1 as a truss: the separation-form elastic
coefficient vector is the reduced statics solution. -/
example : Matrix.diagonal ![1 / 2, 3]
      *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![3, 5])
    = ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ)⁻¹ *ᵥ ![0, 6] := by
  have hdet : IsUnit (axialCompatibility rF ![0, 1] ![1, 2] * SF).det := by
    rw [supportedBsF]
    exact detBsW1
  have hu : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![3, 5]
      = ![0, 6] := by
    rw [supportedStiffnessF]
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (truss_reduced_memberCoefficient_eq_inv_mulVec rF ![0, 1] ![1, 2] SF
    hdet _ hu).1

/-- W1 as a truss: virtual-work equilibrium at the two
basis supported displacements. -/
example : (Matrix.diagonal ![1 / 2, 3]
        *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![3, 5]))
      ⬝ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![1, 0])
        = (![0, 6] : Fin 2 → ℝ) ⬝ᵥ ![1, 0]
    ∧ (Matrix.diagonal ![1 / 2, 3]
        *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![3, 5]))
      ⬝ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![0, 1])
        = (![0, 6] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] := by
  have hdet : IsUnit (axialCompatibility rF ![0, 1] ![1, 2] * SF).det := by
    rw [supportedBsF]
    exact detBsW1
  have hu : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![3, 5]
      = ![0, 6] := by
    rw [supportedStiffnessF]
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h := (truss_reduced_memberCoefficient_eq_inv_mulVec rF ![0, 1] ![1, 2] SF
    hdet _ hu).2
  exact ⟨h _, h _⟩

/-- W1 physical axial forces: member lengths `2` and
`√2` rescale the coefficient vector `![3, -6]` to
`![6, -6 √2]`. -/
example : (fun e => (Matrix.diagonal ![1 / 2, 3]
        *ᵥ ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ ![3, 5])) e
      * memberLength rF ![0, 1] ![1, 2] e)
    = ![6, -6 * Real.sqrt 2] := by
  funext e
  fin_cases e
  · simp [memberLength, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      supportedBsF]
    norm_num
  · simp [memberLength, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      supportedBsF]
    norm_num

/-- Singular control: `Bs = !![1, 1; 1, 1]` is not
invertible, and two positive weight choices give two
distinct equilibrating elastic forces for `f = ![1, 1]`
(determinacy does real work). -/
example : ¬ IsUnit (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_fin_two]
  norm_num

example : ((!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ
        * Matrix.diagonal ![1, 1] * !![1, 1; 1, 1]) *ᵥ ![1 / 4, 1 / 4]
      = ![1, 1]
    ∧ Matrix.diagonal ![1, 1]
        *ᵥ ((!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1 / 4, 1 / 4])
      = ![1 / 2, 1 / 2]
    ∧ ((!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ
        * Matrix.diagonal ![1, 3] * !![1, 1; 1, 1]) *ᵥ ![1 / 8, 1 / 8]
      = ![1, 1]
    ∧ Matrix.diagonal ![1, 3]
        *ᵥ ((!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1 / 8, 1 / 8])
      = ![1 / 4, 3 / 4]
    ∧ (![1 / 2, 1 / 2] : Fin 2 → ℝ) ≠ ![1 / 4, 3 / 4] := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩ <;>
    · funext i
      fin_cases i <;>
        norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Matrix.mulVec_mulVec, Matrix.mulVec_diagonal,
          Matrix.transpose_apply, Matrix.mul_apply, Matrix.diagonal]

/-- Zero-weight control: with `Bs = 1` and weights
`![1, 0]`, the load `![0, 1]` has no supported solution,
so the nonvanishing hypothesis of the existence result
is essential. -/
example : ¬ ∃ u : Fin 2 → ℝ,
    (((1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ * Matrix.diagonal ![1, 0]
      * (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ u = ![0, 1] := by
  rintro ⟨u, hu⟩
  have h1 := congrFun hu 1
  simp [Matrix.mulVec, dotProduct] at h1

/-- Rectangular (indeterminate) shadow, outside the
square statements: two members, one free coordinate; the
elastic force split depends on the weights
(`(1/2, 1/2)` vs `(1/4, 3/4)`). -/
example : Matrix.diagonal ![1, 1]
      *ᵥ ((!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ ![1 / 2])
        = ![1 / 2, 1 / 2]
    ∧ Matrix.diagonal ![1, 3]
      *ᵥ ((!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ ![1 / 4])
        = ![1 / 4, 3 / 4] := by
  constructor <;>
    · funext i
      fin_cases i <;>
        norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Matrix.mulVec_diagonal]

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
#print axioms Mechanics.TrussCompatibility.supported_stiffness_isSymm
#print axioms
  Mechanics.TrussCompatibility.supported_dotProduct_mulVec_comm
#print axioms Mechanics.TrussCompatibility.supported_reciprocalWork
#print axioms
  Mechanics.TrussCompatibility.loadObservation_eq_of_supported_eq
#print axioms
  Mechanics.TrussCompatibility.loadObservation_supported_response
#print axioms
  Mechanics.TrussCompatibility.loadObservation_identifiableOnAffine_of_kernels
#print axioms Mechanics.TrussCompatibility.inv_not_affine_on_pos

#print axioms
  Mechanics.TrussCompatibility.supported_invDiagonal_mulVec_memberCoefficient
#print axioms
  Mechanics.TrussCompatibility.supported_influenceVector_mulVec
#print axioms Mechanics.TrussCompatibility.supported_influenceVector_smul
#print axioms Mechanics.TrussCompatibility.supported_unitLoadResponse_eq
#print axioms
  Mechanics.TrussCompatibility.supported_unitLoad_identity_separationForm
#print axioms Mechanics.TrussCompatibility.supported_unitLoad_identity
#print axioms
  Mechanics.TrussCompatibility.supported_unitLoad_axialForce_identity
#print axioms
  Mechanics.TrussCompatibility.supported_unitLoad_identity_of_kernel

#print axioms
  Mechanics.TrussCompatibility.supported_unitLoadResponse_sum_smul
#print axioms
  Mechanics.TrussCompatibility.supported_inf'_le_unitLoadResponse_sum_smul
#print axioms
  Mechanics.TrussCompatibility.supported_unitLoadResponse_sum_smul_le_sup'
#print axioms
  Mechanics.TrussCompatibility.supported_unitLoadResponse_convexCombination_bounds
#print axioms
  Mechanics.TrussCompatibility.supported_unitLoadResponse_singleton
#print axioms
  Mechanics.TrussCompatibility.supported_unitLoadResponse_convexCombination_output_bounds

#print axioms
  Mechanics.TrussCompatibility.supported_abs_unitLoadResponse_sum_smul_le_sup'_abs
#print axioms
  Mechanics.TrussCompatibility.supported_abs_convexCombination_output_le_sup'_abs

#print axioms Mechanics.TrussCompatibility.reduced_equilibrium_of_elastic
#print axioms Mechanics.TrussCompatibility.reduced_equilibrium_iff_eq_inv
#print axioms Mechanics.TrussCompatibility.reduced_memberForce_eq_inv_mulVec
#print axioms
  Mechanics.TrussCompatibility.reduced_memberForce_indep_of_diagonal
#print axioms Mechanics.TrussCompatibility.reduced_stiffness_existsUnique
#print axioms
  Mechanics.TrussCompatibility.reduced_stiffness_existsUnique_of_pos
#print axioms
  Mechanics.TrussCompatibility.truss_reduced_memberCoefficient_eq_inv_mulVec
#print axioms Mechanics.TrussCompatibility.truss_reduced_axialForce_eq

end PhyslibExtTest.Mechanics.TrussCompatibility
