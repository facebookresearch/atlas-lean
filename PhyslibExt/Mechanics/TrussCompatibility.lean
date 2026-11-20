/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.HarmonicMechanics
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Axial compatibility on the finite member table

## i. Overview

Geometric compatibility for the axial-member table of
`PhyslibExt.Mechanics.HarmonicMechanics` (joints `J` at
positions `r`, members `M` with endpoints `a e`, `b e`). The
compatibility matrix `B : Matrix M (J × Fin 2) ℝ` has
separation-vector rows: `(B *ᵥ u) e` pairs the initial
separation vector with the relative joint displacement, i.e.
`L e` times the linearized (small-displacement) elongation,
not the exact change in member length (a transverse relative
displacement changes length at second order and reads zero
here). The unit-direction variant scales rows by the inverse
member length, so its rows give linearized elongations and
pair with member stiffness `EA / L` in the linearized energy;
the separation form pairs with `EA / L ^ 3`. The transpose collects endpoint forces at
each joint coordinate with a minus sign, so joint equilibrium
reads `Bᵀ *ᵥ c = f_ext`, the `PlasticWork` orientation.
Supported coordinates come from a supplied injection
`S : Matrix (J × Fin 2) F ℝ`; the supported stiffness
quadratic form (twice the linearized stored energy, in the
convention of `BeamStiffness`) is the member sum and is
positive semidefinite for nonnegative stiffnesses. Zero-length members contribute zero rows in the
unit form (totalized inverse); a physical energy reading
needs distinct endpoints. The rigidity certificate
(section E) characterizes positive definiteness, for
positive member weights, by the absence of supported
mechanisms.

## ii. Key results

- `Mechanics.TrussCompatibility.axialCompatibility` and
  `axialCompatibilityUnit`: the two row forms.
- `axialCompatibility_mulVec_apply`: row action.
- `axialCompatibility_transpose_mulVec_apply` and
  `axialCompatibilityUnit_transpose_mulVec_apply`: force
  collection at joints.
- `supported_quad_form_eq_sum`, `supported_pairing`,
  `supported_posSemidef`: supported energy form.
- `supported_virtualWork_iff`: supported equilibrium iff
  internal and external virtual work agree on every
  supported virtual displacement.
- `supported_posDef_iff`: for positive member weights the
  supported stiffness is positive definite iff the supported
  compatibility map has trivial kernel (no supported
  mechanism).

## iii. Table of contents

- A. Compatibility matrices and row action
- B. Transpose force collection
- C. Supported quadratic form
- D. Supported virtual work
- E. Supported rigidity certificate

## iv. References

- `PhyslibExt.Mechanics.HarmonicMechanics` for the member
  table, endpoint forces, and member lengths.
- `MathlibExt.LinearAlgebra.Matrix.PlasticWork` for the
  members-by-coordinates orientation convention.
-/

@[expose] public section

open Matrix
open PhyslibExt.Mechanics.HarmonicMechanics

namespace Mechanics.TrussCompatibility

/-! ## A. Compatibility matrices and row action -/

/-- The joint owning an endpoint. -/
def endpointJoint {J M : Type*} (a b : M → J) (p : M × Bool) :
    J :=
  if p.2 then b p.1 else a p.1

/-- Separation-vector compatibility matrix: rows are members,
columns are joint coordinates. -/
noncomputable def axialCompatibility {J M : Type*}
    [DecidableEq J] (r : J → (Fin 2 → ℝ)) (a b : M → J) :
    Matrix M (J × Fin 2) ℝ :=
  Matrix.of fun e q =>
    ((if b e = q.1 then (1 : ℝ) else 0)
      - (if a e = q.1 then 1 else 0))
      * (r (b e) - r (a e)) q.2

/-- Unit-direction compatibility matrix: rows scaled by the
inverse member length (zero-length members contribute zero). -/
noncomputable def axialCompatibilityUnit {J M : Type*}
    [DecidableEq J] (r : J → (Fin 2 → ℝ)) (a b : M → J) :
    Matrix M (J × Fin 2) ℝ :=
  Matrix.of fun e q =>
    (memberLength r a b e)⁻¹ * axialCompatibility r a b e q

/-- A row of `B *ᵥ u` is the separation vector paired with
the relative joint displacement. -/
theorem axialCompatibility_mulVec_apply {J M : Type*}
    [Fintype J] [DecidableEq J] (r : J → (Fin 2 → ℝ))
    (a b : M → J) (u : J × Fin 2 → ℝ) (e : M) :
    (axialCompatibility r a b *ᵥ u) e
      = ∑ k, (r (b e) - r (a e)) k
          * (u (b e, k) - u (a e, k)) := by
  rw [Matrix.mulVec_apply]
  simp only [Matrix.row, dotProduct, axialCompatibility, Matrix.of_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Fintype.sum_ite_eq]
  ring

/-! ## B. Transpose force collection -/

/-- The transpose collects endpoint forces at each joint
coordinate, with a minus sign. -/
theorem axialCompatibility_transpose_mulVec_apply
    {J M : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    (r : J → (Fin 2 → ℝ)) (a b : M → J) (c : M → ℝ) (j : J)
    (k : Fin 2) :
    ((axialCompatibility r a b)ᵀ *ᵥ c) (j, k)
      = -(∑ p : M × Bool,
          if endpointJoint a b p = j
          then memberEndpointForce r a b c p k else 0) := by
  rw [Matrix.mulVec_apply]
  simp only [Matrix.row, dotProduct, Matrix.transpose_apply, axialCompatibility,
    Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool, endpointJoint,
    memberEndpointForce]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases ha : a e = j <;> by_cases hb : b e = j <;> simp [ha, hb] <;> ring

/-- Unit-direction transpose collects axial endpoint forces.
`haxial` is the canonical
`axialEndpointForce_eq_memberEndpointForce` statement. -/
private theorem axialCompatibilityUnit_transpose_mulVec_apply_of
    {J M : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    (haxial : ∀ (r : J → (Fin 2 → ℝ)) (a b : M → J)
        (N : M → ℝ),
      axialEndpointForce r a b N
        = memberEndpointForce r a b
            (fun e => N e / memberLength r a b e))
    (r : J → (Fin 2 → ℝ)) (a b : M → J) (N : M → ℝ) (j : J)
    (k : Fin 2) :
    ((axialCompatibilityUnit r a b)ᵀ *ᵥ N) (j, k)
      = -(∑ p : M × Bool,
          if endpointJoint a b p = j
          then axialEndpointForce r a b N p k else 0) := by
  have h2 := axialCompatibility_transpose_mulVec_apply r a b
    (fun e => N e / memberLength r a b e) j k
  rw [← haxial r a b N] at h2
  rw [← h2]
  simp only [Matrix.mulVec_apply, Matrix.row, dotProduct,
    Matrix.transpose_apply, axialCompatibilityUnit, axialCompatibility,
    Matrix.of_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-! ## C. Supported quadratic form -/

/-- Supported stiffness quadratic form (twice the linearized
stored energy) is the member sum
`∑ e, k e * ((B S *ᵥ u) e)^2`. -/
theorem supported_quad_form_eq_sum {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (u : F → ℝ) :
    u ⬝ᵥ (((axialCompatibility r a b * S)ᵀ
          * Matrix.diagonal k
          * (axialCompatibility r a b * S)) *ᵥ u)
      = ∑ e, k e
          * (((axialCompatibility r a b * S) *ᵥ u) e) ^ 2 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- Free-coordinate pairing: supported equilibrium block is
the transpose of supported compatibility. -/
theorem supported_pairing {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (u : F → ℝ) (N : M → ℝ) :
    ((axialCompatibility r a b * S) *ᵥ u) ⬝ᵥ N
      = u ⬝ᵥ ((axialCompatibility r a b * S)ᵀ *ᵥ N) := by
  rw [dotProduct_comm]
  exact (Matrix.dotProduct_transpose_mulVec (axialCompatibility r a b * S) u N).symm

/-- The supported stiffness form is positive semidefinite for
nonnegative member stiffnesses. -/
theorem supported_posSemidef {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (hk : 0 ≤ k) :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)).PosSemidef := by
  have hD : (Matrix.diagonal k).PosSemidef := Matrix.PosSemidef.diagonal hk
  have htr : (axialCompatibility r a b * S)ᴴ
      = (axialCompatibility r a b * S)ᵀ :=
    Matrix.conjTranspose_eq_transpose_of_trivial _
  rw [← htr]
  exact hD.conjTranspose_mul_mul_same _

/-- Unit-direction transpose collects axial endpoint forces
at each joint coordinate. -/
theorem axialCompatibilityUnit_transpose_mulVec_apply
    {J M : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    (r : J → (Fin 2 → ℝ)) (a b : M → J) (N : M → ℝ) (j : J)
    (k : Fin 2) :
    ((axialCompatibilityUnit r a b)ᵀ *ᵥ N) (j, k)
      = -(∑ p : M × Bool,
          if endpointJoint a b p = j
          then axialEndpointForce r a b N p k else 0) :=
  axialCompatibilityUnit_transpose_mulVec_apply_of
    (fun r a b N => axialEndpointForce_eq_memberEndpointForce
      r a b N) r a b N j k

/-! ## D. Supported virtual work -/

/-- Conditional form of the supported virtual-work
characterization, given the canonical supported pairing. -/
private theorem supported_virtualWork_iff_of {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [Fintype F]
    (hpair : ∀ (r : J → (Fin 2 → ℝ)) (a b : M → J)
        (S : Matrix (J × Fin 2) F ℝ) (u : F → ℝ) (N : M → ℝ),
      ((axialCompatibility r a b * S) *ᵥ u) ⬝ᵥ N
        = u ⬝ᵥ ((axialCompatibility r a b * S)ᵀ *ᵥ N))
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (s : M → ℝ) (f : F → ℝ) :
    (axialCompatibility r a b * S)ᵀ *ᵥ s = f ↔
      ∀ v : F → ℝ, s ⬝ᵥ ((axialCompatibility r a b * S) *ᵥ v) = f ⬝ᵥ v := by
  constructor
  · intro h v
    calc s ⬝ᵥ ((axialCompatibility r a b * S) *ᵥ v)
        = ((axialCompatibility r a b * S) *ᵥ v) ⬝ᵥ s := dotProduct_comm _ _
      _ = v ⬝ᵥ ((axialCompatibility r a b * S)ᵀ *ᵥ s) := hpair r a b S v s
      _ = v ⬝ᵥ f := by rw [h]
      _ = f ⬝ᵥ v := dotProduct_comm _ _
  · intro h
    apply dotProduct_eq_iff.mp
    intro v
    calc ((axialCompatibility r a b * S)ᵀ *ᵥ s) ⬝ᵥ v
        = v ⬝ᵥ ((axialCompatibility r a b * S)ᵀ *ᵥ s) := dotProduct_comm _ _
      _ = ((axialCompatibility r a b * S) *ᵥ v) ⬝ᵥ s := (hpair r a b S v s).symm
      _ = s ⬝ᵥ ((axialCompatibility r a b * S) *ᵥ v) := dotProduct_comm _ _
      _ = f ⬝ᵥ v := h v

/-- Supported virtual work: member coefficients `s` balance
the supported load `f` (`(B S)ᵀ *ᵥ s = f`) iff internal
virtual work `s ⬝ᵥ ((B S) *ᵥ v)` equals external virtual
work `f ⬝ᵥ v` for every supported virtual displacement
`v`. The coefficients `s` are separation-form; for a
member with noncoincident endpoints (positive member
length) they are axial force divided by member length,
tension positive, with unit-direction member force
`N e = s e * L e` (for a zero-length member there is no
axial direction and the quotient reading does not apply;
the algebraic equivalence is unaffected). Test
displacements range over the free coordinates only, so
support reactions are excluded. No injectivity, stiffness,
or positivity hypothesis is used. -/
theorem supported_virtualWork_iff {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (s : M → ℝ) (f : F → ℝ) :
    (axialCompatibility r a b * S)ᵀ *ᵥ s = f ↔
      ∀ v : F → ℝ, s ⬝ᵥ ((axialCompatibility r a b * S) *ᵥ v) = f ⬝ᵥ v :=
  supported_virtualWork_iff_of
    (fun r a b S u N => supported_pairing r a b S u N) r a b S s f

/-! ## E. Supported rigidity certificate -/

/-- Conditional form of the rigidity certificate, given the
supported quadratic-form identity. -/
private theorem supported_posDef_iff_of {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (hquad : ∀ (r : J → (Fin 2 → ℝ)) (a b : M → J)
        (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (u : F → ℝ),
      u ⬝ᵥ (((axialCompatibility r a b * S)ᵀ
            * Matrix.diagonal k
            * (axialCompatibility r a b * S)) *ᵥ u)
        = ∑ e, k e
            * (((axialCompatibility r a b * S) *ᵥ u) e) ^ 2)
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (hk : ∀ e, 0 < k e) :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef ↔
      ∀ u : F → ℝ, (axialCompatibility r a b * S) *ᵥ u = 0 → u = 0 := by
  constructor
  · intro hPD u hu
    by_contra hne
    have hpos := Matrix.PosDef.dotProduct_mulVec_pos hPD hne
    have hKu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).mulVec u = 0 := by
      simp only [← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
    rw [hKu, dotProduct_zero] at hpos
    exact lt_irrefl 0 hpos
  · intro hker
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · have hD : (Matrix.diagonal k).conjTranspose = Matrix.diagonal k :=
        Matrix.isHermitian_diagonal k
      have key : ∀ B : Matrix M F ℝ,
          (Bᵀ * Matrix.diagonal k * B).IsHermitian := by
        intro B
        show (B.transpose * Matrix.diagonal k * B).conjTranspose
          = B.transpose * Matrix.diagonal k * B
        have hB : B.conjTranspose = B.transpose :=
          Matrix.conjTranspose_eq_transpose_of_trivial B
        have hBT : B.transpose.conjTranspose = B := by
          rw [Matrix.conjTranspose_eq_transpose_of_trivial,
            Matrix.transpose_transpose]
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hB, hD, hBT,
          ← Matrix.mul_assoc]
      exact key (axialCompatibility r a b * S)
    · intro x hx
      have hstar : star x = x := by simp
      rw [hstar, hquad r a b S k x]
      have hne : (axialCompatibility r a b * S) *ᵥ x ≠ 0 :=
        fun h => hx (hker x h)
      obtain ⟨e0, he0⟩ := Function.ne_iff.mp hne
      simp only [Pi.zero_apply] at he0
      refine Finset.sum_pos' (fun e _ => ?_) ⟨e0, Finset.mem_univ e0, ?_⟩
      · exact mul_nonneg (le_of_lt (hk e)) (sq_nonneg _)
      · exact mul_pos (hk e0) (pow_two_pos_of_ne_zero he0)

/-- Conditional form of the kernel-side certificate, given
the supported quadratic-form identity. -/
private theorem supported_posDef_iff_ker_eq_bot_of {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (hquad : ∀ (r : J → (Fin 2 → ℝ)) (a b : M → J)
        (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (u : F → ℝ),
      u ⬝ᵥ (((axialCompatibility r a b * S)ᵀ
            * Matrix.diagonal k
            * (axialCompatibility r a b * S)) *ᵥ u)
        = ∑ e, k e
            * (((axialCompatibility r a b * S) *ᵥ u) e) ^ 2)
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (hk : ∀ e, 0 < k e) :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef ↔
      LinearMap.ker (axialCompatibility r a b * S).mulVecLin = ⊥ := by
  rw [supported_posDef_iff_of hquad r a b S k hk, Submodule.eq_bot_iff]
  constructor
  · intro h x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
    exact h x hx
  · intro hker u hu
    apply hker
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hu

/-- Conditional form of the physical certificate, given the
supported quadratic-form identity and positive member
lengths at noncoincident endpoints. -/
private theorem supported_posDef_iff_of_axial_of {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (hquad : ∀ (r : J → (Fin 2 → ℝ)) (a b : M → J)
        (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (u : F → ℝ),
      u ⬝ᵥ (((axialCompatibility r a b * S)ᵀ
            * Matrix.diagonal k
            * (axialCompatibility r a b * S)) *ᵥ u)
        = ∑ e, k e
            * (((axialCompatibility r a b * S) *ᵥ u) e) ^ 2)
    (hlen : ∀ (r : J → (Fin 2 → ℝ)) (a b : M → J) {e : M},
      r (a e) ≠ r (b e) → 0 < memberLength r a b e)
    (r : J → (Fin 2 → ℝ)) (a b : M → J) (S : Matrix (J × Fin 2) F ℝ)
    {E A : M → ℝ} (hE : ∀ e, 0 < E e) (hA : ∀ e, 0 < A e)
    (hne : ∀ e, r (a e) ≠ r (b e)) :
    ((axialCompatibility r a b * S)ᵀ
        * Matrix.diagonal (fun e => E e * A e / memberLength r a b e ^ 3)
        * (axialCompatibility r a b * S)).PosDef ↔
      ∀ u : F → ℝ, (axialCompatibility r a b * S) *ᵥ u = 0 → u = 0 := by
  have hk : ∀ e, 0 < E e * A e / memberLength r a b e ^ 3 := fun e =>
    div_pos (mul_pos (hE e) (hA e)) (pow_pos (hlen r a b (hne e)) 3)
  exact supported_posDef_iff_of hquad r a b S _ hk

/-- Support-restriction rigidity certificate: for positive
member stiffnesses `k`, the supported stiffness
`(B S)ᵀ diag(k) (B S)` is positive definite iff the
supported compatibility map `B S` has trivial kernel (no
supported mechanism). Connectivity of the member graph is
not assumed and does not suffice. -/
theorem supported_posDef_iff {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (hk : ∀ e, 0 < k e) :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef ↔
      ∀ u : F → ℝ, (axialCompatibility r a b * S) *ᵥ u = 0 → u = 0 :=
  supported_posDef_iff_of supported_quad_form_eq_sum r a b S k hk

/-- The same certificate with the kernel written as
`ker (B S) = ⊥`. -/
theorem supported_posDef_iff_ker_eq_bot {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (hk : ∀ e, 0 < k e) :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef ↔
      LinearMap.ker (axialCompatibility r a b * S).mulVecLin = ⊥ :=
  supported_posDef_iff_ker_eq_bot_of supported_quad_form_eq_sum
    r a b S k hk

/-- Physical instance: separation rows pair with
`E A / L ^ 3`; positive `E`, `A` and noncoincident endpoint
positions (`r (a e) ≠ r (b e)`, the model admission
`L > 0`) make these weights positive. -/
theorem supported_posDef_iff_of_axial {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J) (S : Matrix (J × Fin 2) F ℝ)
    {E A : M → ℝ} (hE : ∀ e, 0 < E e) (hA : ∀ e, 0 < A e)
    (hne : ∀ e, r (a e) ≠ r (b e)) :
    ((axialCompatibility r a b * S)ᵀ
        * Matrix.diagonal (fun e => E e * A e / memberLength r a b e ^ 3)
        * (axialCompatibility r a b * S)).PosDef ↔
      ∀ u : F → ℝ, (axialCompatibility r a b * S) *ᵥ u = 0 → u = 0 :=
  supported_posDef_iff_of_axial_of supported_quad_form_eq_sum
    memberLength_pos_of_ne r a b S hE hA hne

end Mechanics.TrussCompatibility
