/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.HarmonicMechanics
public import PhyslibExt.Statistics.UncertaintyPropagation
public import Mathlib.Data.Finset.Max
import MathlibExt.LinearAlgebra.Matrix.WeightedScatter
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import MathlibExt.LinearAlgebra.Matrix.FullRankLinearSystem

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
positive member weights, by the absence of
generalized-coordinate null modes of the supported
compatibility map.
Section F turns positive definiteness into the unique
supported response to a load, with the explicit inverse
form and the unique residual reaction vector for a full
joint load.
Section G records reciprocal work: one symmetric supported
stiffness gives equal cross work for any two supported load
cases.
Section H builds the load-parameter observation matrix at
fixed supported stiffness and records when load parameters
on a declared affine space are identifiable from it.
Section I builds the unit-load (dummy-unit-load) response
functional for a fixed output and proves it from reciprocal
work with a single inverse application.
Section J bounds every convex combination over a finite
load table by the minimum and maximum vertex responses of
the same fixed-output response, and the absolute response
by the maximum absolute vertex response.
Section K treats the determinate case, where the supported
compatibility matrix is square and invertible: elastic
member forces then agree with reduced statics and do not
depend on the axial weights ("reduced" here is the supported
system in free coordinates).

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
  compatibility map has trivial kernel (no
  generalized-coordinate null mode).
- `supported_existsUnique` and
  `supported_residual_existsUnique_of_posDef`: the unique
  supported displacement and residual reaction vector.
- `supported_reciprocalWork`: for one supported
  stiffness, the work of either supported load through the
  other solution is the same.
- `loadObservationMatrix` and
  `loadObservation_identifiableOnAffine_of_kernels`: at
  fixed positive-definite supported stiffness, load
  parameters on an affine space are identifiable when the
  sensor map and the load basis have trivial kernels there.
- `influenceVector`, `unitLoadResponse`, and
  `supported_unitLoad_identity`: the fixed output of a
  supported solution is the pairing of the unit-load
  separation-form coefficients with the compliance-applied
  coefficients; `supported_unitLoad_axialForce_identity`
  is the physical axial-force form.
- `supported_unitLoadResponse_convexCombination_bounds`:
  every convex combination over a nonempty finite load
  table has fixed-output response between the minimum and
  maximum vertex responses.
- `supported_abs_convexCombination_output_le_sup'_abs`:
  the absolute fixed output of a combined solution is at
  most the maximum absolute vertex output.
- `reduced_memberForce_eq_inv_mulVec` and
  `reduced_memberForce_indep_of_diagonal`: for square
  invertible reduced compatibility, the diagonal-law force
  vector is the reduced statics solution, independent of
  the axial weights.
- `truss_reduced_memberCoefficient_eq_inv_mulVec` and
  `truss_reduced_axialForce_eq`: the truss instance. Its
  force vector is separation-form (axial force divided by
  member length); the second result converts it to
  physical axial forces `N e = s e * L e`.

## iii. Table of contents

- A. Compatibility matrices and row action
- B. Transpose force collection
- C. Supported quadratic form
- D. Supported virtual work
- E. Supported rigidity certificate
- F. Supported unique response
- G. Reciprocal work
- H. Load-parameter identifiability
- I. Unit-load response
- J. Finite load hull
- K. Reduced determinate statics

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
stored energy, for positive weights) is the member sum
`∑ e, k e * ((B S *ᵥ u) e)^2`, for all real weights `k`. -/
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

/-- Unit-direction transpose collects axial endpoint forces at each joint coordinate. A zero-length
member exerts no force (`0⁻¹ = 0`). -/
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

/-- Support-restriction rigidity certificate: for positive
member stiffnesses `k`, the supported stiffness
`(B S)ᵀ diag(k) (B S)` is positive definite iff the
supported compatibility map `B S` has trivial kernel (no
generalized-coordinate null mode). For arbitrary `S` a
kernel vector `u` need not give a nonzero joint
displacement `S *ᵥ u`; the physical supported-mechanism
reading needs `S.mulVec` injective, as for a coordinate
selection. Connectivity of the member graph is not
assumed and does not suffice. This is the weighted-Gram
characterization
`MetaMathlibExt.posDef_mul_diagonal_mul_transpose_iff`
at the supported compatibility map. -/
theorem supported_posDef_iff {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (hk : ∀ e, 0 < k e) :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef ↔
      ∀ u : F → ℝ, (axialCompatibility r a b * S) *ᵥ u = 0 → u = 0 := by
  have hgen := MetaMathlibExt.posDef_mul_diagonal_mul_transpose_iff
    (B := (axialCompatibility r a b * S)ᵀ) (w := k) (fun e => (hk e).le)
  rw [Matrix.transpose_transpose] at hgen
  rw [hgen]
  constructor
  · intro h u hu
    by_contra hne
    obtain ⟨e, -, he⟩ := h u hne
    rw [Matrix.vecMul_transpose] at he
    have h0 : ((axialCompatibility r a b * S) *ᵥ u) e = 0 := by
      simp only [hu, Pi.zero_apply]
    exact he h0
  · intro h v hv
    have hne : (axialCompatibility r a b * S) *ᵥ v ≠ 0 :=
      fun h0 => hv (h v h0)
    obtain ⟨e, he⟩ := Function.ne_iff.mp hne
    simp only [Pi.zero_apply] at he
    exact ⟨e, hk e, by rwa [Matrix.vecMul_transpose]⟩

/-- The same certificate with the kernel written as
`ker (B S) = ⊥`. -/
theorem supported_posDef_iff_ker_eq_bot {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (hk : ∀ e, 0 < k e) :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef ↔
      LinearMap.ker (axialCompatibility r a b * S).mulVecLin = ⊥ := by
  rw [supported_posDef_iff r a b S k hk, Submodule.eq_bot_iff]
  constructor
  · intro h x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
    exact h x hx
  · intro hker u hu
    apply hker
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hu

/-- Physical instance: separation rows pair with
`E A / L ^ 3`; positive `E`, `A` and noncoincident endpoint
positions (`r (a e) ≠ r (b e)`, the model admission
`L > 0`) make these weights positive. The kernel side is
in generalized coordinates `u`; it reads as supported
joint mechanisms when `S.mulVec` is injective. -/
theorem supported_posDef_iff_of_axial {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J) (S : Matrix (J × Fin 2) F ℝ)
    {E A : M → ℝ} (hE : ∀ e, 0 < E e) (hA : ∀ e, 0 < A e)
    (hne : ∀ e, r (a e) ≠ r (b e)) :
    ((axialCompatibility r a b * S)ᵀ
        * Matrix.diagonal (fun e => E e * A e / memberLength r a b e ^ 3)
        * (axialCompatibility r a b * S)).PosDef ↔
      ∀ u : F → ℝ, (axialCompatibility r a b * S) *ᵥ u = 0 → u = 0 := by
  have hk : ∀ e, 0 < E e * A e / memberLength r a b e ^ 3 := fun e =>
    div_pos (mul_pos (hE e) (hA e))
      (pow_pos (memberLength_pos_of_ne r a b (hne e)) 3)
  exact supported_posDef_iff r a b S _ hk

/-! ## F. Supported unique response -/

/-- Reduced/full coordinate commute: the supported stiffness is the
full stiffness restricted by the support map, `Sᵀ * K * S`. No
positivity hypothesis is used. -/
theorem supported_stiffness_eq {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) :
    (axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)
      = Sᵀ * ((axialCompatibility r a b)ᵀ * Matrix.diagonal k
          * axialCompatibility r a b) * S := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Unique supported response: for positive-definite supported
stiffness, every supported load `f` has exactly one supported
displacement `u` in the supported coordinates `F`. -/
theorem supported_existsUnique_of_posDef {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef)
    (f : F → ℝ) :
    ∃! u : F → ℝ, ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f := by
  classical
  exact Matrix.exists_unique_mulVec_eq
    (Matrix.mulVec_injective_of_isUnit hPD.isUnit) f

/-- Explicit supported response: for positive-definite supported
stiffness, `u` solves the supported system exactly when it is the
inverse applied to the load, `u = K⁻¹ *ᵥ f`. -/
theorem supported_mulVec_eq_iff_inv_mulVec {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef)
    {f u : F → ℝ} :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f ↔
      u = ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S))⁻¹ *ᵥ f := by
  have hU : IsUnit (((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S))).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  exact Matrix.mulVec_eq_iff_inv_mulVec hU

/-- Certified unique supported response: for positive member
weights `k` and trivial supported kernel (no supported null mode),
every supported load has exactly one supported displacement,
through the supported rigidity certificate
`supported_posDef_iff`. -/
theorem supported_existsUnique {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (hk : ∀ e, 0 < k e)
    (hker : ∀ u : F → ℝ, (axialCompatibility r a b * S) *ᵥ u = 0 → u = 0)
    (f : F → ℝ) :
    ∃! u : F → ℝ, ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f := by
  have hPD : (((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S))).PosDef :=
    (supported_posDef_iff r a b S k hk).mpr hker
  exact supported_existsUnique_of_posDef r a b S k hPD f

/-- Unique residual reaction vector: for positive-definite
supported stiffness and a full joint load `g`, there is exactly one
pair of a supported displacement `p.1` and a full joint-coordinate
residual `p.2` with full balance `K *ᵥ (S *ᵥ p.1) = g + p.2` and
vanishing supported projection `Sᵀ *ᵥ p.2 = 0`. The residual is the
vector `K *ᵥ (S *ᵥ p.1) - g`; no expansion in a reaction basis and
no uniqueness of such coefficients is stated. -/
theorem supported_residual_existsUnique_of_posDef {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef)
    (g : J × Fin 2 → ℝ) :
    ∃! p : (F → ℝ) × (J × Fin 2 → ℝ),
      ((axialCompatibility r a b)ᵀ * Matrix.diagonal k
          * axialCompatibility r a b) *ᵥ (S *ᵥ p.1) = g + p.2
        ∧ Sᵀ *ᵥ p.2 = 0 := by
  have hKs : (axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)
      = Sᵀ * ((axialCompatibility r a b)ᵀ * Matrix.diagonal k
          * axialCompatibility r a b) * S :=
    supported_stiffness_eq r a b S k
  have hcomm : ∀ u : F → ℝ,
      ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
          * (axialCompatibility r a b * S)) *ᵥ u
        = Sᵀ *ᵥ (((axialCompatibility r a b)ᵀ * Matrix.diagonal k
            * axialCompatibility r a b) *ᵥ (S *ᵥ u)) := by
    intro u
    rw [hKs, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  obtain ⟨u, hu, huniq⟩ :=
    supported_existsUnique_of_posDef r a b S k hPD (Sᵀ *ᵥ g)
  refine ⟨(u, ((axialCompatibility r a b)ᵀ * Matrix.diagonal k
      * axialCompatibility r a b) *ᵥ (S *ᵥ u) - g), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · dsimp only
      exact (add_sub_cancel _ _).symm
    · dsimp only
      rw [Matrix.mulVec_sub, ← hcomm u, hu, sub_self]
  · rintro ⟨u', r'⟩ ⟨h1', h2'⟩
    dsimp only at h1' h2' ⊢
    have hSu : Sᵀ *ᵥ (((axialCompatibility r a b)ᵀ * Matrix.diagonal k
          * axialCompatibility r a b) *ᵥ (S *ᵥ u')) = Sᵀ *ᵥ g := by
      rw [h1', Matrix.mulVec_add, h2', add_zero]
    have hKsu' : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
          * (axialCompatibility r a b * S)) *ᵥ u' = Sᵀ *ᵥ g := by
      rw [hcomm u', hSu]
    have huv : u' = u := huniq _ hKsu'
    have hr : r' = ((axialCompatibility r a b)ᵀ * Matrix.diagonal k
          * axialCompatibility r a b) *ᵥ (S *ᵥ u') - g := by
      rw [h1']; abel
    subst huv
    rw [hr]

/-- Null modes are rejected: a nonzero supported displacement `z`
with no member stretch (`(B S) *ᵥ z = 0`) rules out a unique
supported response for every supported load, for arbitrary weights
`k`. In particular an unsupported rigid mode or a supported
mechanism admits no such unique response. -/
theorem supported_not_existsUnique_of_kernel {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    {z : F → ℝ} (hz : z ≠ 0)
    (hBz : (axialCompatibility r a b * S) *ᵥ z = 0) (f : F → ℝ) :
    ¬ ∃! u : F → ℝ, ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f := by
  rintro ⟨u, hu, huniq⟩
  have hKz : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)) *ᵥ z = 0 := by
    rw [← Matrix.mulVec_mulVec, hBz, Matrix.mulVec_zero]
  have h2 : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)) *ᵥ (u + z) = f := by
    rw [Matrix.mulVec_add, hu, hKz, add_zero]
  have hEq : u + z = u := huniq _ h2
  have hz0 : z = 0 := add_left_cancel_iff.mp (by rwa [add_zero])
  exact hz hz0

/-- Physical unique response: separation rows with weights
`E A / L ^ 3`, positive `E` and `A`, noncoincident endpoint
positions (`r (a e) ≠ r (b e)`, the model admission `L > 0`) and
trivial supported kernel give a unique supported displacement for
every supported load and a unique displacement/residual pair for
every full joint load, through the physical supported
rigidity certificate `supported_posDef_iff_of_axial`. -/
theorem supported_response_of_axial {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J) (S : Matrix (J × Fin 2) F ℝ)
    {E A : M → ℝ} (hE : ∀ e, 0 < E e) (hA : ∀ e, 0 < A e)
    (hne : ∀ e, r (a e) ≠ r (b e))
    (hker : ∀ u : F → ℝ, (axialCompatibility r a b * S) *ᵥ u = 0 → u = 0) :
    (∀ f : F → ℝ, ∃! u : F → ℝ,
      ((axialCompatibility r a b * S)ᵀ
        * Matrix.diagonal (fun e => E e * A e / memberLength r a b e ^ 3)
        * (axialCompatibility r a b * S)) *ᵥ u = f) ∧
    (∀ g : J × Fin 2 → ℝ, ∃! p : (F → ℝ) × (J × Fin 2 → ℝ),
      ((axialCompatibility r a b)ᵀ
          * Matrix.diagonal (fun e => E e * A e / memberLength r a b e ^ 3)
          * axialCompatibility r a b) *ᵥ (S *ᵥ p.1) = g + p.2
        ∧ Sᵀ *ᵥ p.2 = 0) := by
  have hPD : (((axialCompatibility r a b * S)ᵀ
      * Matrix.diagonal (fun e => E e * A e / memberLength r a b e ^ 3)
      * (axialCompatibility r a b * S))).PosDef :=
    (supported_posDef_iff_of_axial r a b S hE hA hne).mpr hker
  exact ⟨fun f => supported_existsUnique_of_posDef r a b S _ hPD f,
    fun g => supported_residual_existsUnique_of_posDef r a b S _ hPD g⟩

/-! ## G. Reciprocal work -/

/-- Symmetry of the supported stiffness: the supported stiffness is
the Gram matrix of the supported compatibility map against the
diagonal member law, so it is symmetric. Symmetry is structural and
needs no sign hypothesis on the weights; for nonnegative weights it
also follows from positive semidefiniteness of the supported
stiffness (nonnegative stored energy). -/
lemma supported_stiffness_isSymm {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)).IsSymm := by
  generalize (axialCompatibility r a b * S) = B
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Symmetry of the supported stiffness bilinear form: for a symmetric
supported stiffness, pairing one supported displacement against the
stiffness applied to another is unchanged when the two displacements
are exchanged. This is the existing symmetric-matrix bilinear identity
at the supported stiffness; no load or solve hypothesis is used. -/
lemma supported_dotProduct_mulVec_comm {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (u v : F → ℝ) :
    u ⬝ᵥ (((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ v)
      = v ⬝ᵥ (((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u) := by
  exact (supported_stiffness_isSymm r a b S k).dotProduct_mulVec_comm

/-- Reciprocal work for two supported loads: for one symmetric
supported stiffness (same reference geometry, supports and weights in
both load cases) and solutions `K *ᵥ u = f`, `K *ᵥ v = g`, the work of
`f` through `v` equals the work of `g` through `u`. The loads `f` and
`g` are independent. No reciprocity is claimed between solutions of two
different stiffnesses, or for follower loads or contact switching. -/
theorem supported_reciprocalWork {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    {u v f g : F → ℝ}
    (hu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f)
    (hv : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ v = g) :
    f ⬝ᵥ v = g ⬝ᵥ u := by
  have h := supported_dotProduct_mulVec_comm r a b S k u v
  rw [hv, hu] at h
  rw [dotProduct_comm f v, dotProduct_comm g u]
  exact h.symm

/-! ## H. Load-parameter identifiability -/

/-- Load-parameter observation matrix at fixed supported stiffness:
`Cmat * K⁻¹ * Bload`, where `K = (B S)ᵀ * Matrix.diagonal k * (B S)`
is the supported stiffness, with `B S = axialCompatibility r a b * S`.
The truss data and weights `k` are fixed knowns; only the load
parameters multiplied by `Bload` are unknown, so the
parameter-to-observation map is linear. At a non-invertible `K` the
totalized matrix inverse is `0`, so the observation matrix is `0`;
the physical reading needs positive definiteness, as in the theorems
below. -/
noncomputable def loadObservationMatrix {J M : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] {nf np nm : ℕ}
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) (Fin nf) ℝ) (k : M → ℝ)
    (Cmat : Matrix (Fin nm) (Fin nf) ℝ)
    (Bload : Matrix (Fin nf) (Fin np) ℝ) :
    Matrix (Fin nm) (Fin np) ℝ :=
  Cmat * ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S))⁻¹ * Bload
/-- Forward observation at fixed positive-definite supported
stiffness: a supported displacement `u` solving the supported system
at load `Bload *ᵥ θ` is observed as the linear observation matrix
applied to `θ`.
Uses the supported inverse characterization
`supported_mulVec_eq_iff_inv_mulVec`. -/
lemma loadObservation_eq_of_supported_eq {J M : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] {nf np nm : ℕ}
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) (Fin nf) ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef)
    (Cmat : Matrix (Fin nm) (Fin nf) ℝ)
    (Bload : Matrix (Fin nf) (Fin np) ℝ)
    {u : Fin nf → ℝ} {θ : Fin np → ℝ}
    (hu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = Bload *ᵥ θ) :
    Cmat *ᵥ u
      = loadObservationMatrix r a b S k Cmat Bload *ᵥ θ := by
  have hu' := (supported_mulVec_eq_iff_inv_mulVec r a b S k hPD).mp hu
  rw [hu']
  simp only [loadObservationMatrix, ← Matrix.mulVec_mulVec]

/-- Realized supported response: at positive-definite fixed
supported stiffness, `K⁻¹ *ᵥ (Bload *ᵥ θ)` solves the supported
system at load `Bload *ᵥ θ` and is observed as the linear observation
matrix applied to `θ`. Uses the supported inverse
characterization `supported_mulVec_eq_iff_inv_mulVec`. -/
lemma loadObservation_supported_response {J M : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] {nf np nm : ℕ}
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) (Fin nf) ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef)
    (Cmat : Matrix (Fin nm) (Fin nf) ℝ)
    (Bload : Matrix (Fin nf) (Fin np) ℝ)
    (θ : Fin np → ℝ) :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ
      (((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S))⁻¹ *ᵥ (Bload *ᵥ θ))
      = Bload *ᵥ θ
    ∧ Cmat *ᵥ (((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S))⁻¹ *ᵥ (Bload *ᵥ θ))
      = loadObservationMatrix r a b S k Cmat Bload *ᵥ θ := by
  have h1 : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ
      (((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S))⁻¹ *ᵥ (Bload *ᵥ θ))
      = Bload *ᵥ θ :=
    (supported_mulVec_eq_iff_inv_mulVec r a b S k hPD).mpr rfl
  exact ⟨h1,
    loadObservation_eq_of_supported_eq r a b S k hPD Cmat Bload h1⟩
/-- Known stiffness with unknown loads: at positive-definite fixed
supported stiffness, if the sensor map has trivial kernel and the
load basis has trivial kernel on the direction space `V`, then load
parameters on `theta0 + V` are identifiable from the observation.
The two kernel conditions are sufficient, not necessary: the exact
obstruction is a nonzero kernel direction of the composite
observation map inside `V`, and a sensor kernel that misses the
realized response subspace does not by itself obstruct
identifiability. -/
lemma loadObservation_identifiableOnAffine_of_kernels
    {J M : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [DecidableEq M] {nf np nm : ℕ}
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) (Fin nf) ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef)
    (Cmat : Matrix (Fin nm) (Fin nf) ℝ)
    (Bload : Matrix (Fin nf) (Fin np) ℝ) (theta0 : Fin np → ℝ)
    (V : Submodule ℝ (Fin np → ℝ))
    (hC : ∀ w : Fin nf → ℝ, Cmat *ᵥ w = 0 → w = 0)
    (hB : ∀ v : Fin np → ℝ, v ∈ V → Bload *ᵥ v = 0 → v = 0) :
    Statistics.UncertaintyPropagation.IdentifiableOnAffine
      (loadObservationMatrix r a b S k Cmat Bload)
      (AffineSubspace.mk' theta0 V) := by
  rw [Statistics.UncertaintyPropagation.identifiableOnAffine_mk'_iff_trivial_ker]
  intro v hv hHv
  have h := hHv
  simp only [loadObservationMatrix, ← Matrix.mulVec_mulVec] at h
  have hK := hC _ h
  have hdet := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have hKK := Matrix.mul_nonsing_inv _ hdet
  have hBv : Bload *ᵥ v = 0 := by
    have e : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
          * (axialCompatibility r a b * S)) *ᵥ
        ((((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
          * (axialCompatibility r a b * S))⁻¹) *ᵥ (Bload *ᵥ v))
        = Bload *ᵥ v := by
      rw [Matrix.mulVec_mulVec, hKK, Matrix.one_mulVec]
    rw [hK, Matrix.mulVec_zero] at e
    exact e.symm
  exact hB v hv hBv

/-- Scope guard for unknown stiffness: the one-degree-of-freedom
displacement at unit load as a function of a positive scalar
stiffness `s`, namely `s⁻¹`, is not affine (in particular not linear)
in `s`. A stiffness-parameter inverse problem therefore cannot reuse
the fixed-stiffness linear observation matrix; it needs a separate
nonlinear or local model. No varying-stiffness identifiability
statement is made here. -/
lemma inv_not_affine_on_pos :
    ¬ ∃ a b : ℝ, ∀ s : ℝ, 0 < s → s⁻¹ = a * s + b := by
  rintro ⟨a, b, h⟩
  have h1 := h 1 one_pos
  have h2 := h 2 two_pos
  have h3 := h 3 three_pos
  norm_num at h1 h2 h3
  linarith

/-! ## I. Unit-load response -/

/-- Influence vector for the fixed output functional `aout`: the supported response to the
generalized unit load `aout` itself, `K⁻¹ *ᵥ aout` for the supported stiffness `K`. This definition
is the one inverse application of the section; the theorems below that read it as the unit-load
solution carry the positive-definiteness (or positive-weight and trivial-kernel) premise explicitly.
At a singular `K` the totalized inverse is `0`, and so is the influence vector. -/
noncomputable def influenceVector {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    [DecidableEq F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ) :
    F → ℝ :=
  ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
    * (axialCompatibility r a b * S))⁻¹ *ᵥ aout

/-- Unit-load response of the fixed output `aout` to the supported load `f`: the influence vector
paired with the load, `eta ⬝ᵥ f`. As a function of `f` this is the retained linear response map;
evaluating it needs no further inverse once the influence vector is formed. At a singular supported
stiffness the influence vector, and so every response, is `0`. -/
noncomputable def unitLoadResponse {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    [DecidableEq F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ) :
    (F → ℝ) →ₗ[ℝ] ℝ where
  toFun f := influenceVector r a b S k aout ⬝ᵥ f
  map_add' _ _ := dotProduct_add _ _ _
  map_smul' _ _ := by simp [dotProduct_smul, smul_eq_mul]

@[simp]
lemma unitLoadResponse_apply {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    [DecidableEq F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout f : F → ℝ) :
    unitLoadResponse r a b S k aout f
      = influenceVector r a b S k aout ⬝ᵥ f :=
  rfl

/-- The pointwise inverse diagonal recovers the separation-form
pairing vector from the elastic coefficient vector: for positive
member weights `k`, applying `Matrix.diagonal (fun e => (k e)⁻¹)` to
the coefficient vector `Matrix.diagonal k *ᵥ ((B S) *ᵥ u)` returns
`(B S) *ᵥ u`, whose entries are member length times elongation (the
coefficients are axial force divided by member length, as at
`supported_virtualWork_iff`). The inverses are scalar inverses
`(k e)⁻¹` (generalized compliances for the separation-form weights);
positivity is used as nonvanishing member by member. No stiffness
inverse occurs. -/
lemma supported_invDiagonal_mulVec_memberCoefficient {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hk : ∀ e, 0 < k e) (u : F → ℝ) :
    Matrix.diagonal (fun e => (k e)⁻¹)
        *ᵥ (Matrix.diagonal k
          *ᵥ ((axialCompatibility r a b * S) *ᵥ u))
      = (axialCompatibility r a b * S) *ᵥ u := by
  ext e
  simp only [mulVec_diagonal]
  exact inv_mul_cancel_left₀ (ne_of_gt (hk e)) _

/-- The influence vector solves the unit-load system: for
positive-definite supported stiffness, `K *ᵥ eta = aout`, where `eta`
is `influenceVector` for the fixed output `aout`. Later use takes
this solve equation for the one precomputed vector and forms no
further inverse. -/
lemma supported_influenceVector_mulVec {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)).PosDef)
    (aout : F → ℝ) :
    ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S))
      *ᵥ influenceVector r a b S k aout = aout := by
  exact (supported_mulVec_eq_iff_inv_mulVec r a b S k hPD).mpr rfl

/-- Fixed-output normalization by scaling: rescaling the fixed output
functional rescales its influence vector by the same factor. This is
linearity of the single inverse application in its load argument; no
solve reading and no definiteness premise is used. -/
lemma supported_influenceVector_smul {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    [DecidableEq F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (c : ℝ)
    (aout : F → ℝ) :
    influenceVector r a b S k (c • aout)
      = c • influenceVector r a b S k aout := by
  unfold influenceVector
  exact mulVec_smul _ _ _

/-- The response map computes the fixed output: for
positive-definite supported stiffness and a supported solution
`K *ᵥ u = f`, the unit-load response `eta ⬝ᵥ f` equals the output
`aout ⬝ᵥ u`, by reciprocal work for the two supported load cases `f`
and `aout` against the one stiffness. The output functional `aout`
is fixed while the load `f` varies. -/
lemma supported_unitLoadResponse_eq {J M F : Type*} [Fintype J]
    [DecidableEq J] [Fintype M] [DecidableEq M] [Fintype F]
    [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)).PosDef)
    (aout : F → ℝ) {f u : F → ℝ}
    (hu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f) :
    unitLoadResponse r a b S k aout f = aout ⬝ᵥ u := by
  have heta := supported_influenceVector_mulVec r a b S k hPD aout
  have hrec := supported_reciprocalWork r a b S k hu heta
  rw [unitLoadResponse_apply, dotProduct_comm]
  exact hrec

private theorem dotProduct_diag_mulVec {M : Type*} [Fintype M]
    [DecidableEq M] (k x y : M → ℝ) :
    x ⬝ᵥ (Matrix.diagonal k *ᵥ y)
      = (Matrix.diagonal k *ᵥ x) ⬝ᵥ y := by
  unfold dotProduct
  simp only [mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Unit-load identity in separation form: for positive-definite
supported stiffness and a supported solution `K *ᵥ u = f`, the fixed
output `aout ⬝ᵥ u` equals the unit-load separation-form coefficients
paired with `(B S) *ᵥ u` (member length times elongation; for a
member of positive length the coefficients are axial force divided
by member length).
The vector `K⁻¹ *ᵥ aout` is the influence vector by definition. No
inverse diagonal occurs, so no sign premise on the weights beyond
the positive-definiteness certificate is used. -/
lemma supported_unitLoad_identity_separationForm {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)).PosDef)
    (aout : F → ℝ) {f u : F → ℝ}
    (hu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f) :
    aout ⬝ᵥ u
      = (Matrix.diagonal k
          *ᵥ ((axialCompatibility r a b * S)
            *ᵥ influenceVector r a b S k aout))
        ⬝ᵥ ((axialCompatibility r a b * S) *ᵥ u) := by
  have heta := supported_influenceVector_mulVec r a b S k hPD aout
  have hrec := supported_reciprocalWork r a b S k hu heta
  have hK : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)) *ᵥ u
      = (axialCompatibility r a b * S)ᵀ *ᵥ
        (Matrix.diagonal k *ᵥ ((axialCompatibility r a b * S) *ᵥ u)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  rw [← hrec, ← hu, hK, dotProduct_comm, ← supported_pairing r a b S _ _]
  exact dotProduct_diag_mulVec k _ _

/-- Unit-load identity: for one supported stiffness with positive
member weights and positive-definite certificate, a supported
solution `K *ᵥ u = f` with separation-form coefficient vectors
`N = Matrix.diagonal k *ᵥ ((B S) *ᵥ u)` and
`n = Matrix.diagonal k *ᵥ ((B S) *ᵥ (K⁻¹ *ᵥ aout))` (for a member
of positive length, axial force divided by member length) satisfies
`aout ⬝ᵥ u = n ⬝ᵥ (D⁻¹ *ᵥ N)`, where `D⁻¹` is the pointwise inverse
diagonal `Matrix.diagonal (fun e => (k e)⁻¹)` (generalized
compliances for the separation-form weights — for physical weights
`EA / L ^ 3` this is `L ^ 3 / EA`, not member flexibility
`L / EA`; the physical axial-force form is
`supported_unitLoad_axialForce_identity` below). The separation form
is the preceding identity; the two member pairings agree through
recovery of `(B S) *ᵥ u` from `N`, which is where positivity of the
weights enters. Both load cases share the one stiffness, supports
and reference configuration. -/
theorem supported_unitLoad_identity {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hk : ∀ e, 0 < k e)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)).PosDef)
    (aout : F → ℝ) {f u : F → ℝ}
    (hu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f) :
    aout ⬝ᵥ u
      = (Matrix.diagonal k
          *ᵥ ((axialCompatibility r a b * S)
            *ᵥ influenceVector r a b S k aout))
        ⬝ᵥ (Matrix.diagonal (fun e => (k e)⁻¹)
          *ᵥ (Matrix.diagonal k
            *ᵥ ((axialCompatibility r a b * S) *ᵥ u))) := by
  have hrec := supported_invDiagonal_mulVec_memberCoefficient r a b S k hk u
  rw [hrec]
  exact supported_unitLoad_identity_separationForm r a b S k hPD aout hu

/-- Unit-load identity from the physical member data: for positive
member weights `k` and trivial supported kernel (no supported null
mode), a supported solution `K *ᵥ u = f` satisfies the same identity
`aout ⬝ᵥ u = n ⬝ᵥ (D⁻¹ *ᵥ N)` as above, with `N`, `n` and `D⁻¹`
read there. Positive definiteness enters through the supported
rigidity certificate. This is the entry point when the member data
and kernel condition, rather than an abstract definiteness
certificate, are in hand. -/
theorem supported_unitLoad_identity_of_kernel {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hk : ∀ e, 0 < k e)
    (hker : ∀ u : F → ℝ,
      (axialCompatibility r a b * S) *ᵥ u = 0 → u = 0)
    (aout : F → ℝ) {f u : F → ℝ}
    (hu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f) :
    aout ⬝ᵥ u
      = (Matrix.diagonal k
          *ᵥ ((axialCompatibility r a b * S)
            *ᵥ influenceVector r a b S k aout))
        ⬝ᵥ (Matrix.diagonal (fun e => (k e)⁻¹)
          *ᵥ (Matrix.diagonal k
            *ᵥ ((axialCompatibility r a b * S) *ᵥ u))) := by
  have hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)).PosDef :=
    (supported_posDef_iff r a b S k hk).mpr hker
  exact supported_unitLoad_identity r a b S k hk hPD aout hu


/-- Unit-load identity in physical axial forces: under the
`supported_unitLoad_identity` data with noncoincident endpoints,
rescaling the separation-form coefficients by member length
(`N e * L e` is the physical axial force, tension positive) gives
`aout ⬝ᵥ u = ∑ e, nphys e * (Nphys e / (k e * (L e) ^ 2))`; for
physical separation-form weights `k e = EA / (L e) ^ 3` the
denominator `k e * (L e) ^ 2` is `EA / L e`, the classical
dummy-unit-load sum `∑ n N L / EA`. -/
theorem supported_unitLoad_axialForce_identity {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hk : ∀ e, 0 < k e)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)).PosDef)
    (hne : ∀ e, r (a e) ≠ r (b e))
    (aout : F → ℝ) {f u : F → ℝ}
    (hu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f) :
    aout ⬝ᵥ u
      = (fun e => (Matrix.diagonal k
            *ᵥ ((axialCompatibility r a b * S)
              *ᵥ influenceVector r a b S k aout)) e * memberLength r a b e)
        ⬝ᵥ (fun e => ((Matrix.diagonal k
              *ᵥ ((axialCompatibility r a b * S) *ᵥ u)) e
            * memberLength r a b e) / (k e * memberLength r a b e ^ 2)) := by
  rw [supported_unitLoad_identity r a b S k hk hPD aout hu, dotProduct,
    dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  have hL : memberLength r a b e ≠ 0 :=
    ne_of_gt (memberLength_pos_of_ne r a b (hne e))
  have hk' : k e ≠ 0 := ne_of_gt (hk e)
  simp only [mulVec_diagonal]
  field_simp

/-! ## J. Finite load hull -/

/-- Finite superposition for the retained response map: with the output `aout` (hence the influence
vector) fixed, the response to a finite combination of vertex loads is the same combination of the
vertex responses, for arbitrary coefficients and an arbitrary scenario finset. This is linearity of
the pairing in the load argument over a finite sum; no solve reading, sign condition, or
normalization is used. No positivity of `k` or definiteness of the supported stiffness is assumed:
its inverse is the totalized matrix inverse, zero for a singular stiffness, and then the influence
vector and every response are `0`. -/
lemma supported_unitLoadResponse_sum_smul {J M F ι : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] [DecidableEq F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ)
    (s : Finset ι) (w : ι → ℝ) (f : ι → (F → ℝ)) :
    unitLoadResponse r a b S k aout (∑ i ∈ s, w i • f i)
      = ∑ i ∈ s, w i * unitLoadResponse r a b S k aout (f i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]

/-- Lower hull bound: for a nonempty scenario table with nonnegative coefficients summing to one,
the minimum vertex response is at most the response of the combined load, all at the one fixed
output and supported stiffness. The stiffness, supports and output do not change between scenarios;
no solve reading is used. No positivity of `k` or definiteness of the supported stiffness is
assumed: its inverse is the totalized matrix inverse, zero for a singular stiffness, and then the
influence vector and every response are `0`. -/
lemma supported_inf'_le_unitLoadResponse_sum_smul
    {J M F ι : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [DecidableEq M] [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ)
    (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (f : ι → (F → ℝ)) (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : ∑ i ∈ s, w i = 1) :
    s.inf' hs (fun i => unitLoadResponse r a b S k aout (f i))
      ≤ unitLoadResponse r a b S k aout (∑ i ∈ s, w i • f i) := by
  rw [supported_unitLoadResponse_sum_smul]
  calc s.inf' hs (fun i => unitLoadResponse r a b S k aout (f i))
      = ∑ i ∈ s, w i * s.inf' hs (fun i => unitLoadResponse r a b S k aout (f i)) := by
        rw [← Finset.sum_mul, hw₁, one_mul]
    _ ≤ ∑ i ∈ s, w i * unitLoadResponse r a b S k aout (f i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hi) (hw₀ i hi)

/-- Upper hull bound: for a nonempty scenario table with nonnegative coefficients summing to one,
the response of the combined load is at most the maximum vertex response, all at the one fixed
output and supported stiffness. The stiffness, supports and output do not change between scenarios;
no solve reading is used. No positivity of `k` or definiteness of the supported stiffness is
assumed: its inverse is the totalized matrix inverse, zero for a singular stiffness, and then the
influence vector and every response are `0`. -/
lemma supported_unitLoadResponse_sum_smul_le_sup'
    {J M F ι : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [DecidableEq M] [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ)
    (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (f : ι → (F → ℝ)) (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : ∑ i ∈ s, w i = 1) :
    unitLoadResponse r a b S k aout (∑ i ∈ s, w i • f i)
      ≤ s.sup' hs (fun i => unitLoadResponse r a b S k aout (f i)) := by
  rw [supported_unitLoadResponse_sum_smul]
  calc ∑ i ∈ s, w i * unitLoadResponse r a b S k aout (f i)
      ≤ ∑ i ∈ s, w i * s.sup' hs (fun i => unitLoadResponse r a b S k aout (f i)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun i => unitLoadResponse r a b S k aout (f i)) hi) (hw₀ i hi)
    _ = s.sup' hs (fun i => unitLoadResponse r a b S k aout (f i)) := by
        rw [← Finset.sum_mul, hw₁, one_mul]

/-- Finite load hull for the retained response: every convex combination of the vertex loads of a
nonempty finite table (nonnegative coefficients summing to one) has its fixed-output response
between the minimum and maximum vertex responses, at one fixed supported stiffness and output. The
coefficients are supplied finite data; no design factor is introduced. Stiffness, supports and
output are the same for every scenario and for the combined load. No positivity of `k` or
definiteness of the supported stiffness is assumed: its inverse is the totalized matrix inverse,
zero for a singular stiffness, and then the influence vector and every response are `0`. -/
theorem supported_unitLoadResponse_convexCombination_bounds
    {J M F ι : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [DecidableEq M] [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ)
    (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (f : ι → (F → ℝ)) (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : ∑ i ∈ s, w i = 1) :
    s.inf' hs (fun i => unitLoadResponse r a b S k aout (f i))
        ≤ unitLoadResponse r a b S k aout (∑ i ∈ s, w i • f i)
      ∧ unitLoadResponse r a b S k aout (∑ i ∈ s, w i • f i)
        ≤ s.sup' hs (fun i => unitLoadResponse r a b S k aout (f i)) := by
  exact ⟨supported_inf'_le_unitLoadResponse_sum_smul r a b S k aout s hs w f hw₀ hw₁,
    supported_unitLoadResponse_sum_smul_le_sup' r a b S k aout s hs w f hw₀ hw₁⟩

/-- Singleton table: a convex combination over one scenario is that scenario. The normalization over
the singleton forces its coefficient to be one, so the combined load has the vertex response; the
hull collapses to that value. No solve reading is used. No positivity of `k` or definiteness of the
supported stiffness is assumed: its inverse is the totalized matrix inverse, zero for a singular
stiffness, and then the influence vector and every response are `0`. -/
lemma supported_unitLoadResponse_singleton {J M F ι : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] [DecidableEq F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ)
    (i : ι) (w : ι → ℝ) (f : ι → (F → ℝ))
    (hw₁ : ∑ j ∈ ({i} : Finset ι), w j = 1) :
    unitLoadResponse r a b S k aout
        (∑ j ∈ ({i} : Finset ι), w j • f j)
      = unitLoadResponse r a b S k aout (f i) := by
  rw [Finset.sum_singleton] at hw₁
  rw [Finset.sum_singleton, hw₁, one_smul]

/-- Hull bounds in fixed-output form: for positive-definite
supported stiffness, vertex solutions `K *ᵥ (u i) = f i` on the
table and a supported solution `K *ᵥ u₀` of the combined load,
the fixed output `aout ⬝ᵥ u₀` of the combined solution lies
between the minimum and maximum vertex outputs
`aout ⬝ᵥ (u i)`. Every solution is against the one stiffness,
supports and reference configuration; the solutions are
presupposed, and existence stays with the supported unique
response. This is the hull bound read through the producer
identification of the retained response with the fixed output. -/
theorem supported_unitLoadResponse_convexCombination_output_bounds
    {J M F ι : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [DecidableEq M] [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)).PosDef)
    (aout : F → ℝ) (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (f u : ι → (F → ℝ)) (u₀ : F → ℝ)
    (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : ∑ i ∈ s, w i = 1)
    (hu : ∀ i ∈ s, ((axialCompatibility r a b * S)ᵀ
        * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ (u i) = f i)
    (hu₀ : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u₀
      = ∑ i ∈ s, w i • f i) :
    s.inf' hs (fun i => aout ⬝ᵥ (u i)) ≤ aout ⬝ᵥ u₀
      ∧ aout ⬝ᵥ u₀ ≤ s.sup' hs (fun i => aout ⬝ᵥ (u i)) := by
  have hveq : ∀ i ∈ s, unitLoadResponse r a b S k aout (f i) = aout ⬝ᵥ (u i) :=
    fun i hi => supported_unitLoadResponse_eq r a b S k hPD aout (hu i hi)
  have h0eq : unitLoadResponse r a b S k aout (∑ i ∈ s, w i • f i) = aout ⬝ᵥ u₀ :=
    supported_unitLoadResponse_eq r a b S k hPD aout hu₀
  have hmain :=
    supported_unitLoadResponse_convexCombination_bounds r a b S k aout s hs w f hw₀ hw₁
  have hinf : s.inf' hs (fun i => unitLoadResponse r a b S k aout (f i))
      = s.inf' hs (fun i => aout ⬝ᵥ (u i)) :=
    Finset.inf'_congr hs rfl hveq
  have hsup : s.sup' hs (fun i => unitLoadResponse r a b S k aout (f i))
      = s.sup' hs (fun i => aout ⬝ᵥ (u i)) :=
    Finset.sup'_congr hs rfl hveq
  rw [h0eq, hinf, hsup] at hmain
  exact hmain

/-- Absolute load hull for the retained response: for a nonempty scenario table with nonnegative
coefficients summing to one, the absolute response of the combined load is at most the maximum
absolute vertex response, at one fixed supported stiffness and output. Vertex responses may have
either sign or be zero; the bound is the absolute consequence of the two signed hull bounds. The
coefficients are supplied finite data; no design factor is introduced. Stiffness, supports and
output are the same for every scenario and for the combined load, the response is the one fixed
linear pairing, and no solve reading is used. No positivity of `k` or definiteness of the supported
stiffness is assumed: its inverse is the totalized matrix inverse, zero for a singular stiffness,
and then the influence vector and every response are `0`. -/
theorem supported_abs_unitLoadResponse_sum_smul_le_sup'_abs
    {J M F ι : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [DecidableEq M] [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ)
    (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (f : ι → (F → ℝ)) (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : ∑ i ∈ s, w i = 1) :
    |unitLoadResponse r a b S k aout (∑ i ∈ s, w i • f i)|
      ≤ s.sup' hs (fun i => |unitLoadResponse r a b S k aout (f i)|) := by
  obtain ⟨hLo, hHi⟩ := supported_unitLoadResponse_convexCombination_bounds r a b S k aout s hs w f hw₀ hw₁
  rw [abs_le]
  constructor
  · calc -s.sup' hs (fun i => |unitLoadResponse r a b S k aout (f i)|)
        ≤ s.inf' hs (fun i => unitLoadResponse r a b S k aout (f i)) := by
          refine Finset.le_inf' hs _ fun i hi => ?_
          calc -s.sup' hs (fun i => |unitLoadResponse r a b S k aout (f i)|)
              ≤ -|unitLoadResponse r a b S k aout (f i)| := by
                apply neg_le_neg
                exact Finset.le_sup' (fun i => |unitLoadResponse r a b S k aout (f i)|) hi
            _ ≤ unitLoadResponse r a b S k aout (f i) := neg_abs_le _
      _ ≤ unitLoadResponse r a b S k aout (∑ i ∈ s, w i • f i) := hLo
  · calc unitLoadResponse r a b S k aout (∑ i ∈ s, w i • f i)
        ≤ s.sup' hs (fun i => unitLoadResponse r a b S k aout (f i)) := hHi
      _ ≤ s.sup' hs (fun i => |unitLoadResponse r a b S k aout (f i)|) := by
          apply Finset.sup'_mono_fun
          intro i _
          exact le_abs_self _

/-- Absolute hull bound in fixed-output form: for positive-definite
supported stiffness, vertex solutions `K *ᵥ (u i) = f i` on the
table and a supported solution `K *ᵥ u₀` of the combined load,
the absolute fixed output `|aout ⬝ᵥ u₀|` of the combined solution
is at most the maximum absolute vertex output
`s.sup' hs (fun i => |aout ⬝ᵥ (u i)|)`. Every solution is against
the one stiffness, supports and reference configuration; the
solutions are presupposed, and existence stays with the supported
unique response. This is the absolute hull bound read through the
identification of the retained response with the fixed output,
over the signed hull bounds. -/
theorem supported_abs_convexCombination_output_le_sup'_abs
    {J M F ι : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [DecidableEq M] [Fintype F] [DecidableEq F]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
      * (axialCompatibility r a b * S)).PosDef)
    (aout : F → ℝ) (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (f u : ι → (F → ℝ)) (u₀ : F → ℝ)
    (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : ∑ i ∈ s, w i = 1)
    (hu : ∀ i ∈ s, ((axialCompatibility r a b * S)ᵀ
        * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ (u i) = f i)
    (hu₀ : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u₀
      = ∑ i ∈ s, w i • f i) :
    |aout ⬝ᵥ u₀| ≤ s.sup' hs (fun i => |aout ⬝ᵥ (u i)|) := by
  have hmain :=
    supported_abs_unitLoadResponse_sum_smul_le_sup'_abs r a b S k aout s hs w f
      hw₀ hw₁
  have hpt : ∀ i ∈ s, unitLoadResponse r a b S k aout (f i) = aout ⬝ᵥ (u i) :=
    fun i hi => supported_unitLoadResponse_eq r a b S k hPD aout (hu i hi)
  have hsup :
      s.sup' hs (fun i => |unitLoadResponse r a b S k aout (f i)|) =
        s.sup' hs (fun i => |aout ⬝ᵥ (u i)|) :=
    Finset.sup'_congr hs rfl (fun i hi => by
      show |unitLoadResponse r a b S k aout (f i)| = |aout ⬝ᵥ (u i)|
      rw [hpt i hi])
  rw [supported_unitLoadResponse_eq r a b S k hPD aout hu₀, hsup] at hmain
  exact hmain

/-! ## K. Reduced determinate statics -/

/-- Elastic member forces satisfy reduced equilibrium: for a
supported solution `u`, collecting the elastic forces
`Matrix.diagonal d *ᵥ (Bs *ᵥ u)` through the transpose returns
the supported load. No invertibility or positivity hypothesis
is used. -/
theorem reduced_equilibrium_of_elastic {n : Type*} [Fintype n]
    [DecidableEq n] (Bs : Matrix n n ℝ) (d : n → ℝ)
    {f u : n → ℝ}
    (hu : (Bsᵀ * Matrix.diagonal d * Bs) *ᵥ u = f) :
    Bsᵀ *ᵥ (Matrix.diagonal d *ᵥ (Bs *ᵥ u)) = f := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hu
  exact hu

/-- Reduced determinate statics: for square invertible reduced
compatibility `Bs`, a member-force vector `N` satisfies reduced
equilibrium `Bsᵀ *ᵥ N = f` exactly when it is the explicit
statics solution `(Bsᵀ)⁻¹ *ᵥ f`. -/
theorem reduced_equilibrium_iff_eq_inv {n : Type*} [Fintype n]
    [DecidableEq n] (Bs : Matrix n n ℝ) (hBs : IsUnit Bs.det)
    {f N : n → ℝ} :
    Bsᵀ *ᵥ N = f ↔ N = (Bsᵀ)⁻¹ *ᵥ f := by
  have hT : IsUnit (Bsᵀ).det := by
    rw [Matrix.det_transpose]
    exact hBs
  exact Matrix.mulVec_eq_iff_inv_mulVec hT

/-- Elastic forces agree with determinate statics: for square
invertible `Bs`, axial weights `d` and a supported
solution `u`, the elastic member-force vector
`Matrix.diagonal d *ᵥ (Bs *ᵥ u)` is the statics solution
`(Bsᵀ)⁻¹ *ᵥ f`. -/
theorem reduced_memberForce_eq_inv_mulVec {n : Type*}
    [Fintype n] [DecidableEq n] (Bs : Matrix n n ℝ)
    (hBs : IsUnit Bs.det) (d : n → ℝ)
    {f u : n → ℝ}
    (hu : (Bsᵀ * Matrix.diagonal d * Bs) *ᵥ u = f) :
    Matrix.diagonal d *ᵥ (Bs *ᵥ u) = (Bsᵀ)⁻¹ *ᵥ f := by
  exact (reduced_equilibrium_iff_eq_inv Bs hBs).mp
    (reduced_equilibrium_of_elastic Bs d hu)

/-- Member forces are independent of the axial weights for a
square invertible `Bs` (the statically determinate case): two
axial diagonals and supported solutions for the same
geometry, supports and load give the same elastic member-force
vector. The displacements may differ; the forces do not. -/
theorem reduced_memberForce_indep_of_diagonal {n : Type*}
    [Fintype n] [DecidableEq n] (Bs : Matrix n n ℝ)
    (hBs : IsUnit Bs.det) (d₁ d₂ : n → ℝ)
    {f u₁ u₂ : n → ℝ}
    (hu₁ : (Bsᵀ * Matrix.diagonal d₁ * Bs) *ᵥ u₁ = f)
    (hu₂ : (Bsᵀ * Matrix.diagonal d₂ * Bs) *ᵥ u₂ = f) :
    Matrix.diagonal d₁ *ᵥ (Bs *ᵥ u₁)
      = Matrix.diagonal d₂ *ᵥ (Bs *ᵥ u₂) := by
  rw [reduced_memberForce_eq_inv_mulVec Bs hBs d₁ hu₁,
    reduced_memberForce_eq_inv_mulVec Bs hBs d₂ hu₂]

/-- The supported solution exists and is unique: for square
invertible `Bs` and nonvanishing axial weights `d`, every
supported load `f` has exactly one supported displacement
`u`. -/
theorem reduced_stiffness_existsUnique {n : Type*} [Fintype n]
    [DecidableEq n] (Bs : Matrix n n ℝ) (hBs : IsUnit Bs.det)
    (d : n → ℝ) (hd : ∀ e, d e ≠ 0) (f : n → ℝ) :
    ∃! u : n → ℝ, (Bsᵀ * Matrix.diagonal d * Bs) *ᵥ u = f := by
  have hD : IsUnit (Matrix.diagonal d).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun e _ => hd e
  have hK : IsUnit (Bsᵀ * Matrix.diagonal d * Bs).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact (hBs.mul hD).mul hBs
  exact Matrix.exists_unique_mulVec_eq
    (Matrix.mulVec_injective_of_det_ne_zero (isUnit_iff_ne_zero.mp hK)) f

/-- Positive-weight form of `reduced_stiffness_existsUnique`:
positive axial weights are nonvanishing. -/
theorem reduced_stiffness_existsUnique_of_pos {n : Type*}
    [Fintype n] [DecidableEq n] (Bs : Matrix n n ℝ)
    (hBs : IsUnit Bs.det) (d : n → ℝ) (hd : ∀ e, 0 < d e)
    (f : n → ℝ) :
    ∃! u : n → ℝ, (Bsᵀ * Matrix.diagonal d * Bs) *ᵥ u = f :=
  reduced_stiffness_existsUnique Bs hBs d
    (fun e => ne_of_gt (hd e)) f

/-- Truss instance: for the supported compatibility matrix
`axialCompatibility r a b * S` with free coordinates indexed by
the members, square and invertible, member weights
`k` and a supported solution `u`, the separation-form elastic
coefficient vector (axial force divided by member length, the
convention of `supported_virtualWork_iff`) is the reduced
statics solution
`((axialCompatibility r a b * S)ᵀ)⁻¹ *ᵥ f`, and it equilibrates
the supported load in virtual work: internal work
`s ⬝ᵥ ((axialCompatibility r a b * S) *ᵥ v)` equals external
work `f ⬝ᵥ v` for every supported virtual displacement `v`.
The virtual-work conjunct is the canonical
supported virtual-work correspondence.
Reactions at constrained joint coordinates are not addressed:
`f` is the supported load in free coordinates. -/
theorem truss_reduced_memberCoefficient_eq_inv_mulVec {J M : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) M ℝ)
    (hdet : IsUnit (axialCompatibility r a b * S).det)
    (k : M → ℝ) {f u : M → ℝ}
    (hu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f) :
    Matrix.diagonal k *ᵥ ((axialCompatibility r a b * S) *ᵥ u)
        = ((axialCompatibility r a b * S)ᵀ)⁻¹ *ᵥ f
      ∧ ∀ v : M → ℝ,
          (Matrix.diagonal k
              *ᵥ ((axialCompatibility r a b * S) *ᵥ u))
            ⬝ᵥ ((axialCompatibility r a b * S) *ᵥ v) = f ⬝ᵥ v := by
  have hmain := reduced_memberForce_eq_inv_mulVec _ hdet k hu
  refine ⟨hmain, ?_⟩
  have heq := reduced_equilibrium_of_elastic _ _ hu
  exact (supported_virtualWork_iff r a b S _ f).mp heq


/-- Physical axial forces from the separation-form
coefficients: with the same data as
`truss_reduced_memberCoefficient_eq_inv_mulVec`, the
physical axial force vector `fun e => s e * L e` (member
length times the separation-form coefficient
`s = Matrix.diagonal k *ᵥ ((B S) *ᵥ u)`, tension positive)
is the memberwise length rescaling of the reduced statics
coefficient solution. In particular the physical forces,
like the coefficients, do not depend on the axial
weights `k` through anything but the common statics
solution. -/
theorem truss_reduced_axialForce_eq {J M : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) M ℝ)
    (hdet : IsUnit (axialCompatibility r a b * S).det)
    (k : M → ℝ) {f u : M → ℝ}
    (hu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u = f) :
    (fun e => (Matrix.diagonal k
        *ᵥ ((axialCompatibility r a b * S) *ᵥ u)) e
          * memberLength r a b e)
      = fun e => (((axialCompatibility r a b * S)ᵀ)⁻¹ *ᵥ f) e
          * memberLength r a b e := by
  funext e
  rw [(truss_reduced_memberCoefficient_eq_inv_mulVec r a b S hdet k hu).1]

end Mechanics.TrussCompatibility
