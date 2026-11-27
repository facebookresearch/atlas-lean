/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GroundCoordinates
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Eliminating a vertex with one neighbor

Let A be a real matrix on a finite set V, r ∈ V, and u ∈ I = V ∖ {r}. Put p = Aᵣᵣ and c = Aᵣᵤ.
The retained matrix is S = A|I − (c²/p)eᵤeᵤᵀ, the new right-hand side is b′ = b|I − (c
bᵣ/p)eᵤ, and back substitution restores xᵣ = (bᵣ − c zᵤ)/p. A positive definite symmetric
matrix with nonpositive off-diagonal entries and nonnegative row sums retains these properties
after this elimination. The factorization uses the full diagonal pivot p.

Reference: Spielman and Teng, Nearly-Linear Time Algorithms for Preconditioning and Solving
Symmetric, Diagonally Dominant Linear Systems, arXiv:cs/0607105v5, typesetting dated 26
November 2024, §§1.1, 3.1, 4.1 and 5.
-/

@[expose] public section

noncomputable section

open Finset
open scoped BigOperators

namespace Matrix

variable {V : Type*} [DecidableEq V]

/-- **The retained matrix for one-neighbor elimination.**

For a real matrix A on a set V, r ∈ V and u ∈ I = V ∖ {r}, put p = Aᵣᵣ and c = Aᵣᵤ. Define Sᵢⱼ
= Aᵢⱼ − (c²/p) when i = j = u, and Sᵢⱼ = Aᵢⱼ otherwise. Real division defines this matrix also
when p = 0.
-/
def degreeOnePivot (A : Matrix V V ℝ) (r : V) (u : {v : V // v ≠ r}) :
    Matrix {v : V // v ≠ r} {v : V // v ≠ r} ℝ :=
  fun i j => if i = u ∧ j = u then
    A u.val u.val - (A r u.val) ^ 2 / A r r else A i.val j.val

/-- **Forward substitution at one neighbor.**

For a real matrix A on V, r ∈ V, u ∈ I = V ∖ {r}, p = Aᵣᵣ and c = Aᵣᵤ, the linear map b ↦ b′
is b′ᵢ = bᵢ − 1_{i=u} c bᵣ/p. It is defined for every p, with real division at p = 0.
-/
def degreeOneRHS (A : Matrix V V ℝ) (r : V) (u : {v : V // v ≠ r}) :
    (V → ℝ) →ₗ[ℝ] ({v : V // v ≠ r} → ℝ) where
  toFun b := Function.update (fun v => b v.val) u
    (b u.val - A r u.val * b r / A r r)
  map_add' b c := by
    ext i
    by_cases hi : i = u
    · subst i
      simp only [Function.update_self, Pi.add_apply]
      ring
    · simp [hi]
  map_smul' k b := by
    ext i
    by_cases hi : i = u
    · subst i
      simp only [Function.update_self, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [hi]

/-- **Back substitution at one neighbor.**

For a real matrix A on V, r ∈ V, u ∈ I = V ∖ {r}, p = Aᵣᵣ and c = Aᵣᵤ, define the linear map
L(b,z) by L(b,z)ᵣ = (bᵣ − c zᵤ)/p and L(b,z)ᵢ = zᵢ for i ∈ I. It is linear jointly in b and z.
-/
def degreeOneLift (A : Matrix V V ℝ) (r : V) (u : {v : V // v ≠ r}) :
    (V → ℝ) × ({v : V // v ≠ r} → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun bz i := if hi : i = r then (bz.1 r - A r u.val * bz.2 u) / A r r else bz.2 ⟨i, hi⟩
  map_add' bz cw := by
    ext i
    by_cases hi : i = r
    · subst i
      simp
      ring
    · simp [hi]
  map_smul' k bz := by
    ext i
    by_cases hi : i = r
    · subst i
      simp
      ring
    · simp [hi]

/-- **The one-neighbor factor column.**

For a real matrix A on V, r ∈ V and u ∈ V ∖ {r}, put p = Aᵣᵣ and c = Aᵣᵤ. Define l = √p eᵣ +
(c/√p)eᵤ. The formula uses the real square root and real division for every p.
-/
def degreeOneColumn (A : Matrix V V ℝ) (r : V) (u : {v : V // v ≠ r}) : V → ℝ :=
  Real.sqrt (A r r) • Pi.single r 1 + (A r u.val / Real.sqrt (A r r)) • Pi.single u.val 1

variable (A : Matrix V V ℝ) (r : V) (u : {v : V // v ≠ r})

theorem degreeOnePivot_apply (i j : {v : V // v ≠ r}) :
    degreeOnePivot A r u i j =
      A i.val j.val - if i = u ∧ j = u then (A r u.val) ^ 2 / A r r else 0 := by
  by_cases hi : i = u <;> by_cases hj : j = u <;>
    simp [degreeOnePivot, hi, hj]

@[simp]
theorem degreeOnePivot_apply_of_ne {i j : {v : V // v ≠ r}} (hij : i ≠ j) :
    degreeOnePivot A r u i j = A i.val j.val := by
  rw [degreeOnePivot_apply]
  have h : ¬ (i = u ∧ j = u) := fun h => hij (h.1.trans h.2.symm)
  simp [h]

@[simp]
theorem degreeOneRHS_apply (b : V → ℝ) (i : {v : V // v ≠ r}) :
    degreeOneRHS A r u b i =
      b i.val - if i = u then A r u.val * b r / A r r else 0 := by
  by_cases hi : i = u <;> simp [degreeOneRHS, hi]

@[simp]
theorem degreeOneLift_root (b : V → ℝ) (z : {v : V // v ≠ r} → ℝ) :
    degreeOneLift A r u (b, z) r = (b r - A r u.val * z u) / A r r := by
  simp [degreeOneLift]

@[simp]
theorem degreeOneLift_retained (b : V → ℝ) (z : {v : V // v ≠ r} → ℝ)
    (i : {v : V // v ≠ r}) : degreeOneLift A r u (b, z) i.val = z i := by
  simp [degreeOneLift, i.property]

theorem degreeOneColumn_eq_zero {i : V} (hir : i ≠ r) (hiu : i ≠ u.val) :
    degreeOneColumn A r u i = 0 := by
  simp [degreeOneColumn, hir, hiu]

private theorem pivot_rank : degreeOnePivot A r u =
    A.submatrix Subtype.val Subtype.val -
      ((A r u.val) ^ 2 / A r r) • vecMulVec (Pi.single u 1) (Pi.single u 1) := by
  ext i j
  by_cases hi : i = u <;> by_cases hj : j = u <;>
    simp [degreeOnePivot_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, hi, hj]

private theorem rhs_sub (b : V → ℝ) : degreeOneRHS A r u b =
    (fun i => b i.val) - (A r u.val * b r / A r r) • Pi.single u 1 := by
  ext i
  by_cases hi : i = u <;> simp [degreeOneRHS_apply, hi]

private def liftMatrix : Matrix V {v : V // v ≠ r} ℝ :=
  zeroInsertion r - (A r u.val / A r r) • vecMulVec (Pi.single r 1) (Pi.single u 1)

variable [Fintype V]

private theorem lift_add (b : V → ℝ) (z : {v : V // v ≠ r} → ℝ) :
    degreeOneLift A r u (b, z) = zeroInsertion r *ᵥ z +
      ((b r - A r u.val * z u) / A r r) • Pi.single r 1 := by
  ext i
  by_cases hi : i = r
  · subst i
    simp
  · simp [degreeOneLift, zeroInsertion_mulVec_apply, hi]

private theorem zeroInsertion_single :
    zeroInsertion r *ᵥ (Pi.single u 1) = Pi.single u.val 1 := by
  ext i
  simp [zeroInsertion_eq_submatrix_one, mulVec_single, Matrix.one_apply, Pi.single_apply]

private theorem principal_action (z : {v : V // v ≠ r} → ℝ) :
    groundRestriction r *ᵥ (A *ᵥ (zeroInsertion r *ᵥ z)) =
      A.submatrix Subtype.val Subtype.val *ᵥ z := by
  rw [mulVec_mulVec, mulVec_mulVec, groundRestriction_mul_mul_zeroInsertion]

private theorem pivot_row_action
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0)
    (z : {v : V // v ≠ r} → ℝ) :
    (A *ᵥ (zeroInsertion r *ᵥ z)) r = A r u.val * z u := by
  rw [mulVec_mulVec, zeroInsertion_eq_submatrix_one]
  have hm := mul_submatrix_one (Equiv.refl V) (Subtype.val : {v : V // v ≠ r} → V) A
  simp only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] at hm
  rw [hm, mulVec, dotProduct, Finset.sum_eq_single u]
  · rfl
  · intro j _ hju
    have hj : j.val ≠ u.val := fun h => hju (Subtype.ext h)
    simp [hs j.val j.property hj]
  · simp

private theorem column_action (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0) :
    A *ᵥ Pi.single r 1 = A r r • Pi.single r 1 + A r u.val • Pi.single u.val 1 := by
  rw [mulVec_single_one]
  ext i
  change A i r = A r r * (Pi.single r 1 : V → ℝ) i +
    A r u.val * (Pi.single u.val 1 : V → ℝ) i
  have hsym : A i r = A r i := by simpa only [star_trivial] using hA.apply r i
  rw [hsym]
  by_cases hir : i = r
  · subst i
    simp [Ne.symm u.property]
  · by_cases hiu : i = u.val
    · subst i
      simp [u.property]
    · simp [hir, hiu, hs i hir hiu]

private theorem action_split
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0)
    (z : {v : V // v ≠ r} → ℝ) :
    A *ᵥ (zeroInsertion r *ᵥ z) =
      zeroInsertion r *ᵥ (A.submatrix Subtype.val Subtype.val *ᵥ z) +
        (A r u.val * z u) • Pi.single r 1 := by
  ext i
  by_cases hi : i = r
  · subst i
    rw [pivot_row_action A r u hs z, Pi.add_apply, zeroInsertion_mulVec_root]
    simp
  · have h := congrArg (fun x : {v : V // v ≠ r} → ℝ => x ⟨i, hi⟩)
      (principal_action A r z)
    simpa only [groundRestriction_mulVec, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, zeroInsertion_mulVec_apply, dite_eq_right hi, Pi.single_apply,
      ite_eq_right hi, mul_zero, add_zero] using h

private theorem vector_split (b : V → ℝ) :
    b = zeroInsertion r *ᵥ (fun i => b i.val) + b r • Pi.single r 1 := by
  ext i
  by_cases hi : i = r
  · subst i
    simp
  · simp [zeroInsertion_mulVec_apply, hi]

private theorem pivot_action (z : {v : V // v ≠ r} → ℝ) :
    degreeOnePivot A r u *ᵥ z = A.submatrix Subtype.val Subtype.val *ᵥ z -
      ((A r u.val) ^ 2 / A r r * z u) • Pi.single u 1 := by
  rw [pivot_rank, sub_mulVec, smul_mulVec, vecMulVec_mulVec]
  ext i
  simp [mul_comm, mul_assoc, mul_left_comm]

/-- **Residual after one-neighbor back substitution.**

Let A be a real matrix on a finite set V, r ∈ V, and u ∈ I = V ∖ {r}. Put p = Aᵣᵣ and c = Aᵣᵤ.
Assume A is symmetric, Aᵣⱼ = 0 for j outside {r,u}, and p ≠ 0. Let S = A|I − (c²/p)eᵤeᵤᵀ, b′ =
b|I − (c bᵣ/p)eᵤ, and L(b,z)ᵣ = (bᵣ − c zᵤ)/p with L(b,z)|I = z. If J inserts a zero at r,
then A L(b,z) − b = J(Sz − b′) for all b and z.
-/
theorem degreeOneLift_residual (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0) (hp : A r r ≠ 0)
    (b : V → ℝ) (z : {v : V // v ≠ r} → ℝ) :
    A *ᵥ degreeOneLift A r u (b, z) - b =
      zeroInsertion r *ᵥ (degreeOnePivot A r u *ᵥ z - degreeOneRHS A r u b) := by
  rw [lift_add, mulVec_add, mulVec_smul, action_split A r u hs z,
    column_action A r u hA hs]
  conv_lhs => rhs; rw [vector_split r b]
  simp only [pivot_action, rhs_sub, mulVec_sub, mulVec_smul, zeroInsertion_single]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hp]
  ring

/-- **Restriction of one-neighbor back substitution.**

Let A be a real matrix on a finite set V, r ∈ V, and u ∈ I = V ∖ {r}. Put p = Aᵣᵣ and c = Aᵣᵤ.
For L(b,z)ᵣ = (bᵣ − c zᵤ)/p and L(b,z)|I = z, the coordinate restriction C : ℝ^V → ℝ^I
satisfies C L(b,z) = z for every b and z, with no nonzero-pivot condition.
-/
theorem degreeOneLift_restrict (b : V → ℝ) (z : {v : V // v ≠ r} → ℝ) :
    groundRestriction r *ᵥ degreeOneLift A r u (b, z) = z := by
  rw [groundRestriction_mulVec]
  ext i
  exact degreeOneLift_retained A r u b z i

private theorem liftMatrix_mulVec (z : {v : V // v ≠ r} → ℝ) :
    liftMatrix A r u *ᵥ z = degreeOneLift A r u (0, z) := by
  rw [liftMatrix, sub_mulVec, smul_mulVec, vecMulVec_mulVec, lift_add]
  ext i
  simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm, sub_eq_add_neg]

private theorem restriction_liftMatrix : groundRestriction r * liftMatrix A r u = 1 := by
  apply ext_of_mulVec_single
  intro i
  rw [← mulVec_mulVec, liftMatrix_mulVec, degreeOneLift_restrict, one_mulVec]

private theorem source_liftMatrix (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0) (hp : A r r ≠ 0) :
    A * liftMatrix A r u = zeroInsertion r * degreeOnePivot A r u := by
  apply ext_of_mulVec_single
  intro i
  rw [← mulVec_mulVec, ← mulVec_mulVec, liftMatrix_mulVec]
  have h := degreeOneLift_residual A r u hA hs hp 0 (Pi.single i 1)
  simpa only [map_zero, sub_zero] using h

private theorem liftMatrix_congruence (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0) (hp : A r r ≠ 0) :
    (liftMatrix A r u)ᴴ * A * liftMatrix A r u = degreeOnePivot A r u := by
  have ht : (liftMatrix A r u)ᵀ * zeroInsertion r = 1 := by
    have h := congrArg Matrix.transpose (restriction_liftMatrix A r u)
    simpa only [transpose_mul, transpose_one, zeroInsertion] using h
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, source_liftMatrix A r u hA hs hp,
    ← Matrix.mul_assoc, ht, one_mul]

omit [Fintype V] in
private theorem pivot_posDef [Finite V] (hA : A.PosDef)
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0) : (degreeOnePivot A r u).PosDef := by
  let := Fintype.ofFinite V
  have hinj : Function.Injective (liftMatrix A r u).mulVec := by
    intro z w hzw
    have h := congrArg (fun x => groundRestriction r *ᵥ x) hzw
    simpa only [mulVec_mulVec, restriction_liftMatrix, one_mulVec] using h
  have h := hA.conjTranspose_mul_mul_same hinj
  rwa [liftMatrix_congruence A r u hA.isHermitian hs (ne_of_gt hA.diag_pos)] at h

/-- **Energy of a one-neighbor lifted error.**

Let A be a real matrix on a finite set V, r ∈ V, and u ∈ I = V ∖ {r}. Put p = Aᵣᵣ and c = Aᵣᵤ.
Assume A is symmetric, Aᵣⱼ = 0 for j outside {r,u}, and p ≠ 0. Let S = A|I − (c²/p)eᵤeᵤᵀ and
let L(b,z) restore the root coordinate (bᵣ − c zᵤ)/p. For e = L(b,z) − L(b,w), one has eᵀ A e
= (z − w)ᵀ S(z − w).
-/
theorem degreeOneLift_error_energy (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0) (hp : A r r ≠ 0)
    (b : V → ℝ) (z w : {v : V // v ≠ r} → ℝ) :
    (degreeOneLift A r u (b, z) - degreeOneLift A r u (b, w)) ⬝ᵥ
        (A *ᵥ (degreeOneLift A r u (b, z) - degreeOneLift A r u (b, w))) =
      (z - w) ⬝ᵥ (degreeOnePivot A r u *ᵥ (z - w)) := by
  have hd : degreeOneLift A r u (b, z) - degreeOneLift A r u (b, w) =
      liftMatrix A r u *ᵥ (z - w) := by
    rw [liftMatrix_mulVec, ← map_sub]
    simp only [Prod.mk_sub_mk, sub_self]
  rw [hd]
  calc
    (liftMatrix A r u *ᵥ (z - w)) ⬝ᵥ (A *ᵥ (liftMatrix A r u *ᵥ (z - w))) =
        (z - w) ⬝ᵥ ((liftMatrix A r u)ᵀ *ᵥ (A *ᵥ (liftMatrix A r u *ᵥ (z - w)))) := by
      exact (dotProduct_comm _ _).trans
        (by simpa only [transpose_transpose] using
          dotProduct_transpose_mulVec (liftMatrix A r u)ᵀ (A *ᵥ (liftMatrix A r u *ᵥ (z - w))) (z - w))
    _ = (z - w) ⬝ᵥ (((liftMatrix A r u)ᴴ * A * liftMatrix A r u) *ᵥ (z - w)) := by
      rw [conjTranspose_eq_transpose_of_trivial, mulVec_mulVec, mulVec_mulVec]
    _ = (z - w) ⬝ᵥ (degreeOnePivot A r u *ᵥ (z - w)) := by
      rw [liftMatrix_congruence A r u hA hs hp]

private theorem sum_delete (f : V → ℝ) :
    (∑ i : {v : V // v ≠ r}, f i.val) = (∑ i, f i) - f r := by
  have h := Fintype.sum_eq_add_sum_subtype_ne f r
  linarith only [h]

omit [DecidableEq V] in
/-- **Row sum at a one-neighbor pivot.**

Let A be a real matrix on a finite set V, r ∈ V, and u ∈ I = V ∖ {r}. Put p = Aᵣᵣ and c = Aᵣᵤ.
If Aᵣⱼ = 0 outside {r,u}, then ∑ⱼ Aᵣⱼ = p + c.
-/
theorem degreeOnePivot_surplus
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0) :
    (∑ j, A r j) = A r r + A r u.val := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => A r j) r]
  congr 1
  apply Finset.sum_eq_single u
  · intro j _ hju
    exact hs j.val j.property (fun h => hju (Subtype.ext h))
  · simp

/-- **Retained row sums after one-neighbor elimination.**

Let A be a real matrix on a finite set V, r ∈ V, and u ∈ I = V ∖ {r}. Put p = Aᵣᵣ and c = Aᵣᵤ.
Assume A is symmetric, Aᵣⱼ = 0 for j outside {r,u}, and p ≠ 0. For S = A|I − (c²/p)eᵤeᵤᵀ and i
∈ I, one has ∑ⱼ∈I Sᵢⱼ = ∑ⱼ∈V Aᵢⱼ − 1_{i=u}(c/p)∑ⱼ∈V Aᵣⱼ.
-/
theorem degreeOnePivot_rowSum (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0) (hp : A r r ≠ 0)
    (i : {v : V // v ≠ r}) :
    (∑ j, degreeOnePivot A r u i j) = (∑ j, A i.val j) -
      if i = u then (A r u.val / A r r) * ∑ j, A r j else 0 := by
  by_cases hi : i = u
  · subst i
    have hsum : (∑ j, degreeOnePivot A r u u j) =
        (∑ j : {v : V // v ≠ r}, A u.val j.val) - (A r u.val) ^ 2 / A r r := by
      simp [degreeOnePivot_apply, Finset.sum_sub_distrib]
    have hcol : A u.val r = A r u.val := by simpa only [star_trivial] using hA.apply r u.val
    rw [hsum, sum_delete r (fun j => A u.val j), hcol,
      degreeOnePivot_surplus A r u hs]
    simp only [ite_true]
    field_simp [hp]
    ring
  · have hcol : A i.val r = 0 := by
      have h := hA.apply r i.val
      simpa only [star_trivial, hs i.val i.property (fun h => hi (Subtype.ext h))] using h
    simp only [degreeOnePivot_apply, hi, false_and, ite_false, sub_zero,
      sum_delete r (fun j => A i.val j), hcol]

/-- **Preservation of positive definite diagonal dominance.**

Let A be a real matrix on a finite set V, r ∈ V, and u ∈ I = V ∖ {r}. Put p = Aᵣᵣ and c = Aᵣᵤ.
Assume A is positive definite, its off-diagonal entries are nonpositive, its row sums are
nonnegative, and Aᵣⱼ = 0 outside {r,u}. Then S = A|I − (c²/p)eᵤeᵤᵀ is positive definite, has
nonpositive off-diagonal entries and has nonnegative row sums.
-/
theorem degreeOnePivot_preserves_sddm (hA : A.PosDef)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hrows : ∀ i, 0 ≤ ∑ j, A i j)
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0) :
    (degreeOnePivot A r u).PosDef ∧
      (∀ i j, i ≠ j → degreeOnePivot A r u i j ≤ 0) ∧
      ∀ i, 0 ≤ ∑ j, degreeOnePivot A r u i j := by
  have hp : 0 < A r r := hA.diag_pos
  have hq : A r u.val ≤ 0 := hoff r u.val (Ne.symm u.property)
  refine ⟨pivot_posDef A r u hA hs, ?_, ?_⟩
  · intro i j hij
    rw [degreeOnePivot_apply_of_ne A r u hij]
    exact hoff i.val j.val (fun h => hij (Subtype.ext h))
  · intro i
    rw [degreeOnePivot_rowSum A r u hA.isHermitian hs (ne_of_gt hp) i]
    by_cases hi : i = u
    · rw [ite_eq_left hi]
      exact sub_nonneg.mpr (le_trans
        (mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hq hp.le) (hrows r))
        (hrows i.val))
    · simpa only [ite_eq_right hi, sub_zero] using hrows i.val

private theorem restriction_root_single : groundRestriction r *ᵥ Pi.single r 1 = 0 := by
  rw [groundRestriction_mulVec]
  ext i
  simp [i.property]

private theorem restriction_single (j : {v : V // v ≠ r}) :
    groundRestriction r *ᵥ Pi.single j.val 1 = Pi.single j 1 := by
  rw [groundRestriction_mulVec]
  ext i
  simp [Pi.single_apply, Subtype.val_injective.eq_iff]

private theorem embedding_apply (M : Matrix {v : V // v ≠ r} {v : V // v ≠ r} ℝ)
    (i j : V) :
    (zeroInsertion r * M * groundRestriction r) i j =
      if hi : i = r then 0 else if hj : j = r then 0 else M ⟨i, hi⟩ ⟨j, hj⟩ := by
  have h : (zeroInsertion r * M * groundRestriction r) i j =
      (zeroInsertion r *ᵥ (M *ᵥ (groundRestriction r *ᵥ Pi.single j 1))) i := by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_single_one]
    rfl
  rw [h]
  by_cases hi : i = r
  · subst i
    simp
  · by_cases hj : j = r
    · subst j
      rw [restriction_root_single, mulVec_zero, mulVec_zero]
      simp [hi]
    · have hg := restriction_single r (⟨j, hj⟩ : {v : V // v ≠ r})
      rw [hg, mulVec_single_one, zeroInsertion_mulVec_apply]
      simp only [dite_eq_right hi, dite_eq_right hj]
      rfl

/-- **The one-neighbor matrix factorization.**

Let A be a real matrix on a finite set V, r ∈ V, and u ∈ I = V ∖ {r}. Put p = Aᵣᵣ and c = Aᵣᵤ.
Assume A is symmetric, Aᵣⱼ = 0 outside {r,u}, and p > 0. Put l = √p eᵣ + (c/√p)eᵤ and S = A|I
− (c²/p)eᵤeᵤᵀ. For zero insertion J and coordinate restriction C, one has A = l lᵀ + J S C.
-/
theorem degreeOnePivot_factor (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → A r j = 0) (hp : 0 < A r r) :
    A = vecMulVec (degreeOneColumn A r u) (degreeOneColumn A r u) +
      zeroInsertion r * degreeOnePivot A r u * groundRestriction r := by
  let s := Real.sqrt (A r r)
  have hs0 : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hs2 : s ^ 2 = A r r := Real.sq_sqrt hp.le
  have hcross : s * (A r u.val / s) = A r u.val := by
    field_simp [hs0]
  have hratio : (A r u.val / s) ^ 2 = (A r u.val) ^ 2 / A r r := by
    rw [div_pow, ← hs2]
  ext i j
  rw [Matrix.add_apply, vecMulVec_apply, embedding_apply]
  simp only [degreeOneColumn, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change A i j =
    (s * (Pi.single r 1 : V → ℝ) i + (A r u.val / s) * (Pi.single u.val 1 : V → ℝ) i) *
      (s * (Pi.single r 1 : V → ℝ) j + (A r u.val / s) * (Pi.single u.val 1 : V → ℝ) j) +
      (if hi : i = r then 0 else if hj : j = r then 0 else degreeOnePivot A r u ⟨i, hi⟩ ⟨j, hj⟩)
  by_cases hir : i = r
  · subst i
    by_cases hjr : j = r
    · subst j
      simpa [Ne.symm u.property, pow_two] using hs2.symm
    · by_cases hju : j = u.val
      · subst j
        simpa [Ne.symm u.property, u.property] using hcross.symm
      · simp [hjr, hju, Ne.symm u.property, hs j hjr hju]
  · by_cases hjr : j = r
    · subst j
      have hh : A i r = A r i := by simpa only [star_trivial] using hA.apply r i
      rw [hh]
      by_cases hiu : i = u.val
      · subst i
        simpa [Ne.symm u.property, u.property, mul_comm] using hcross.symm
      · simp [hir, hiu, Ne.symm u.property, hs i hir hiu]
    · rw [dite_eq_right hir, dite_eq_right hjr, pivot_rank]
      simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, vecMulVec_apply,
        smul_eq_mul, Pi.single_apply, Subtype.ext_iff, ite_eq_right hir, ite_eq_right hjr,
        mul_zero, zero_add]
      have h := congrArg (fun t : ℝ => t * (if i = u.val then 1 else 0) *
        (if j = u.val then 1 else 0)) hratio
      linear_combination -h

/-- **Support of the one-neighbor factor column.**

Let A be a real matrix on a finite set V, r ∈ V, and u ∈ I = V ∖ {r}. Put p = Aᵣᵣ and c = Aᵣᵤ.
For l = √p eᵣ + (c/√p)eᵤ, the number of coordinates i with lᵢ ≠ 0 is at most two.
-/
theorem degreeOneColumn_support_card :
    ((univ : Finset V).filter fun i => degreeOneColumn A r u i ≠ 0).card ≤ 2 := by
  have hsub : (univ : Finset V).filter (fun i => degreeOneColumn A r u i ≠ 0) ⊆ {r, u.val} := by
    intro i hi
    by_contra h
    have hir : i ≠ r := by simpa using (not_or.mp (by simpa using h)).1
    have hiu : i ≠ u.val := by simpa using (not_or.mp (by simpa using h)).2
    exact (mem_filter.mp hi).2 (degreeOneColumn_eq_zero A r u hir hiu)
  exact (card_le_card hsub).trans (by simp [Ne.symm u.property])

end Matrix
