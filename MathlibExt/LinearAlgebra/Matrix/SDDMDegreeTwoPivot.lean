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
# Eliminating a vertex with two neighbors

Let A be a real matrix on a finite set V, r ∈ V and u,v ∈ I = V ∖ {r}. Put p = Aᵣᵣ, c = Aᵣᵤ
and d = Aᵣᵥ. When u ≠ v, write w = c eᵤ + d eᵥ. The retained matrix is S = A|I − p⁻¹ w wᵀ,
forward substitution gives b′ = b|I − (bᵣ/p)w, and back substitution restores xᵣ = (bᵣ − c zᵤ
− d zᵥ)/p. For a positive definite symmetric matrix with nonpositive off-diagonal entries and
nonnegative row sums, elimination preserves those properties when r has no other neighbors.

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

/-- **The retained matrix for two-neighbor elimination.**

For a real matrix A on V, r ∈ V and u,v ∈ I = V ∖ {r}, put p = Aᵣᵣ, c = Aᵣᵤ and d = Aᵣᵥ.
Define Sᵢⱼ by subtracting c²/p when i = j = u, otherwise d²/p when i = j = v, otherwise cd/p
when (i,j) is (u,v) or (v,u), and otherwise zero, from Aᵢⱼ. This ordered definition applies
also to u = v or p = 0.
-/
def degreeTwoPivot (A : Matrix V V ℝ) (r : V) (u v : {i : V // i ≠ r}) :
    Matrix {i : V // i ≠ r} {i : V // i ≠ r} ℝ :=
  fun i j => A i.val j.val -
    if i = u ∧ j = u then (A r u.val) ^ 2 / A r r
    else if i = v ∧ j = v then (A r v.val) ^ 2 / A r r
    else if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then A r u.val * A r v.val / A r r
    else 0

/-- **Forward substitution at two neighbors.**

For a real matrix A on V, r ∈ V, u,v ∈ I = V ∖ {r}, p = Aᵣᵣ, c = Aᵣᵤ and d = Aᵣᵥ, define b′ᵢ =
bᵢ − 1_{i=u} c bᵣ/p − 1_{i=v} d bᵣ/p. This is a linear map in b and uses both corrections even
when u = v.
-/
def degreeTwoRHS (A : Matrix V V ℝ) (r : V) (u v : {i : V // i ≠ r}) :
    (V → ℝ) →ₗ[ℝ] ({i : V // i ≠ r} → ℝ) where
  toFun b i := b i.val - (if i = u then A r u.val * b r / A r r else 0) -
    (if i = v then A r v.val * b r / A r r else 0)
  map_add' b c := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' k b := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- **Back substitution at two neighbors.**

For a real matrix A on V, r ∈ V, u,v ∈ I = V ∖ {r}, p = Aᵣᵣ, c = Aᵣᵤ and d = Aᵣᵥ, define
L(b,z)ᵣ = (bᵣ − c zᵤ − d zᵥ)/p and L(b,z)|I = z. The map is linear jointly in b and z and is
defined for all p.
-/
def degreeTwoLift (A : Matrix V V ℝ) (r : V) (u v : {i : V // i ≠ r}) :
    (V → ℝ) × ({i : V // i ≠ r} → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun bz i := if hi : i = r then
      (bz.1 r - A r u.val * bz.2 u - A r v.val * bz.2 v) / A r r
    else bz.2 ⟨i, hi⟩
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

/-- **The two-neighbor factor column.**

For a real matrix A on V, r ∈ V and u,v ∈ V ∖ {r}, put p = Aᵣᵣ, c = Aᵣᵤ and d = Aᵣᵥ. Define l
= √p eᵣ + (c/√p)eᵤ + (d/√p)eᵥ, using the real square root and real division.
-/
def degreeTwoColumn (A : Matrix V V ℝ) (r : V) (u v : {i : V // i ≠ r}) : V → ℝ :=
  Real.sqrt (A r r) • Pi.single r 1 +
    (A r u.val / Real.sqrt (A r r)) • Pi.single u.val 1 +
    (A r v.val / Real.sqrt (A r r)) • Pi.single v.val 1

variable (A : Matrix V V ℝ) (r : V) (u v : {i : V // i ≠ r})

@[simp]
theorem degreeTwoPivot_apply (i j : {i : V // i ≠ r}) :
    degreeTwoPivot A r u v i j = A i.val j.val -
      if i = u ∧ j = u then (A r u.val) ^ 2 / A r r
      else if i = v ∧ j = v then (A r v.val) ^ 2 / A r r
      else if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then A r u.val * A r v.val / A r r
      else 0 := rfl

@[simp]
theorem degreeTwoRHS_apply (b : V → ℝ) (i : {i : V // i ≠ r}) :
    degreeTwoRHS A r u v b i =
      b i.val - (if i = u then A r u.val * b r / A r r else 0) -
        (if i = v then A r v.val * b r / A r r else 0) := rfl

@[simp]
theorem degreeTwoLift_root (b : V → ℝ) (z : {i : V // i ≠ r} → ℝ) :
    degreeTwoLift A r u v (b, z) r =
      (b r - A r u.val * z u - A r v.val * z v) / A r r := by
  simp [degreeTwoLift]

@[simp]
theorem degreeTwoLift_retained (b : V → ℝ) (z : {i : V // i ≠ r} → ℝ)
    (i : {i : V // i ≠ r}) : degreeTwoLift A r u v (b, z) i.val = z i := by
  simp [degreeTwoLift, i.property]

theorem degreeTwoColumn_eq_zero {i : V} (hir : i ≠ r) (hiu : i ≠ u.val) (hiv : i ≠ v.val) :
    degreeTwoColumn A r u v i = 0 := by
  simp [degreeTwoColumn, hir, hiu, hiv]

private def coupling : {i : V // i ≠ r} → ℝ :=
  A r u.val • Pi.single u 1 + A r v.val • Pi.single v 1

private theorem coupling_apply (i : {i : V // i ≠ r}) :
    coupling A r u v i = (if i = u then A r u.val else 0) +
      (if i = v then A r v.val else 0) := by
  simp [coupling, Pi.single_apply]

private theorem row_restricted (hne : u ≠ v)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) :
    (fun i : {i : V // i ≠ r} => A r i.val) = coupling A r u v := by
  ext i
  by_cases hiu : i = u
  · subst i
    simp [coupling_apply, hne]
  · by_cases hiv : i = v
    · subst i
      simp [coupling_apply, Ne.symm hne]
    · have hiu' : i.val ≠ u.val := fun h => hiu (Subtype.ext h)
      have hiv' : i.val ≠ v.val := fun h => hiv (Subtype.ext h)
      simp [coupling_apply, hiu, hiv, hs i.val i.property hiu' hiv']

private theorem pivot_rank (hne : u ≠ v) : degreeTwoPivot A r u v =
    A.submatrix Subtype.val Subtype.val -
      (A r r)⁻¹ • vecMulVec (coupling A r u v) (coupling A r u v) := by
  ext i j
  by_cases hiu : i = u <;> by_cases hiv : i = v <;>
    by_cases hju : j = u <;> by_cases hjv : j = v <;>
    simp_all [degreeTwoPivot, coupling_apply, Matrix.sub_apply, Matrix.smul_apply,
      vecMulVec_apply, div_eq_mul_inv] <;> ring

/-- **Two-neighbor elimination as a rank-one correction.**

Let A be a real matrix on a finite set V, r ∈ V and u,v ∈ I = V ∖ {r}. Put p = Aᵣᵣ, c = Aᵣᵤ
and d = Aᵣᵥ. Assume u ≠ v and put w = c eᵤ + d eᵥ. The piecewise retained matrix S obtained by
subtracting c²/p at (u,u), d²/p at (v,v), and cd/p at the two cross entries satisfies S = A|I
− p⁻¹ w wᵀ.
-/
theorem degreeTwoPivot_eq_sub_rankOne (hne : u ≠ v) : degreeTwoPivot A r u v =
    A.submatrix Subtype.val Subtype.val -
      (A r r)⁻¹ • vecMulVec
        (A r u.val • Pi.single u 1 + A r v.val • Pi.single v 1)
        (A r u.val • Pi.single u 1 + A r v.val • Pi.single v 1) := by
  exact pivot_rank A r u v hne

private theorem rhs_sub (b : V → ℝ) : degreeTwoRHS A r u v b =
    (fun i => b i.val) - (b r / A r r) • coupling A r u v := by
  ext i
  change b i.val - (if i = u then A r u.val * b r / A r r else 0) -
    (if i = v then A r v.val * b r / A r r else 0) =
      b i.val - (b r / A r r) * coupling A r u v i
  rw [coupling_apply]
  split_ifs <;> ring

private def liftMatrix : Matrix V {i : V // i ≠ r} ℝ :=
  zeroInsertion r - (A r r)⁻¹ • vecMulVec (Pi.single r 1) (coupling A r u v)

variable [Fintype V]

private theorem coupling_dot (z : {i : V // i ≠ r} → ℝ) :
    coupling A r u v ⬝ᵥ z = A r u.val * z u + A r v.val * z v := by
  simp [coupling, add_dotProduct, smul_dotProduct]

private theorem lift_add (b : V → ℝ) (z : {i : V // i ≠ r} → ℝ) :
    degreeTwoLift A r u v (b, z) = zeroInsertion r *ᵥ z +
      ((b r - coupling A r u v ⬝ᵥ z) / A r r) • Pi.single r 1 := by
  ext i
  by_cases hi : i = r
  · subst i
    rw [degreeTwoLift_root]
    simp only [Pi.add_apply, zeroInsertion_mulVec_root]
    rw [coupling_dot]
    simp
    ring
  · simp [degreeTwoLift, zeroInsertion_mulVec_apply, hi]

private theorem principal_action (z : {i : V // i ≠ r} → ℝ) :
    groundRestriction r *ᵥ (A *ᵥ (zeroInsertion r *ᵥ z)) =
      A.submatrix Subtype.val Subtype.val *ᵥ z := by
  rw [mulVec_mulVec, mulVec_mulVec, groundRestriction_mul_mul_zeroInsertion]

private theorem pivot_row_action (hne : u ≠ v)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0)
    (z : {i : V // i ≠ r} → ℝ) :
    (A *ᵥ (zeroInsertion r *ᵥ z)) r = coupling A r u v ⬝ᵥ z := by
  rw [mulVec_mulVec, zeroInsertion_eq_submatrix_one]
  have hm := mul_submatrix_one (Equiv.refl V) (Subtype.val : {i : V // i ≠ r} → V) A
  simp only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] at hm
  rw [hm]
  change (fun i : {i : V // i ≠ r} => A r i.val) ⬝ᵥ z = coupling A r u v ⬝ᵥ z
  rw [row_restricted A r u v hne hs]

private theorem column_action (hne : u ≠ v) (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) :
    A *ᵥ Pi.single r 1 = A r r • Pi.single r 1 + zeroInsertion r *ᵥ coupling A r u v := by
  rw [mulVec_single_one]
  ext i
  have hh : A i r = A r i := by simpa only [star_trivial] using hA.apply r i
  change A i r = A r r * (Pi.single r 1 : V → ℝ) i +
    (zeroInsertion r *ᵥ coupling A r u v) i
  rw [hh]
  by_cases hi : i = r
  · subst i
    simp
  · have h := congrArg (fun x : {i : V // i ≠ r} → ℝ => x ⟨i, hi⟩)
      (row_restricted A r u v hne hs)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zeroInsertion_mulVec_apply,
      dite_eq_right hi, Pi.single_apply, ite_eq_right hi, mul_zero, zero_add] using h

private theorem action_split (hne : u ≠ v)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0)
    (z : {i : V // i ≠ r} → ℝ) :
    A *ᵥ (zeroInsertion r *ᵥ z) =
      zeroInsertion r *ᵥ (A.submatrix Subtype.val Subtype.val *ᵥ z) +
        (coupling A r u v ⬝ᵥ z) • Pi.single r 1 := by
  ext i
  by_cases hi : i = r
  · subst i
    rw [pivot_row_action A r u v hne hs z, Pi.add_apply, zeroInsertion_mulVec_root]
    simp
  · have h := congrArg (fun x : {i : V // i ≠ r} → ℝ => x ⟨i, hi⟩)
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

private theorem pivot_action (hne : u ≠ v) (z : {i : V // i ≠ r} → ℝ) :
    degreeTwoPivot A r u v *ᵥ z = A.submatrix Subtype.val Subtype.val *ᵥ z -
      ((coupling A r u v ⬝ᵥ z) / A r r) • coupling A r u v := by
  rw [pivot_rank A r u v hne, sub_mulVec, smul_mulVec, vecMulVec_mulVec]
  ext i
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- **Residual after two-neighbor back substitution.**

Let A be a real matrix on a finite set V, r ∈ V and u,v ∈ I = V ∖ {r}. Put p = Aᵣᵣ, c = Aᵣᵤ
and d = Aᵣᵥ. Assume u ≠ v, A is symmetric, Aᵣⱼ = 0 outside {r,u,v}, and p ≠ 0. Put w = c eᵤ +
d eᵥ, S = A|I − p⁻¹ w wᵀ and b′ = b|I − (bᵣ/p)w. For L(b,z)ᵣ = (bᵣ − c zᵤ − d zᵥ)/p and
L(b,z)|I = z, one has A L(b,z) − b = J(Sz − b′), where J inserts a zero at r.
-/
theorem degreeTwoLift_residual (hne : u ≠ v) (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) (hp : A r r ≠ 0)
    (b : V → ℝ) (z : {i : V // i ≠ r} → ℝ) :
    A *ᵥ degreeTwoLift A r u v (b, z) - b =
      zeroInsertion r *ᵥ (degreeTwoPivot A r u v *ᵥ z - degreeTwoRHS A r u v b) := by
  rw [lift_add, mulVec_add, mulVec_smul, action_split A r u v hne hs z,
    column_action A r u v hne hA hs]
  conv_lhs => rhs; rw [vector_split r b]
  simp only [pivot_action A r u v hne, rhs_sub, mulVec_sub, mulVec_smul]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hp]
  ring

/-- **Restriction of two-neighbor back substitution.**

Let A be a real matrix on a finite set V, r ∈ V and u,v ∈ I = V ∖ {r}. Put p = Aᵣᵣ, c = Aᵣᵤ
and d = Aᵣᵥ. For L(b,z)ᵣ = (bᵣ − c zᵤ − d zᵥ)/p and L(b,z)|I = z, coordinate restriction C
satisfies C L(b,z) = z. This holds for every b,z,u,v,p.
-/
theorem degreeTwoLift_restrict (b : V → ℝ) (z : {i : V // i ≠ r} → ℝ) :
    groundRestriction r *ᵥ degreeTwoLift A r u v (b, z) = z := by
  rw [groundRestriction_mulVec]
  ext i
  exact degreeTwoLift_retained A r u v b z i

private theorem liftMatrix_mulVec (z : {i : V // i ≠ r} → ℝ) :
    liftMatrix A r u v *ᵥ z = degreeTwoLift A r u v (0, z) := by
  rw [liftMatrix, sub_mulVec, smul_mulVec, vecMulVec_mulVec, lift_add]
  ext i
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, sub_eq_add_neg]

private theorem restriction_liftMatrix :
    groundRestriction r * liftMatrix A r u v = 1 := by
  apply ext_of_mulVec_single
  intro i
  rw [← mulVec_mulVec, liftMatrix_mulVec, degreeTwoLift_restrict, one_mulVec]

private theorem source_liftMatrix (hne : u ≠ v) (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) (hp : A r r ≠ 0) :
    A * liftMatrix A r u v = zeroInsertion r * degreeTwoPivot A r u v := by
  apply ext_of_mulVec_single
  intro i
  rw [← mulVec_mulVec, ← mulVec_mulVec, liftMatrix_mulVec]
  have h := degreeTwoLift_residual A r u v hne hA hs hp 0 (Pi.single i 1)
  simpa only [map_zero, sub_zero] using h

private theorem liftMatrix_congruence (hne : u ≠ v) (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) (hp : A r r ≠ 0) :
    (liftMatrix A r u v)ᴴ * A * liftMatrix A r u v = degreeTwoPivot A r u v := by
  have ht : (liftMatrix A r u v)ᵀ * zeroInsertion r = 1 := by
    have h := congrArg Matrix.transpose (restriction_liftMatrix A r u v)
    simpa only [transpose_mul, transpose_one, zeroInsertion] using h
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc,
    source_liftMatrix A r u v hne hA hs hp, ← Matrix.mul_assoc, ht, one_mul]

omit [Fintype V] in
private theorem pivot_posDef [Finite V] (hne : u ≠ v) (hA : A.PosDef)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) :
    (degreeTwoPivot A r u v).PosDef := by
  let := Fintype.ofFinite V
  have hinj : Function.Injective (liftMatrix A r u v).mulVec := by
    intro z w hzw
    have h := congrArg (fun x => groundRestriction r *ᵥ x) hzw
    simpa only [mulVec_mulVec, restriction_liftMatrix, one_mulVec] using h
  have h := hA.conjTranspose_mul_mul_same hinj
  rwa [liftMatrix_congruence A r u v hne hA.isHermitian hs (ne_of_gt hA.diag_pos)] at h

/-- **Energy of a two-neighbor lifted error.**

Let A be a real matrix on a finite set V, r ∈ V and u,v ∈ I = V ∖ {r}. Put p = Aᵣᵣ, c = Aᵣᵤ
and d = Aᵣᵥ. Assume u ≠ v, A is symmetric, Aᵣⱼ = 0 outside {r,u,v}, and p ≠ 0. Put S = A|I −
p⁻¹(c eᵤ + d eᵥ)(c eᵤ + d eᵥ)ᵀ. For e = L(b,z) − L(b,w), where L restores the root coordinate
by two-neighbor back substitution, one has eᵀ A e = (z − w)ᵀ S(z − w).
-/
theorem degreeTwoLift_error_energy (hne : u ≠ v) (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) (hp : A r r ≠ 0)
    (b : V → ℝ) (z w : {i : V // i ≠ r} → ℝ) :
    (degreeTwoLift A r u v (b, z) - degreeTwoLift A r u v (b, w)) ⬝ᵥ
        (A *ᵥ (degreeTwoLift A r u v (b, z) - degreeTwoLift A r u v (b, w))) =
      (z - w) ⬝ᵥ (degreeTwoPivot A r u v *ᵥ (z - w)) := by
  have hd : degreeTwoLift A r u v (b, z) - degreeTwoLift A r u v (b, w) =
      liftMatrix A r u v *ᵥ (z - w) := by
    rw [liftMatrix_mulVec, ← map_sub]
    simp only [Prod.mk_sub_mk, sub_self]
  rw [hd]
  calc
    (liftMatrix A r u v *ᵥ (z - w)) ⬝ᵥ (A *ᵥ (liftMatrix A r u v *ᵥ (z - w))) =
        (z - w) ⬝ᵥ ((liftMatrix A r u v)ᵀ *ᵥ (A *ᵥ (liftMatrix A r u v *ᵥ (z - w)))) := by
      exact (dotProduct_comm _ _).trans
        (by simpa only [transpose_transpose] using
          (dotProduct_transpose_mulVec (liftMatrix A r u v)ᵀ
            (A *ᵥ (liftMatrix A r u v *ᵥ (z - w))) (z - w)))
    _ = (z - w) ⬝ᵥ (((liftMatrix A r u v)ᴴ * A * liftMatrix A r u v) *ᵥ (z - w)) := by
      rw [conjTranspose_eq_transpose_of_trivial, mulVec_mulVec, mulVec_mulVec]
    _ = (z - w) ⬝ᵥ (degreeTwoPivot A r u v *ᵥ (z - w)) := by
      rw [liftMatrix_congruence A r u v hne hA hs hp]

private theorem sum_delete (f : V → ℝ) :
    (∑ i : {j : V // j ≠ r}, f i.val) = (∑ i, f i) - f r := by
  have h := Fintype.sum_eq_add_sum_subtype_ne f r
  linarith only [h]

private theorem coupling_sum :
    (∑ i, coupling A r u v i) = A r u.val + A r v.val := by
  simp [coupling, Finset.sum_add_distrib, Pi.single_apply]

omit [DecidableEq V] in
/-- **Row sum at a two-neighbor pivot.**

Let A be a real matrix on a finite set V, r ∈ V and u,v ∈ I = V ∖ {r}. Put p = Aᵣᵣ, c = Aᵣᵤ
and d = Aᵣᵥ. Assume u ≠ v and Aᵣⱼ = 0 outside {r,u,v}. Then ∑ⱼ Aᵣⱼ = p + c + d.
-/
theorem degreeTwoPivot_surplus (hne : u ≠ v)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) :
    (∑ j, A r j) = A r r + A r u.val + A r v.val := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => A r j) r]
  change A r r + (∑ i : {j : V // j ≠ r}, (fun i => A r i.val) i) =
    A r r + A r u.val + A r v.val
  rw [row_restricted A r u v hne hs, coupling_sum]
  ring

private theorem rowSum_internal (hne : u ≠ v) (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) (hp : A r r ≠ 0)
    (i : {j : V // j ≠ r}) :
    (∑ j, degreeTwoPivot A r u v i j) = (∑ j, A i.val j) -
      (coupling A r u v i / A r r) * ∑ j, A r j := by
  have hcol : A i.val r = coupling A r u v i := by
    have hh : A i.val r = A r i.val := by simpa only [star_trivial] using hA.apply r i.val
    exact hh.trans (congrArg (fun f : {j : V // j ≠ r} → ℝ => f i)
      (row_restricted A r u v hne hs))
  have hcorr : (∑ j, (A r r)⁻¹ * (coupling A r u v i * coupling A r u v j)) =
      (A r r)⁻¹ * coupling A r u v i * (A r u.val + A r v.val) := by
    simp only [← mul_assoc, ← Finset.mul_sum, coupling_sum]
  rw [pivot_rank A r u v hne]
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
    vecMulVec_apply, Finset.sum_sub_distrib]
  rw [hcorr, sum_delete r (fun j => A i.val j), hcol, degreeTwoPivot_surplus A r u v hne hs]
  field_simp [hp]
  ring

/-- **Retained row sums after two-neighbor elimination.**

Let A be a real matrix on a finite set V, r ∈ V and u,v ∈ I = V ∖ {r}. Put p = Aᵣᵣ, c = Aᵣᵤ
and d = Aᵣᵥ. Assume u ≠ v, A is symmetric, Aᵣⱼ = 0 outside {r,u,v}, and p ≠ 0. For S = A|I −
p⁻¹(c eᵤ + d eᵥ)(c eᵤ + d eᵥ)ᵀ and i ∈ I, one has ∑ⱼ∈I Sᵢⱼ = ∑ⱼ∈V Aᵢⱼ − (1_{i=u}c/p +
1_{i=v}d/p)∑ⱼ∈V Aᵣⱼ.
-/
theorem degreeTwoPivot_rowSum (hne : u ≠ v) (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) (hp : A r r ≠ 0)
    (i : {j : V // j ≠ r}) :
    (∑ j, degreeTwoPivot A r u v i j) = (∑ j, A i.val j) -
      (if i = u then A r u.val / A r r else 0) * (∑ j, A r j) -
      (if i = v then A r v.val / A r r else 0) * (∑ j, A r j) := by
  rw [rowSum_internal A r u v hne hA hs hp i, coupling_apply]
  split_ifs <;> ring

/-- **Preservation of diagonal dominance with two neighbors.**

Let A be a real matrix on a finite set V, r ∈ V and u,v ∈ I = V ∖ {r}. Put p = Aᵣᵣ, c = Aᵣᵤ
and d = Aᵣᵥ. Assume u ≠ v, A is positive definite, its off-diagonal entries are nonpositive,
its row sums are nonnegative, and Aᵣⱼ = 0 outside {r,u,v}. Then S = A|I − p⁻¹(c eᵤ + d eᵥ)(c
eᵤ + d eᵥ)ᵀ is positive definite, has nonpositive off-diagonal entries and has nonnegative row
sums.
-/
theorem degreeTwoPivot_preserves_sddm (hne : u ≠ v) (hA : A.PosDef)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hrows : ∀ i, 0 ≤ ∑ j, A i j)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) :
    (degreeTwoPivot A r u v).PosDef ∧
      (∀ i j, i ≠ j → degreeTwoPivot A r u v i j ≤ 0) ∧
      ∀ i, 0 ≤ ∑ j, degreeTwoPivot A r u v i j := by
  have hp : 0 < A r r := hA.diag_pos
  have hw (i : {j : V // j ≠ r}) : coupling A r u v i ≤ 0 := by
    have h := congrArg (fun f : {j : V // j ≠ r} → ℝ => f i)
      (row_restricted A r u v hne hs)
    rw [← h]
    exact hoff r i.val (Ne.symm i.property)
  refine ⟨pivot_posDef A r u v hne hA hs, ?_, ?_⟩
  · intro i j hij
    rw [pivot_rank A r u v hne]
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
      vecMulVec_apply]
    exact sub_nonpos.mpr (le_trans (hoff i.val j.val (fun h => hij (Subtype.ext h)))
      (mul_nonneg (inv_nonneg.mpr hp.le) (mul_nonneg_of_nonpos_of_nonpos (hw i) (hw j))))
  · intro i
    rw [rowSum_internal A r u v hne hA.isHermitian hs (ne_of_gt hp) i]
    exact sub_nonneg.mpr (le_trans
      (mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (hw i) hp.le) (hrows r))
      (hrows i.val))

private theorem zeroInsertion_single (j : {i : V // i ≠ r}) :
    zeroInsertion r *ᵥ (Pi.single j 1) = Pi.single j.val 1 := by
  ext i
  simp [zeroInsertion_eq_submatrix_one, mulVec_single, Matrix.one_apply, Pi.single_apply]

private theorem column_decomp : degreeTwoColumn A r u v =
    Real.sqrt (A r r) • Pi.single r 1 +
      (Real.sqrt (A r r))⁻¹ • (zeroInsertion r *ᵥ coupling A r u v) := by
  rw [coupling, mulVec_add, mulVec_smul, mulVec_smul, zeroInsertion_single, zeroInsertion_single]
  ext i
  simp only [degreeTwoColumn, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem restriction_root_single : groundRestriction r *ᵥ Pi.single r 1 = 0 := by
  rw [groundRestriction_mulVec]
  ext i
  simp [i.property]

private theorem restriction_single (j : {i : V // i ≠ r}) :
    groundRestriction r *ᵥ Pi.single j.val 1 = Pi.single j 1 := by
  rw [groundRestriction_mulVec]
  ext i
  simp [Pi.single_apply, Subtype.val_injective.eq_iff]

private theorem embedding_apply (M : Matrix {i : V // i ≠ r} {i : V // i ≠ r} ℝ)
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
    · have hg := restriction_single r (⟨j, hj⟩ : {i : V // i ≠ r})
      rw [hg, mulVec_single_one, zeroInsertion_mulVec_apply]
      simp only [dite_eq_right hi, dite_eq_right hj]
      rfl

/-- **The two-neighbor matrix factorization.**

Let A be a real matrix on a finite set V, r ∈ V and u,v ∈ I = V ∖ {r}. Put p = Aᵣᵣ, c = Aᵣᵤ
and d = Aᵣᵥ. Assume u ≠ v, A is symmetric, Aᵣⱼ = 0 outside {r,u,v}, and p > 0. Put l = √p eᵣ +
(c/√p)eᵤ + (d/√p)eᵥ and S = A|I − p⁻¹(c eᵤ + d eᵥ)(c eᵤ + d eᵥ)ᵀ. For zero insertion J and
restriction C, A = l lᵀ + J S C.
-/
theorem degreeTwoPivot_factor (hne : u ≠ v) (hA : A.IsHermitian)
    (hs : ∀ j, j ≠ r → j ≠ u.val → j ≠ v.val → A r j = 0) (hp : 0 < A r r) :
    A = vecMulVec (degreeTwoColumn A r u v) (degreeTwoColumn A r u v) +
      zeroInsertion r * degreeTwoPivot A r u v * groundRestriction r := by
  let s := Real.sqrt (A r r)
  have hs0 : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hs2 : s ^ 2 = A r r := Real.sq_sqrt hp.le
  have hratio : (s⁻¹) ^ 2 = (A r r)⁻¹ := by rw [← hs2, inv_pow]
  have hroot : degreeTwoColumn A r u v r = s := by
    rw [column_decomp]
    simp [s]
  have hret (i : V) (hi : i ≠ r) : degreeTwoColumn A r u v i =
      s⁻¹ * coupling A r u v ⟨i, hi⟩ := by
    rw [column_decomp]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      ite_eq_right hi, mul_zero, zero_add, zeroInsertion_mulVec_apply, dite_eq_right hi]
    rfl
  ext i j
  rw [Matrix.add_apply, vecMulVec_apply, embedding_apply]
  by_cases hir : i = r
  · subst i
    by_cases hjr : j = r
    · subst j
      simpa [hroot, pow_two] using hs2.symm
    · have hrow := congrArg (fun f : {i : V // i ≠ r} → ℝ => f ⟨j, hjr⟩)
        (row_restricted A r u v hne hs)
      rw [hroot, hret j hjr, dite_eq_left rfl, add_zero, hrow]
      field_simp [hs0]
  · by_cases hjr : j = r
    · subst j
      have hh : A i r = A r i := by simpa only [star_trivial] using hA.apply r i
      have hrow := congrArg (fun f : {i : V // i ≠ r} → ℝ => f ⟨i, hir⟩)
        (row_restricted A r u v hne hs)
      rw [hret i hir, hroot, dite_eq_right hir, dite_eq_left rfl, add_zero, hh, hrow]
      field_simp [hs0]
    · rw [hret i hir, hret j hjr, dite_eq_right hir, dite_eq_right hjr, pivot_rank A r u v hne]
      simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
        vecMulVec_apply]
      have h := congrArg (fun a : ℝ => a * coupling A r u v ⟨i, hir⟩ *
        coupling A r u v ⟨j, hjr⟩) hratio
      linear_combination -h

/-- **Support of the two-neighbor factor column.**

Let A be a real matrix on a finite set V, r ∈ V and u,v ∈ I = V ∖ {r}. Put p = Aᵣᵣ, c = Aᵣᵤ
and d = Aᵣᵥ. For l = √p eᵣ + (c/√p)eᵤ + (d/√p)eᵥ, the number of coordinates i with lᵢ ≠ 0 is
at most three.
-/
theorem degreeTwoColumn_support_card :
    ((univ : Finset V).filter fun i => degreeTwoColumn A r u v i ≠ 0).card ≤ 3 := by
  have hsub : (univ : Finset V).filter (fun i => degreeTwoColumn A r u v i ≠ 0) ⊆
      {r, u.val, v.val} := by
    intro i hi
    by_contra h
    have hout : i ≠ r ∧ i ≠ u.val ∧ i ≠ v.val := by simpa using h
    exact (mem_filter.mp hi).2 (degreeTwoColumn_eq_zero A r u v hout.1 hout.2.1 hout.2.2)
  have hcard : ({r, u.val, v.val} : Finset V).card ≤ 3 := by
    have h₁ := Finset.card_insert_le r ({u.val, v.val} : Finset V)
    have h₂ := Finset.card_insert_le u.val ({v.val} : Finset V)
    simpa using h₁.trans (Nat.add_le_add_right h₂ 1)
  exact (card_le_card hsub).trans hcard

end Matrix
