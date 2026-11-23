/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Algebra.Order.Star.Real

/-!
# Strict positivity of the Schur complement

For a real block matrix `G = [[A, B], [Bᵀ, D]]` that is positive
definite in Mathlib's strict sense (`Matrix.PosDef`), the interior
block `D` and the exterior block `A` are positive definite; the
interior block is invertible, with invertibility derived from the
hypotheses rather than assumed; and the Schur complement
`K = A - B * D⁻¹ * Bᵀ` is Hermitian, positive semidefinite and in
fact positive definite. With an empty interior index type the Schur
complement is `A` itself, and the scalar `Fin 1` case is recorded.
-/

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity

/-- The Schur complement `K = A - B * D⁻¹ * Bᵀ` of the interior block
`D`. Meaningful as the leaf's `K` once `D` is invertible; invertibility
is derived, not assumed, in the lemmas below. -/
noncomputable def schurComplement {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) : Matrix m m ℝ :=
  A - B * D⁻¹ * Bᵀ

/-- The interior block of a positive-definite block matrix is itself
positive definite: `D` is the principal submatrix on the interior
indices. This is the first step in deriving invertibility. -/
theorem interior_posDef {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] {A : Matrix m m ℝ} {B : Matrix m p ℝ}
    {D : Matrix p p ℝ}
    (hG : (Matrix.fromBlocks A B Bᵀ D).PosDef) : D.PosDef := by
  have h : ((Matrix.fromBlocks A B Bᵀ D).submatrix Sum.inr Sum.inr).PosDef :=
    hG.submatrix Sum.inr_injective
  have heq : (Matrix.fromBlocks A B Bᵀ D).submatrix Sum.inr Sum.inr = D := by
    ext i j
    simp
  rwa [heq] at h

/-- The exterior block of a positive-definite block matrix is itself
positive definite, by the same principal-submatrix argument. -/
theorem exterior_posDef {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] {A : Matrix m m ℝ} {B : Matrix m p ℝ}
    {D : Matrix p p ℝ}
    (hG : (Matrix.fromBlocks A B Bᵀ D).PosDef) : A.PosDef := by
  have h : ((Matrix.fromBlocks A B Bᵀ D).submatrix Sum.inl Sum.inl).PosDef :=
    hG.submatrix Sum.inl_injective
  have heq : (Matrix.fromBlocks A B Bᵀ D).submatrix Sum.inl Sum.inl = A := by
    ext i j
    simp
  rwa [heq] at h

/-- Derived invertibility, determinant form: the interior determinant
is a unit (in fact nonzero) because `D` is positive definite. The leaf
requires this to be derived from `hG`, never assumed. -/
theorem interior_isUnit_det {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] {A : Matrix m m ℝ} {B : Matrix m p ℝ}
    {D : Matrix p p ℝ}
    (hG : (Matrix.fromBlocks A B Bᵀ D).PosDef) : IsUnit D.det := by
  have hD : D.PosDef := interior_posDef hG
  have hpos : 0 < D.det := hD.det_pos
  exact isUnit_iff_ne_zero.mpr (ne_of_gt hpos)

/-- Derived invertibility, matrix form: `D` is a unit in the matrix
ring. This is the hypothesis shape that block-elimination results
(such as the sibling elimination leaf) consume as `Invertible D`. -/
theorem interior_isUnit {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] {A : Matrix m m ℝ} {B : Matrix m p ℝ}
    {D : Matrix p p ℝ}
    (hG : (Matrix.fromBlocks A B Bᵀ D).PosDef) : IsUnit D := by
  exact (interior_posDef hG).isUnit

/-- The Schur complement of a positive-definite block matrix is
Hermitian (symmetric over `ℝ`). Proved from the Hermitian transfer
for block matrices once the derived invertibility of `D` is in hand;
stated separately because the strict-positivity argument needs the
Hermitian half of `PosDef` independently of the PSD criterion. -/
theorem schurComplement_isHermitian {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] {A : Matrix m m ℝ} {B : Matrix m p ℝ}
    {D : Matrix p p ℝ}
    (hG : (Matrix.fromBlocks A B Bᵀ D).PosDef) :
    (schurComplement A B D).IsHermitian := by
  have hD : D.PosDef := interior_posDef hG
  letI := (interior_isUnit hG).invertible
  have h := (Matrix.IsHermitian.fromBlocks₂₂ A B hD.isHermitian).mp ?_
  · simpa [schurComplement] using h
  · simpa using hG.isHermitian

/-- Intermediate only: the Schur complement is positive semidefinite.
This is what Mathlib's PSD Schur criterion
(`Matrix.PosDef.fromBlocks₂₂`) yields after deriving `D.PosDef`
and `Invertible D`. The leaf explicitly warns that this alone is not
the strict conclusion; `schurComplement_posDef` below is strictly
stronger and is the headline. -/
theorem schurComplement_posSemidef {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] {A : Matrix m m ℝ} {B : Matrix m p ℝ}
    {D : Matrix p p ℝ}
    (hG : (Matrix.fromBlocks A B Bᵀ D).PosDef) :
    (schurComplement A B D).PosSemidef := by
  have hD : D.PosDef := interior_posDef hG
  letI := (interior_isUnit hG).invertible
  have h := (Matrix.PosDef.fromBlocks₂₂ A B hD).mp ?_
  · simpa [schurComplement] using h
  · simpa using hG.posSemidef

/-- Headline result of the leaf: for a real positive-definite block
matrix `G = [[A, B], [Bᵀ, D]]`, the Schur matrix
`K = A - B D⁻¹ Bᵀ` is positive definite (strict), with the
invertibility of `D` derived from `hG` by the lemmas above. The proof
must transfer strict positivity from the full quadratic form (via the
Schur quadratic-form identity), not merely cite the PSD criterion. -/
theorem schurComplement_posDef {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] {A : Matrix m m ℝ} {B : Matrix m p ℝ}
    {D : Matrix p p ℝ}
    (hG : (Matrix.fromBlocks A B Bᵀ D).PosDef) :
    (schurComplement A B D).PosDef := by
  have hD : D.PosDef := interior_posDef hG
  letI := (interior_isUnit hG).invertible
  have hBH : Bᴴ = Bᵀ := Matrix.conjTranspose_eq_transpose_of_trivial B
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (schurComplement_isHermitian hG)
    fun x hx => ?_
  have hne : x ⊕ᵥ -((D⁻¹ * Bᴴ) *ᵥ x) ≠ 0 := by
    intro hcon
    apply hx
    ext i
    have hci := congrFun hcon (Sum.inl i)
    simpa using hci
  have hpos := hG.dotProduct_mulVec_pos (x := x ⊕ᵥ -((D⁻¹ * Bᴴ) *ᵥ x)) hne
  rw [Matrix.dotProduct_mulVec] at hpos
  have hid := Matrix.schur_complement_eq₂₂ A B x (-((D⁻¹ * Bᴴ) *ᵥ x)) hD.isHermitian
  rw [add_neg_cancel] at hid
  simp only [star_zero, Matrix.zero_vecMul, zero_dotProduct, zero_add] at hid
  simp only [hBH] at hpos hid
  rw [hid] at hpos
  simpa [schurComplement, ← Matrix.dotProduct_mulVec] using hpos

/-- Boundary case named by the leaf: with an empty interior index
type, the Schur complement reduces to the exterior block `A` itself
(there is nothing to eliminate). -/
theorem schurComplement_eq_of_isEmpty {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq p] [IsEmpty p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) : schurComplement A B D = A := by
  have hB : B = 0 := Matrix.ext fun i j => False.elim (IsEmpty.false j)
  simp [schurComplement, hB]

/-- Two-by-two SPD shape named by the leaf's validation: scalar blocks
on `Fin 1 ⊕ Fin 1`. For real scalars `a b d` with the `2 × 2` matrix
`[[a, b], [b, d]]` positive definite, the scalar Schur complement
`a - b * d⁻¹ * b` is strictly positive. This is the `Fin 1` instance
of `schurComplement_posDef`; the concrete numeric example belongs to
the test file, not to this pin. -/
theorem schurComplement_fin_one_posDef {a b d : ℝ}
    (hG : (Matrix.fromBlocks
      (Matrix.of fun _ _ => a : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => b : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => b : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => d : Matrix (Fin 1) (Fin 1) ℝ)).PosDef) :
    (schurComplement (Matrix.of fun _ _ => a : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => b : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => d : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
  have hBT : (Matrix.of fun _ _ => b : Matrix (Fin 1) (Fin 1) ℝ)ᵀ =
      Matrix.of fun _ _ => b := by
    ext i j
    rfl
  have hG' : (Matrix.fromBlocks
      (Matrix.of fun _ _ => a : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => b : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => b : Matrix (Fin 1) (Fin 1) ℝ)ᵀ
      (Matrix.of fun _ _ => d : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
    rwa [hBT]
  exact schurComplement_posDef hG'

end MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity
