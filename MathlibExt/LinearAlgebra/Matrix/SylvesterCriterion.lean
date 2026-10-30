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
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sylvester's criterion for positive definite matrices

A Hermitian real matrix is positive definite if and only if all of its
leading principal minors are positive. Mathlib has the law of inertia
(`MathlibExt.LinearAlgebra.Matrix.SylvesterInertia`, congruent symmetric
matrices share the same numbers of positive, negative, and zero
eigenvalues) and the LU decomposition from nonvanishing leading principal
minors (`MathlibExt.LinearAlgebra.Matrix.LUDecomposition`), but no
statement connecting positivity of the leading principal minors to
positive definiteness.

The proof inducts on the size. In the step, the leading `n × n` block is
positive definite by the induction hypothesis, so the Schur complement
`D - uᴴ * B⁻¹ * u` is a `1 × 1` matrix whose determinant is positive
because `det A = det B * det (Schur complement)` and `det B > 0`; the
Schur-complement quadratic-form identity
(`Matrix.schur_complement_eq₁₁`) then shows the whole matrix is positive
definite. The induction step reindexes `Fin (n + 1)` as `Fin n ⊕ Fin 1`,
following the template of `LUDecomposition.lean`.
-/

@[expose] public section

namespace Matrix

/-- The leading `k × k` principal submatrix of `A`: the submatrix on the
first `k` rows and columns. -/
def leadingPrincipalSubmatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (hk : k ≤ n) : Matrix (Fin k) (Fin k) ℝ :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

/-- The full leading principal submatrix is the matrix itself. -/
theorem leadingPrincipalSubmatrix_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    leadingPrincipalSubmatrix A n (Nat.le_refl n) = A := by
  ext i j
  simp [leadingPrincipalSubmatrix, Matrix.submatrix_apply]

/-- The leading `k × k` submatrix of the leading `n × n` block of a
`(n + 1) × (n + 1)` matrix is the leading `k × k` submatrix of the whole
matrix. -/
private theorem leadingPrincipalSubmatrix_castSucc {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ) (hk : k ≤ n) :
    leadingPrincipalSubmatrix (A.submatrix Fin.castSucc Fin.castSucc) k hk =
      leadingPrincipalSubmatrix A k (Nat.le_trans hk (Nat.le_succ n)) := by
  ext i j
  simp [leadingPrincipalSubmatrix, Matrix.submatrix_apply]

/-- A `1 × 1` Hermitian matrix with a positive entry is positive definite. -/
private theorem posDef_fin_one {S : Matrix (Fin 1) (Fin 1) ℝ}
    (hS : S.IsHermitian) (h : 0 < S 0 0) : S.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos hS fun x hx => ?_
  have hx0 : x 0 ≠ 0 := by
    intro h0
    apply hx
    funext i
    fin_cases i; simp [h0]
  have hform : star x ⬝ᵥ S *ᵥ x = S 0 0 * (x 0 * x 0) := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Pi.star_apply, star_trivial]
    ring
  rw [hform]
  exact mul_pos h (mul_self_pos.mpr hx0)

/-- A block matrix with a positive definite top-left block and a positive
definite Schur complement is positive definite. This is the one-step
induction step of Sylvester's criterion, stated for a `1 × 1`
bottom-right block. -/
theorem PosDef.fromBlocks {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {u : Matrix (Fin n) (Fin 1) ℝ} {D : Matrix (Fin 1) (Fin 1) ℝ}
    (hB : B.PosDef) (hD : D.IsHermitian)
    (hS : (D - uᴴ * B⁻¹ * u).PosDef) :
    (Matrix.fromBlocks B u uᴴ D).PosDef := by
  let _ := hB.isUnit.invertible
  refine PosDef.of_dotProduct_mulVec_pos (IsHermitian.fromBlocks hB.isHermitian rfl hD)
    fun x hx => ?_
  have hx' : x = Sum.elim (fun i => x (Sum.inl i)) (fun j => x (Sum.inr j)) := by
    funext i
    cases i <;> rfl
  rw [hx', Matrix.dotProduct_mulVec,
    Matrix.schur_complement_eq₁₁ u D _ _ hB.isHermitian]
  set y := fun i => x (Sum.inl i) with hy
  set z := fun j => x (Sum.inr j) with hz
  set w := y + (B⁻¹ * u) *ᵥ z with hw
  have h1 : 0 ≤ (star w) ᵥ* B ⬝ᵥ w := by
    rw [← Matrix.dotProduct_mulVec]
    exact hB.posSemidef.dotProduct_mulVec_nonneg w
  have h2 : 0 ≤ (star z) ᵥ* (D - uᴴ * B⁻¹ * u) ⬝ᵥ z := by
    rw [← Matrix.dotProduct_mulVec]
    exact hS.posSemidef.dotProduct_mulVec_nonneg z
  by_cases hz0 : z = 0
  · have hy0 : y ≠ 0 := by
      intro hy0
      apply hx
      funext i
      cases i <;> simp [hx', hy0, hz0]
    have hw_eq : w = y := by simp [hw, hz0]
    have h1pos : 0 < (star w) ᵥ* B ⬝ᵥ w := by
      rw [hw_eq, ← Matrix.dotProduct_mulVec]
      exact hB.dotProduct_mulVec_pos hy0
    have h2eq : (star z) ᵥ* (D - uᴴ * B⁻¹ * u) ⬝ᵥ z = 0 := by simp [hz0]
    linarith
  · have h2pos : 0 < (star z) ᵥ* (D - uᴴ * B⁻¹ * u) ⬝ᵥ z := by
      rw [← Matrix.dotProduct_mulVec]
      exact hS.dotProduct_mulVec_pos hz0
    linarith

/-- Reindexing a `(n + 1) × (n + 1)` matrix as a block matrix over
`Fin n ⊕ Fin 1`: the top-left block is the leading `n × n` submatrix.
This is the reindexing lemma of `LUDecomposition.lean`, restated for
real matrices. -/
private theorem reindexed_topLeft {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm A).toBlocks₁₁ =
      A.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.of_apply,
    Matrix.submatrix_apply]
  change A (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) =
    A i.castSucc j.castSucc
  have hi : Fin.castAdd 1 i = i.castSucc := Fin.ext rfl
  have hj : Fin.castAdd 1 j = j.castSucc := Fin.ext rfl
  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left, hi, hj]

/-- **Sylvester's criterion**: a Hermitian real matrix is positive
definite if and only if all of its leading principal minors are
positive. The Hermitian hypothesis is essential: `!![1, 2; 0, 1]` has
leading minors `1` and `1` but is not Hermitian, hence not positive
definite. -/
theorem posDef_iff_leadingPrincipalMinors_pos :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsHermitian →
      (A.PosDef ↔ ∀ (k : ℕ) (hk : k ≤ n),
        0 < (leadingPrincipalSubmatrix A k hk).det) := by
  intro n
  induction n with
  | zero =>
      intro A hA
      constructor
      · intro hPos k hk
        obtain rfl : k = 0 := Nat.le_zero.mp hk
        simp [leadingPrincipalSubmatrix, Matrix.det_fin_zero]
      · intro _
        refine PosDef.of_dotProduct_mulVec_pos hA fun x hx => ?_
        exact absurd (funext fun i => Fin.elim0 i) hx
  | succ n ih =>
      intro A hA
      constructor
      · intro hPos k hk
        exact (hPos.submatrix (Fin.castLE_injective hk)).det_pos
      · intro h
        let B := A.submatrix Fin.castSucc Fin.castSucc
        have hBherm : B.IsHermitian := hA.submatrix _
        have hBminors : ∀ (k : ℕ) (hk : k ≤ n),
            0 < (leadingPrincipalSubmatrix B k hk).det := by
          intro k hk
          have hAk := h k (Nat.le_trans hk (Nat.le_succ n))
          rw [← leadingPrincipalSubmatrix_castSucc A k hk] at hAk
          exact hAk
        have hB : B.PosDef := (ih B hBherm).mpr hBminors
        set A' := Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm A with hA'def
        have htop : A'.toBlocks₁₁ = B := by
          rw [hA'def]
          exact reindexed_topLeft A
        have hA'det : A'.det = A.det := Matrix.det_reindex_self finSumFinEquiv.symm A
        have hA'herm : A'.IsHermitian := by
          rw [hA'def, Matrix.reindex_apply]
          exact (Matrix.isHermitian_submatrix_equiv finSumFinEquiv).mpr hA
        have hA'herm' : (Matrix.fromBlocks A'.toBlocks₁₁ A'.toBlocks₁₂ A'.toBlocks₂₁
            A'.toBlocks₂₂).IsHermitian := by
          rw [Matrix.fromBlocks_toBlocks]
          exact hA'herm
        obtain ⟨-, hBC, -, hDherm⟩ := Matrix.isHermitian_fromBlocks_iff.mp hA'herm'
        set u := A'.toBlocks₁₂ with hu
        set D := A'.toBlocks₂₂ with hDdef
        have hblocks : Matrix.fromBlocks B u uᴴ D = A' := by
          rw [← Matrix.fromBlocks_toBlocks A', htop, hBC]
        let _ := hB.isUnit.invertible
        let S := D - uᴴ * B⁻¹ * u
        have hSherm : S.IsHermitian :=
          hDherm.sub (Matrix.isHermitian_conjTranspose_mul_mul u hB.isHermitian.inv)
        have hdetS : 0 < S.det := by
          have hdetA : 0 < A.det := by
            have hAn := h (n + 1) (Nat.le_refl (n + 1))
            rwa [leadingPrincipalSubmatrix_self] at hAn
          have hdetB : 0 < B.det := hB.det_pos
          have hfactor : A.det = B.det * S.det := by
            rw [← hA'det, ← hblocks, Matrix.det_fromBlocks₁₁,
              Matrix.invOf_eq_nonsing_inv]
          rw [hfactor] at hdetA
          exact (mul_pos_iff_of_pos_left hdetB).mp hdetA
        have hS : S.PosDef := posDef_fin_one hSherm (by rwa [Matrix.det_fin_one] at hdetS)
        have hA'pos : A'.PosDef := by
          rw [← hblocks]
          exact PosDef.fromBlocks hB hDherm hS
        have hback : A = A'.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
          ext i j
          simp only [hA'def, Matrix.reindex_apply, Matrix.submatrix_apply,
            Equiv.symm_symm, Equiv.apply_symm_apply]
        rw [hback]
        exact hA'pos.submatrix (Equiv.injective finSumFinEquiv.symm)

end Matrix
