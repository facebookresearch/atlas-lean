/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.Factorizations.TwoLevel
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

namespace MathlibExtTest.LinearAlgebra.Matrix.Factorizations.TwoLevel

/-- A permutation matrix is unitary. -/
private theorem permMatrix_mem_unitaryGroup (σ : Equiv.Perm (Fin 3)) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- A three-cycle permutation matrix is a product of two two-level
unitaries. -/
theorem three_cycle_twoLevel :
    ∃ L : List (Matrix (Fin 3) (Fin 3) ℂ),
      L.length = 2 ∧
      (∀ M ∈ L, M ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
        ∃ i j, M.IsTwoLevel i j) ∧
      L.prod =
        Equiv.Perm.permMatrix ℂ
          (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) := by
  refine ⟨[Equiv.Perm.permMatrix ℂ (Equiv.swap (1 : Fin 3) 2),
    Equiv.Perm.permMatrix ℂ (Equiv.swap (0 : Fin 3) 1)],
    by decide, ?_, ?_⟩
  · intro M hM
    simp at hM
    have h3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    cases hM with
    | inl hEq =>
      subst hEq
      constructor
      · exact permMatrix_mem_unitaryGroup _
      · refine ⟨1, 2, ?_⟩
        unfold Matrix.IsTwoLevel
        refine ⟨by decide, fun k l h => ?_⟩
        rcases h3 k with rfl | rfl | rfl <;>
          rcases h3 l with rfl | rfl | rfl <;>
          simp_all [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
            Equiv.toPEquiv_apply, Option.mem_def] <;> decide
    | inr hEq =>
      subst hEq
      constructor
      · exact permMatrix_mem_unitaryGroup _
      · refine ⟨0, 1, ?_⟩
        unfold Matrix.IsTwoLevel
        refine ⟨by decide, fun k l h => ?_⟩
        rcases h3 k with rfl | rfl | rfl <;>
          rcases h3 l with rfl | rfl | rfl <;>
          simp_all [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
            Equiv.toPEquiv_apply, Option.mem_def] <;> decide
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    rw [Matrix.permMatrix_mul]

/-- The exact adjacent-factor count cannot work in dimension one without a
diagonal phase. -/
theorem not_exists_twoLevel_prod_neg_one_fin_one :
    ¬ ∃ L : List (Matrix (Fin 1) (Fin 1) ℂ),
      L.length = 1 * (1 - 1) / 2 ∧ L.prod = -1 := by
  intro h
  obtain ⟨L, hlen, hprod⟩ := h
  have h0 : 1 * (1 - 1) / 2 = 0 := by decide
  rw [h0] at hlen
  cases L with
  | nil =>
    simp at hprod
    have h1 : (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 =
        (-1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 :=
      congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) hprod
    simp at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  | cons hd tl =>
    have hne : (hd :: tl).length ≠ 0 := by simp
    exact absurd hlen hne

/-- In dimension one, the diagonal-phase form gives `[-1]` with no factors. -/
theorem neg_one_twoLevel_diagonal_fin_one :
    ∃ (L : List (Matrix (Fin 1) (Fin 1) ℂ)) (φ : Fin 1 → ℂ),
      L.length ≤ 1 * (1 - 1) / 2 ∧
      (∀ M ∈ L, M ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧
        ∃ i j, M.IsTwoLevel i j) ∧
      (∀ k, ‖φ k‖ = 1) ∧
      L.prod * Matrix.diagonal φ = (-1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  refine ⟨[], fun _ => -1, by decide, by simp, ?_, ?_⟩
  · intro k
    simp
  · simp
    ext i j
    have h1 : ∀ i : Fin 1, i = 0 := by decide
    have hi := h1 i
    have hj := h1 j
    subst hi
    subst hj
    simp

/-- Every two-dimensional unitary is itself two-level on the only pair. -/
theorem isTwoLevel_zero_one_fin_two
    {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    U.IsTwoLevel 0 1 := by
  unfold Matrix.IsTwoLevel
  refine ⟨by decide, fun k l h => ?_⟩
  have h2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  cases h2 k with
  | inl hk0 =>
    cases h2 l with
    | inl hl0 =>
      subst hk0
      subst hl0
      exact absurd h (by decide)
    | inr hl1 =>
      subst hk0
      subst hl1
      exact absurd h (by decide)
  | inr hk1 =>
    cases h2 l with
    | inl hl0 =>
      subst hk1
      subst hl0
      exact absurd h (by decide)
    | inr hl1 =>
      subst hk1
      subst hl1
      exact absurd h (by decide)

#print axioms Matrix.exists_unitary_fin_two_mulVec_eq
#print axioms Matrix.exists_twoLevel_prod_eq
#print axioms Matrix.exists_twoLevel_prod_mul_diagonal_eq

end MathlibExtTest.LinearAlgebra.Matrix.Factorizations.TwoLevel
