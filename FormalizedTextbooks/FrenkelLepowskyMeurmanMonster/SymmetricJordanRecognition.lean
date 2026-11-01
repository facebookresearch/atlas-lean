/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Orthogonal-conjugation recognition from the proved projector and Peirce arguments. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SymmetricJordanConjugation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every real symmetric Jordan automorphism preserving the Frobenius pairing is
conjugation by an actual orthogonal matrix. Unit preservation follows from this conclusion. -/
theorem sym24Jordan_orthogonal_conjugation (φ : Sym24 ≃ₗ[ℝ] Sym24)
    (hJ : ∀ A B, φ (sym24Jordan A B) = sym24Jordan (φ A) (φ B))
    (hT : ∀ A B, Matrix.trace ((φ A).val * (φ B).val) = Matrix.trace (A.val * B.val)) :
    ∃ R : Matrix (Fin 24) (Fin 24) ℝ, R.transpose * R = 1 ∧ R * R.transpose = 1 ∧
      ∀ A : Sym24, (φ A).val = R * A.val * R.transpose := by
  obtain ⟨O, hL, hR, hDiag⟩ := sym24Jordan_diagonalUnit_images_orthogonal φ hJ hT
  let C := sym24ConjugationEquiv O hL hR
  let ψ : Sym24 ≃ₗ[ℝ] Sym24 := φ.trans C.symm
  have hψJ : ∀ A B, ψ (sym24Jordan A B) = sym24Jordan (ψ A) (ψ B) := by
    intro A B
    change C.symm (φ (sym24Jordan A B)) = sym24Jordan (C.symm (φ A)) (C.symm (φ B))
    rw [hJ]
    change sym24ConjugationLinear O.transpose (sym24Jordan (φ A) (φ B)) =
      sym24Jordan (sym24ConjugationLinear O.transpose (φ A))
        (sym24ConjugationLinear O.transpose (φ B))
    exact sym24Conjugation_jordan O.transpose
      (by simpa only [Matrix.transpose_transpose] using hR) _ _
  have hψD : ∀ i, ψ (sym24DiagonalUnit i) = sym24DiagonalUnit i := by
    intro i
    have hh : φ (sym24DiagonalUnit i) = C (sym24DiagonalUnit i) :=
      Subtype.ext (hDiag i)
    change C.symm (φ (sym24DiagonalUnit i)) = sym24DiagonalUnit i
    rw [hh, LinearEquiv.symm_apply_apply]
  obtain ⟨ε, hε, hψ⟩ := sym24Jordan_fixed_diagonal_conjugation ψ hψJ hψD
  let D : Matrix (Fin 24) (Fin 24) ℝ := Matrix.diagonal ε
  have hDt : D.transpose = D := by simp [D]
  have hDD : D * D = 1 := by
    change Matrix.diagonal ε * Matrix.diagonal ε = 1
    rw [Matrix.diagonal_mul_diagonal]
    have he : (fun i => ε i * ε i) = (fun _ : Fin 24 => (1 : ℝ)) := by
      funext i
      simpa only [pow_two] using hε i
    rw [he, Matrix.diagonal_one]
  have hRL : (O * D).transpose * (O * D) = 1 := by
    calc
      _ = D.transpose * (O.transpose * O) * D := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = 1 := by rw [hL, hDt, mul_one, hDD]
  refine ⟨O * D, hRL, mul_eq_one_comm.mp hRL, ?_⟩
  intro A
  have hm : C (ψ A) = φ A := by
    change C (C.symm (φ A)) = φ A
    exact LinearEquiv.apply_symm_apply C (φ A)
  calc
    (φ A).val = (C (ψ A)).val := congrArg Subtype.val hm.symm
    _ = O * (D * A.val * D.transpose) * O.transpose := by
      change O * (ψ A).val * O.transpose = _
      rw [hψ A]
    _ = (O * D) * A.val * (O * D).transpose := by
      rw [Matrix.transpose_mul]
      noncomm_ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
