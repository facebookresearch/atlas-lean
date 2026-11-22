/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.FiniteBijectionMatrix

/-!
# Ordered blocks of finite orthogonal coordinate matrices

These formulas preserve the source finite-bijection tensor and the original
ordered orthogonal matrix block sum. All maps use the original source-first
coordinate convention.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Matrix
open scoped MonoidalCategory

namespace CategoryTheory.Spectra

/-- The ordered sum of two finite-coordinate bijections, with their original left/right blocks. -/
abbrev finiteBijectionSum {m n p q : ℕ} (e : Fin m ≃ Fin n) (f : Fin p ≃ Fin q) :
    Fin (m + p) ≃ Fin (n + q) :=
  Operad.SmallFinBijGroupoid.finiteBijectionSum e f
theorem finiteBijectionSum_left {m n p q : ℕ} (e : Fin m ≃ Fin n) (f : Fin p ≃ Fin q)
    (i : Fin m) :
    finiteBijectionSum e f (Fin.castAdd p i) = Fin.castAdd q (e i) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.finiteBijectionSum_left e f i
theorem finiteBijectionSum_right {m n p q : ℕ} (e : Fin m ≃ Fin n) (f : Fin p ≃ Fin q)
    (i : Fin p) :
    finiteBijectionSum e f (Fin.natAdd m i) = Fin.natAdd n (f i) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.finiteBijectionSum_right e f i

/-- Ordered finite direct sum maps to the literal native ordered matrix block sum. -/
theorem finiteBijectionMatrix_blockSum {m n p q : ℕ}
    (e : Fin m ≃ Fin n) (f : Fin p ≃ Fin q) :
    OrthogonalMatrixHom.blockSum (finiteBijectionMatrix e) (finiteBijectionMatrix f) =
      finiteBijectionMatrix (finiteBijectionSum e f) := by
  apply OrthogonalMatrixHom.ext
  ext i j
  simp only [OrthogonalMatrixHom.blockSum, Matrix.reindex_apply, Matrix.submatrix_apply,
    finiteBijectionMatrix_apply]
  rcases finSumFinEquiv.surjective i with ⟨i, rfl⟩
  rcases finSumFinEquiv.surjective j with ⟨j, rfl⟩
  rcases i with i | i <;> rcases j with j | j
  · simp [finiteBijectionSum, Matrix.fromBlocks, finiteBijectionMatrix_apply]
  · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂,
      Matrix.zero_apply, finiteBijectionSum_right, right_eq_ite_iff, zero_ne_one, imp_false]
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  · simp only [finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_natAdd,
      finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₂₁,
      Matrix.zero_apply, finiteBijectionSum_left, right_eq_ite_iff, zero_ne_one, imp_false]
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  · simp [finiteBijectionSum, Matrix.fromBlocks, finiteBijectionMatrix_apply]

theorem smallFiniteBijection_tensor {A A' B B' : Operad.SmallFinBijGroupoid}
    (f : A ⟶ A') (g : B ⟶ B') :
    smallFiniteBijection (f ⊗ₘ g) =
      finiteBijectionSum (smallFiniteBijection f) (smallFiniteBijection g) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_tensor f g

/-- The original symmetric tensor morphism maps to the original orthogonal block sum. -/
theorem smallBijectionMatrix_tensor {A A' B B' : Operad.SmallFinBijGroupoid}
    (f : A ⟶ A') (g : B ⟶ B') :
    smallBijectionMatrix (f ⊗ₘ g) =
      OrthogonalMatrixHom.blockSum (smallBijectionMatrix f) (smallBijectionMatrix g) := by
  change finiteBijectionMatrix (smallFiniteBijection (f ⊗ₘ g)) =
    OrthogonalMatrixHom.blockSum (finiteBijectionMatrix (smallFiniteBijection f))
      (finiteBijectionMatrix (smallFiniteBijection g))
  rw [smallFiniteBijection_tensor]
  exact (finiteBijectionMatrix_blockSum (smallFiniteBijection f) (smallFiniteBijection g)).symm

/-- The full matrix constructor is continuous in the original finite discrete Hom topology. -/
theorem continuous_finiteBijectionMatrix (m n : ℕ) :
    letI : TopologicalSpace (Fin m ≃ Fin n) := ⊥
    Continuous (finiteBijectionMatrix : (Fin m ≃ Fin n) → OrthogonalMatrixHom m n) := by
  let _ : TopologicalSpace (Fin m ≃ Fin n) := ⊥
  let _ : DiscreteTopology (Fin m ≃ Fin n) := ⟨rfl⟩
  exact continuous_of_discreteTopology

/-- Joint evaluation uses the original continuous orthogonal matrix action. -/
theorem continuous_finiteBijectionEvaluation (m n : ℕ) :
    letI : TopologicalSpace (Fin m ≃ Fin n) := ⊥
    Continuous fun z : (Fin m ≃ Fin n) × EuclideanSpace ℝ (Fin m) =>
      (finiteBijectionMatrix z.1).1 *ᵥ z.2 := by
  let _ : TopologicalSpace (Fin m ≃ Fin n) := ⊥
  exact OrthogonalMatrixHom.continuous_evaluation.comp
    ((continuous_finiteBijectionMatrix m n).comp continuous_fst |>.prodMk continuous_snd)

end CategoryTheory.Spectra
