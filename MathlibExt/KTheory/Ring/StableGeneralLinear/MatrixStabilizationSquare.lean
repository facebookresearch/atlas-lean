/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.MatrixSuccessorEquiv

/-!
# Matrix stabilization square

For a finite index type `ι` and a semiring `R`, the flattening
`matrixGLMulEquiv n : GLₙ (Matrix ι ι R) ≃* GL_{n * card ι} R`
intertwines `GL` stabilization on the matrix-over-matrix side with block
stabilization on the flattened side.

This file proves that the stabilization square commutes, both pointwise
and as an equality of `MonoidHom` compositions:

```
GLₙ (Matrix ι ι R)  --stabilization-->  GL_{n+1} (Matrix ι ι R)
        |                                   |
  matrixGLMulEquiv n                  matrixGLMulEquiv (n+1)
        v                                   v
GL_{n*card ι} R  --matrixBlockStabilization-->  GL_{(n+1)*card ι} R
```

The vertical maps are the finite-level flattening equivalences; the
horizontal maps are ordinary `GeneralLinearGroup.stabilization` and
`matrixBlockStabilization`. The square underlies the identification of
`matrixFiniteGLDiagram` with `scaledBaseFiniteGLDiagram` in
`MatrixDiagram`.
-/

@[expose] public section

open Matrix

universe u

namespace AlgebraicKTheory
namespace MatrixDiagram

variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable {R : Type u} [Semiring R]

omit [DecidableEq ι] [Fintype ι] [Semiring R] in
private lemma comp_reindex_finSumEquiv (n : ℕ)
    (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (Matrix ι ι R)) :
    Matrix.comp (Fin (n + 1)) (Fin (n + 1)) ι ι R
        (Matrix.reindex (finSumFinEquiv (m := n) (n := 1))
          (finSumFinEquiv (m := n) (n := 1)) A) =
      Matrix.reindex (α := R)
        (finSumFinEquiv (m := n) (n := 1) |>.prodCongr (Equiv.refl ι))
        (finSumFinEquiv (m := n) (n := 1) |>.prodCongr (Equiv.refl ι))
        (Matrix.comp (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ι ι R A) := by
  ext ⟨_, _⟩ ⟨_, _⟩
  rfl

private lemma comp_blockDiagonalOne_sumProd (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (Matrix ι ι R)) :
    Matrix.comp (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ι ι R
        (fromBlocks (↑g : Matrix (Fin n) (Fin n) (Matrix ι ι R)) 0 0 1) =
      Matrix.reindex (α := R) (Equiv.sumProdDistrib (Fin n) (Fin 1) ι).symm
        (Equiv.sumProdDistrib (Fin n) (Fin 1) ι).symm
        (fromBlocks (Matrix.comp (Fin n) (Fin n) ι ι R (↑g)) 0 0 1) := by
  classical
  ext ⟨ab, k⟩ ⟨ab', k'⟩
  cases ab with
  | inl a =>
    cases ab' with
    | inl _ => rfl
    | inr _ => rfl
  | inr b =>
    cases ab' with
    | inl _ => rfl
    | inr b' =>
      by_cases hb : b = b'
      · subst hb
        by_cases hk : k = k'
        · subst hk
          simp
        · simp [hk]
      · simp [hb]

private lemma fromBlocks_reindex_prodEquiv (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (Matrix ι ι R)) :
    fromBlocks
        (Matrix.reindex (finProdMatrixEquiv (ι := ι) n) (finProdMatrixEquiv (ι := ι) n)
          (Matrix.comp (Fin n) (Fin n) ι ι R (↑g))) 0 0 1 =
      Matrix.reindex
        ((finProdMatrixEquiv (ι := ι) n).sumCongr
          ((finProdMatrixEquiv (ι := ι) 1).trans (oneMulFinCongr (Fintype.card ι))))
        ((finProdMatrixEquiv (ι := ι) n).sumCongr
          ((finProdMatrixEquiv (ι := ι) 1).trans (oneMulFinCongr (Fintype.card ι))))
        (fromBlocks (Matrix.comp (Fin n) (Fin n) ι ι R (↑g)) 0 0 1) := by
  classical
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp
    · simp
  · rcases j with j | j
    · simp
    · simp
      by_cases h : i = j
      · subst h
        simp
      · simp [h]

/-- The stabilization square commutes pointwise: block stabilization after
flattening equals flattening after `GL` stabilization. The square has
vertical maps `matrixGLMulEquiv` and horizontal maps
`GeneralLinearGroup.stabilization` on top and `matrixBlockStabilization`
below. -/
theorem matrixBlockStabilization_matrixGLMulEquiv [Nonempty ι] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (Matrix ι ι R)) :
    matrixBlockStabilization (R := R) (ι := ι) n
        (matrixGLMulEquiv (R := R) (ι := ι) n g) =
      matrixGLMulEquiv (R := R) (ι := ι) (n + 1)
        (Matrix.GeneralLinearGroup.stabilization (Matrix ι ι R) g) := by
  apply Units.ext
  have hLHS_unfold : (↑(matrixBlockStabilization (R := R) (ι := ι) n
        (matrixGLMulEquiv (R := R) (ι := ι) n g)) :
      Matrix (Fin ((n + 1) * Fintype.card ι)) (Fin ((n + 1) * Fintype.card ι)) R) =
      Matrix.reindex (castSuccMul (ι := ι) n) (castSuccMul (ι := ι) n)
        (Matrix.reindex (finSumFinEquiv (m := n * Fintype.card ι) (n := Fintype.card ι))
          (finSumFinEquiv (m := n * Fintype.card ι) (n := Fintype.card ι))
          (fromBlocks
            (Matrix.reindex (finProdMatrixEquiv (ι := ι) n) (finProdMatrixEquiv (ι := ι) n)
              (Matrix.comp (Fin n) (Fin n) ι ι R (↑g))) 0 0 1)) := rfl
  have hRHS_unfold : (↑(matrixGLMulEquiv (R := R) (ι := ι) (n + 1)
        (Matrix.GeneralLinearGroup.stabilization (Matrix ι ι R) g)) :
      Matrix (Fin ((n + 1) * Fintype.card ι)) (Fin ((n + 1) * Fintype.card ι)) R) =
      Matrix.reindex (finProdMatrixEquiv (ι := ι) (n + 1)) (finProdMatrixEquiv (ι := ι) (n + 1))
        (Matrix.comp (Fin (n + 1)) (Fin (n + 1)) ι ι R
          (Matrix.reindex (finSumFinEquiv (m := n) (n := 1))
            (finSumFinEquiv (m := n) (n := 1))
            (fromBlocks (↑g : Matrix (Fin n) (Fin n) (Matrix ι ι R)) 0 0 1))) := rfl
  have hLHS_block : (↑(matrixBlockStabilization (R := R) (ι := ι) n
        (matrixGLMulEquiv (R := R) (ι := ι) n g)) :
      Matrix (Fin ((n + 1) * Fintype.card ι)) (Fin ((n + 1) * Fintype.card ι)) R) =
      Matrix.reindex (blockSuccEquiv (ι := ι) n) (blockSuccEquiv (ι := ι) n)
        (fromBlocks (Matrix.comp (Fin n) (Fin n) ι ι R (↑g)) 0 0 1) := by
    calc _ = Matrix.reindex (castSuccMul (ι := ι) n) (castSuccMul (ι := ι) n)
          (Matrix.reindex (finSumFinEquiv (m := n * Fintype.card ι) (n := Fintype.card ι))
            (finSumFinEquiv (m := n * Fintype.card ι) (n := Fintype.card ι))
            (fromBlocks
              (Matrix.reindex (finProdMatrixEquiv (ι := ι) n) (finProdMatrixEquiv (ι := ι) n)
                (Matrix.comp (Fin n) (Fin n) ι ι R (↑g))) 0 0 1)) := hLHS_unfold
      _ = Matrix.reindex (castSuccMul (ι := ι) n) (castSuccMul (ι := ι) n)
            (Matrix.reindex (finSumFinEquiv (m := n * Fintype.card ι) (n := Fintype.card ι))
              (finSumFinEquiv (m := n * Fintype.card ι) (n := Fintype.card ι))
              (Matrix.reindex
                ((finProdMatrixEquiv (ι := ι) n).sumCongr
                  ((finProdMatrixEquiv (ι := ι) 1).trans (oneMulFinCongr (Fintype.card ι))))
                ((finProdMatrixEquiv (ι := ι) n).sumCongr
                  ((finProdMatrixEquiv (ι := ι) 1).trans (oneMulFinCongr (Fintype.card ι))))
                (fromBlocks (Matrix.comp (Fin n) (Fin n) ι ι R (↑g)) 0 0 1))) := by
          rw [← fromBlocks_reindex_prodEquiv]
      _ = _ := by
          ext i j
          simp [Matrix.reindex_apply, blockSuccEquiv]
  have hRHS_prod : (↑(matrixGLMulEquiv (R := R) (ι := ι) (n + 1)
        (Matrix.GeneralLinearGroup.stabilization (Matrix ι ι R) g)) :
      Matrix (Fin ((n + 1) * Fintype.card ι)) (Fin ((n + 1) * Fintype.card ι)) R) =
      Matrix.reindex (prodSuccEquiv (ι := ι) n) (prodSuccEquiv (ι := ι) n)
        (fromBlocks (Matrix.comp (Fin n) (Fin n) ι ι R (↑g)) 0 0 1) := by
    calc _ = Matrix.reindex (finProdMatrixEquiv (ι := ι) (n + 1))
            (finProdMatrixEquiv (ι := ι) (n + 1))
            (Matrix.comp (Fin (n + 1)) (Fin (n + 1)) ι ι R
              (Matrix.reindex (finSumFinEquiv (m := n) (n := 1))
                (finSumFinEquiv (m := n) (n := 1))
                (fromBlocks (↑g : Matrix (Fin n) (Fin n) (Matrix ι ι R)) 0 0 1))) := hRHS_unfold
      _ = Matrix.reindex (finProdMatrixEquiv (ι := ι) (n + 1))
            (finProdMatrixEquiv (ι := ι) (n + 1))
            (Matrix.reindex (α := R)
              (finSumFinEquiv (m := n) (n := 1) |>.prodCongr (Equiv.refl ι))
              (finSumFinEquiv (m := n) (n := 1) |>.prodCongr (Equiv.refl ι))
              (Matrix.comp (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ι ι R
                (fromBlocks (↑g : Matrix (Fin n) (Fin n) (Matrix ι ι R)) 0 0 1))) := by
          rw [comp_reindex_finSumEquiv]
      _ = Matrix.reindex (finProdMatrixEquiv (ι := ι) (n + 1))
            (finProdMatrixEquiv (ι := ι) (n + 1))
            (Matrix.reindex (α := R)
              (finSumFinEquiv (m := n) (n := 1) |>.prodCongr (Equiv.refl ι))
              (finSumFinEquiv (m := n) (n := 1) |>.prodCongr (Equiv.refl ι))
              (Matrix.reindex (α := R) (Equiv.sumProdDistrib (Fin n) (Fin 1) ι).symm
                (Equiv.sumProdDistrib (Fin n) (Fin 1) ι).symm
                (fromBlocks (Matrix.comp (Fin n) (Fin n) ι ι R (↑g)) 0 0 1))) := by
          rw [comp_blockDiagonalOne_sumProd]
      _ = _ := by
          ext i j
          simp [Matrix.reindex_apply, prodSuccEquiv, finSuccProdDecomp, finSuccSumEquiv]
  rw [hLHS_block, hRHS_prod, blockSuccEquiv_eq_prodSuccEquiv]

/-- The stabilization square as an equality of `MonoidHom` compositions:
`matrixBlockStabilization ∘ matrixGLMulEquiv = matrixGLMulEquiv ∘ stabilization`.
This is the `MonoidHom` form of the commuting stabilization square whose
vertical sides are `matrixGLMulEquiv` and whose horizontal sides are `GL`
stabilization and `matrixBlockStabilization`. -/
theorem matrixBlockStabilization_comp_matrixGLMulEquiv [Nonempty ι] (n : ℕ) :
    (matrixBlockStabilization (R := R) (ι := ι) n).comp
        (matrixGLMulEquiv (R := R) (ι := ι) n).toMonoidHom =
      (matrixGLMulEquiv (R := R) (ι := ι) (n + 1)).toMonoidHom.comp
        (Matrix.GeneralLinearGroup.stabilization (Matrix ι ι R)) := by
  apply MonoidHom.ext
  intro g
  exact matrixBlockStabilization_matrixGLMulEquiv n g

end MatrixDiagram
end AlgebraicKTheory

end
