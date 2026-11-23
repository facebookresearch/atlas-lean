/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel.Matrix
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace FGProjectiveCat.IdempotentModel.MatrixChecks

noncomputable section

universe u

private noncomputable def genericCornerMorphism
    (A : Type u) [Ring A]
    {P Q : FGProjectiveCat.IdempotentModel A}
    (b : Matrix (Fin P.X) (Fin Q.X) A)
    (hb : rowHomEquiv A P.X P.X P.p * b *
      rowHomEquiv A Q.X Q.X Q.p = b) : P ⟶ Q :=
  homOfMatrix A b hb

private theorem genericCornerMorphism_matrix
    (A : Type u) [Ring A]
    {P Q : FGProjectiveCat.IdempotentModel A}
    (b : Matrix (Fin P.X) (Fin Q.X) A)
    (hb : rowHomEquiv A P.X P.X P.p * b *
      rowHomEquiv A Q.X Q.X Q.p = b) :
    rowHomEquiv A P.X Q.X (genericCornerMorphism A b hb).f = b :=
  homOfMatrix_matrix A b hb

private noncomputable def zeroCornerMorphism
    (A : Type u) [Ring A]
    (P Q : FGProjectiveCat.IdempotentModel A) : P ⟶ Q :=
  homOfMatrix A 0 (by rw [Matrix.mul_zero, Matrix.zero_mul])

private abbrev NoncommutativeCoefficient := Matrix (Fin 2) (Fin 2) ℤ

private theorem noncommutative_matrix_characteristic
    {P Q : FGProjectiveCat.IdempotentModel NoncommutativeCoefficient}
    (b : Matrix (Fin P.X) (Fin Q.X) NoncommutativeCoefficient)
    (hb : rowHomEquiv NoncommutativeCoefficient P.X P.X P.p * b *
      rowHomEquiv NoncommutativeCoefficient Q.X Q.X Q.p = b) :
    rowHomEquiv NoncommutativeCoefficient P.X Q.X
        (homOfMatrix NoncommutativeCoefficient b hb).f = b :=
  homOfMatrix_matrix _ b hb

open CategoryTheory CategoryTheory.Limits

example (A : Type u) [Ring A] (P Q : FGProjectiveCat.IdempotentModel A) :
    blockModel A P Q ≅ P ⊞ Q :=
  blockModelIso A P Q

example (A : Type u) [Ring A] {n m : ℕ}
    (p : Matrix (Fin n) (Fin n) A) (q : Matrix (Fin m) (Fin m) A)
    (hp : p * p = p) (hq : q * q = q) :
    rowHomEquiv A (n + m) (n + m)
      (blockModel A (matrixModel A p hp) (matrixModel A q hq)).p = blockMatrix A p q :=
  (blockModel_matrix A (matrixModel A p hp) (matrixModel A q hq)).trans
    (congrArg₂ (blockMatrix A) (matrixModel_matrix A p hp) (matrixModel_matrix A q hq))

example (A : Type u) [Ring A] (P : FGProjectiveCat.IdempotentModel A) :
    (blockModel A (matrixModel A (0 : Matrix (Fin 0) (Fin 0) A) (Matrix.zero_mul _)) P).X = P.X := by
  rw [blockModel_rank]
  exact Nat.zero_add _

example (P Q : FGProjectiveCat.IdempotentModel (Matrix (Fin 2) (Fin 2) ℤ)) :
    Nonempty (blockModel (Matrix (Fin 2) (Fin 2) ℤ) P Q ≅ P ⊞ Q) :=
  ⟨blockModelIso _ P Q⟩

#print axioms homOfMatrix
#print axioms homOfMatrix_matrix
#print axioms matrixModel
#print axioms matrixModel_matrix
#print axioms blockMatrix
#print axioms blockMatrix_map
#print axioms blockMatrix_idempotent
#print axioms blockModel
#print axioms blockModel_rank
#print axioms blockModel_matrix
#print axioms blockModelIso
#print axioms modelIsoOfInverseMatrices

end

end FGProjectiveCat.IdempotentModel.MatrixChecks
