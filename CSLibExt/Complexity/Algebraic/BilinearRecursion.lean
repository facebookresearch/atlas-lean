/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.CircuitComposition
public import CSLibExt.Complexity.Algebraic.MatrixMultiplication
public import CSLibExt.Complexity.Algebraic.MatrixMultiplicationExponent

/-!
# Recursive bilinear matrix-multiplication circuits

Given a trilinear decomposition of `q`-by-`q` matrix multiplication, the block
encoder forms, for each term, the two block linear combinations of the input
matrices, the block decoder reassembles the per-term outputs into the output
blocks, and `recursiveCircuit` iterates the construction to multiply
`q ^ k`-by-`q ^ k` matrices: encode, run one recursive copy per term in
parallel, decode.
-/

set_option autoImplicit false

universe u v w v'

namespace Cslib.Complexity.Algebraic

@[expose] public section

/-- For each term, the two block linear combinations of the input matrices (the
left and middle factors). -/
noncomputable def blockEncoder {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ) :
    ArithmeticCircuit F
      ((Fin (q ^ (k + 1)) × Fin (q ^ (k + 1))) ⊕
        (Fin (q ^ (k + 1)) × Fin (q ^ (k + 1))))
      (Fin terms.length ×
        ((Fin (q ^ k) × Fin (q ^ k)) ⊕ (Fin (q ^ k) × Fin (q ^ k)))) :=
  ArithmeticCircuit.linearCombination
    (fun
      | (t, Sum.inl (a, c)), x => (terms[t]).left x
      | (t, Sum.inr (c, b)), y => (terms[t]).middle y)
    (fun
      | (_t, Sum.inl (a, c)), x =>
        Sum.inl ((finPowSuccEquiv q k).symm (x.1, a),
          (finPowSuccEquiv q k).symm (x.2, c))
      | (_t, Sum.inr (c, b)), y =>
        Sum.inr ((finPowSuccEquiv q k).symm (y.1, c),
          (finPowSuccEquiv q k).symm (y.2, b)))

/-- Reassemble per-term outputs into output blocks. The third factor is read at
the transposed coordinate `((e L).1, (e I).1)`, not `((e I).1, (e L).1)`,
because the provider's tensor is cyclic (its contraction reads `(k, i)` for
output `(i, k)`); the untransposed read is wrong for `q >= 2, k >= 1`. -/
noncomputable def blockDecoder {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ) :
    ArithmeticCircuit F
      (Fin terms.length × (Fin (q ^ k) × Fin (q ^ k)))
      (Fin (q ^ (k + 1)) × Fin (q ^ (k + 1))) :=
  ArithmeticCircuit.linearCombination
    (fun (I, L) t =>
      (terms[t]).right (((finPowSuccEquiv q k) L).1, ((finPowSuccEquiv q k) I).1))
    (fun (I, L) t =>
      (t, (((finPowSuccEquiv q k) I).2, ((finPowSuccEquiv q k) L).2)))

/-- The `k`-fold block recursion of a fixed trilinear decomposition: encode the
two `q^(k+1)`-block matrices per term, run `terms.length` copies of the level-`k`
circuit in parallel, and decode. At level 0 it is the one-gate outer-product
circuit. Correctness is the companion theorem `recursiveCircuit_isMatrixMultiplication`
(companion stage). -/
noncomputable def recursiveCircuit {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) :
    (k : ℕ) → MatrixArithmeticCircuit F (q ^ k) (q ^ k) (q ^ k)
  | 0 => outerMatrixCircuit F 1 1
  | k + 1 => (blockDecoder terms k).subst
      (((recursiveCircuit terms k).parallel terms.length).subst
        (blockEncoder terms k))

/-- Left encoded block matrix for one term: at `(a, c)`, the sum over the
decomposition coordinates of the left coefficient times the matching `A` block
entry. -/
private noncomputable def encLeft {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ)
    (A : Matrix (Fin (q ^ (k + 1))) (Fin (q ^ (k + 1))) F)
    (t : Fin terms.length) : Matrix (Fin (q ^ k)) (Fin (q ^ k)) F :=
  Matrix.of fun a c => ∑ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
    (terms[t]).left x * A ((finPowSuccEquiv q k).symm (x.1, a))
      ((finPowSuccEquiv q k).symm (x.2, c))

/-- Right encoded block matrix for one term: at `(c, b)`, the sum over the
decomposition coordinates of the middle coefficient times the matching `B`
block entry. -/
private noncomputable def encRight {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ)
    (B : Matrix (Fin (q ^ (k + 1))) (Fin (q ^ (k + 1))) F)
    (t : Fin terms.length) : Matrix (Fin (q ^ k)) (Fin (q ^ k)) F :=
  Matrix.of fun c b => ∑ y : MatrixMultiplicationExponent.MatrixCoordinate q q,
    (terms[t]).middle y * B ((finPowSuccEquiv q k).symm (y.1, c))
      ((finPowSuccEquiv q k).symm (y.2, b))

/-- The `q`-by-`q` slice of `A` over block row `a` and block column `c`. -/
private noncomputable def sliceLeft {F : Type u} {q k : ℕ}
    (A : Matrix (Fin (q ^ (k + 1))) (Fin (q ^ (k + 1))) F)
    (a c : Fin (q ^ k)) : Matrix (Fin q) (Fin q) F :=
  Matrix.of fun p1 p2 => A ((finPowSuccEquiv q k).symm (p1, a))
    ((finPowSuccEquiv q k).symm (p2, c))

/-- The `q`-by-`q` slice of `B` over block row `c` and block column `b`. -/
private noncomputable def sliceRight {F : Type u} {q k : ℕ}
    (B : Matrix (Fin (q ^ (k + 1))) (Fin (q ^ (k + 1))) F)
    (c b : Fin (q ^ k)) : Matrix (Fin q) (Fin q) F :=
  Matrix.of fun p1 p2 => B ((finPowSuccEquiv q k).symm (p1, c))
    ((finPowSuccEquiv q k).symm (p2, b))

/-- The encoder's output at copy `t` is the matrix input of the two encoded
block matrices. -/
private theorem evaluate_blockEncoder {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ)
    (A B : Matrix (Fin (q ^ (k + 1))) (Fin (q ^ (k + 1))) F)
    (t : Fin terms.length)
    (p : (Fin (q ^ k) × Fin (q ^ k)) ⊕ (Fin (q ^ k) × Fin (q ^ k))) :
    (blockEncoder terms k).evaluate (matrixInput A B) (t, p) =
      matrixInput (encLeft terms k A t) (encRight terms k B t) p := by
  cases p with
  | inl q =>
    obtain ⟨a, c⟩ := q
    simp only [blockEncoder, ArithmeticCircuit.evaluate_linearCombination,
      matrixInput, Sum.elim_inl, encLeft, Matrix.of_apply]
  | inr q =>
    obtain ⟨c, b⟩ := q
    simp only [blockEncoder, ArithmeticCircuit.evaluate_linearCombination,
      matrixInput, Sum.elim_inr, encRight, Matrix.of_apply]

end

end Cslib.Complexity.Algebraic
