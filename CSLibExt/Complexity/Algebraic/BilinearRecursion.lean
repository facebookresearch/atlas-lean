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

end

end Cslib.Complexity.Algebraic
