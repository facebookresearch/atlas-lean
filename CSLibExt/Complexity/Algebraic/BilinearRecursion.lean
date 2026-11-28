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

/-- The recursive circuit computes matrix multiplication whenever `terms` is a
trilinear decomposition of the `q`-by-`q` multiplication tensor. -/
theorem recursiveCircuit_isMatrixMultiplication {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)))
    (hterms : ∀ a b c, MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q a b c =
      (terms.map fun term ↦ term.eval a b c).sum)
    (k : ℕ) : IsMatrixMultiplication (recursiveCircuit terms k) := by
  induction k with
  | zero => exact outerMatrixCircuit_correct 1 1
  | succ k ih =>
      intro A B I L
      change ((blockDecoder terms k).subst
        (((recursiveCircuit terms k).parallel terms.length).subst
          (blockEncoder terms k))).evaluate (matrixInput A B) (I, L) =
        (A * B) I L
      obtain ⟨i, a, heI⟩ : ∃ i a, (finPowSuccEquiv q k) I = (i, a) :=
        ⟨_, _, rfl⟩
      obtain ⟨l, b, heL⟩ : ∃ l b, (finPowSuccEquiv q k) L = (l, b) :=
        ⟨_, _, rfl⟩
      have hsymI : (finPowSuccEquiv q k).symm (i, a) = I := by
        rw [← heI]
        exact Equiv.symm_apply_apply _ _
      have hsymL : (finPowSuccEquiv q k).symm (l, b) = L := by
        rw [← heL]
        exact Equiv.symm_apply_apply _ _
      simp only [IsMatrixMultiplication] at ih
      simp only [blockDecoder, ArithmeticCircuit.evaluate_subst,
        ArithmeticCircuit.evaluate_linearCombination,
        ArithmeticCircuit.evaluate_parallel, evaluate_blockEncoder, ih]
      simp only [heI, heL, Matrix.mul_apply, encLeft, encRight,
        Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
      have hswap1 : (∑ t : Fin terms.length, ∑ c : Fin (q ^ k),
            ∑ y : MatrixMultiplicationExponent.MatrixCoordinate q q,
            ∑ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
            (terms[t]).right (l, i) *
              ((terms[t]).left x *
                  A ((finPowSuccEquiv q k).symm (x.1, a))
                    ((finPowSuccEquiv q k).symm (x.2, c)) *
                ((terms[t]).middle y *
                  B ((finPowSuccEquiv q k).symm (y.1, c))
                    ((finPowSuccEquiv q k).symm (y.2, b))))) =
          (∑ c : Fin (q ^ k), ∑ t : Fin terms.length,
            ∑ y : MatrixMultiplicationExponent.MatrixCoordinate q q,
            ∑ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
            (terms[t]).right (l, i) *
              ((terms[t]).left x *
                  A ((finPowSuccEquiv q k).symm (x.1, a))
                    ((finPowSuccEquiv q k).symm (x.2, c)) *
                ((terms[t]).middle y *
                  B ((finPowSuccEquiv q k).symm (y.1, c))
                    ((finPowSuccEquiv q k).symm (y.2, b))))) :=
        Finset.sum_comm
      rw [hswap1]
      have hswap2 : ∀ c : Fin (q ^ k), (∑ t : Fin terms.length,
            ∑ y : MatrixMultiplicationExponent.MatrixCoordinate q q,
            ∑ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
            (terms[t]).right (l, i) *
              ((terms[t]).left x *
                  A ((finPowSuccEquiv q k).symm (x.1, a))
                    ((finPowSuccEquiv q k).symm (x.2, c)) *
                ((terms[t]).middle y *
                  B ((finPowSuccEquiv q k).symm (y.1, c))
                    ((finPowSuccEquiv q k).symm (y.2, b))))) =
          (∑ y : MatrixMultiplicationExponent.MatrixCoordinate q q,
            ∑ t : Fin terms.length,
            ∑ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
            (terms[t]).right (l, i) *
              ((terms[t]).left x *
                  A ((finPowSuccEquiv q k).symm (x.1, a))
                    ((finPowSuccEquiv q k).symm (x.2, c)) *
                ((terms[t]).middle y *
                  B ((finPowSuccEquiv q k).symm (y.1, c))
                    ((finPowSuccEquiv q k).symm (y.2, b))))) :=
        fun c => Finset.sum_comm
      simp only [hswap2]
      have hswap3 : ∀ c : Fin (q ^ k),
          ∀ y : MatrixMultiplicationExponent.MatrixCoordinate q q,
          (∑ t : Fin terms.length,
            ∑ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
            (terms[t]).right (l, i) *
              ((terms[t]).left x *
                  A ((finPowSuccEquiv q k).symm (x.1, a))
                    ((finPowSuccEquiv q k).symm (x.2, c)) *
                ((terms[t]).middle y *
                  B ((finPowSuccEquiv q k).symm (y.1, c))
                    ((finPowSuccEquiv q k).symm (y.2, b))))) =
          (∑ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
            ∑ t : Fin terms.length,
            (terms[t]).right (l, i) *
              ((terms[t]).left x *
                  A ((finPowSuccEquiv q k).symm (x.1, a))
                    ((finPowSuccEquiv q k).symm (x.2, c)) *
                ((terms[t]).middle y *
                  B ((finPowSuccEquiv q k).symm (y.1, c))
                    ((finPowSuccEquiv q k).symm (y.2, b))))) :=
        fun c y => Finset.sum_comm
      simp only [hswap3]
      have hfactor : ∀ c : Fin (q ^ k),
          ∀ y : MatrixMultiplicationExponent.MatrixCoordinate q q,
          ∀ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
          (∑ t : Fin terms.length,
            (terms[t]).right (l, i) *
              ((terms[t]).left x *
                  A ((finPowSuccEquiv q k).symm (x.1, a))
                    ((finPowSuccEquiv q k).symm (x.2, c)) *
                ((terms[t]).middle y *
                  B ((finPowSuccEquiv q k).symm (y.1, c))
                    ((finPowSuccEquiv q k).symm (y.2, b))))) =
          (∑ t : Fin terms.length,
            (terms[t]).left x * (terms[t]).middle y *
              (terms[t]).right (l, i)) *
            A ((finPowSuccEquiv q k).symm (x.1, a))
              ((finPowSuccEquiv q k).symm (x.2, c)) *
            B ((finPowSuccEquiv q k).symm (y.1, c))
              ((finPowSuccEquiv q k).symm (y.2, b)) := by
        intro c y x
        calc (∑ t : Fin terms.length,
                (terms[t]).right (l, i) *
                  ((terms[t]).left x *
                      A ((finPowSuccEquiv q k).symm (x.1, a))
                        ((finPowSuccEquiv q k).symm (x.2, c)) *
                    ((terms[t]).middle y *
                      B ((finPowSuccEquiv q k).symm (y.1, c))
                        ((finPowSuccEquiv q k).symm (y.2, b))))) =
              ∑ t : Fin terms.length,
                ((terms[t]).left x * (terms[t]).middle y *
                  (terms[t]).right (l, i)) *
                  A ((finPowSuccEquiv q k).symm (x.1, a))
                    ((finPowSuccEquiv q k).symm (x.2, c)) *
                  B ((finPowSuccEquiv q k).symm (y.1, c))
                    ((finPowSuccEquiv q k).symm (y.2, b)) :=
              Finset.sum_congr rfl (fun t _ => by ring)
          _ = (∑ t : Fin terms.length,
                (terms[t]).left x * (terms[t]).middle y *
                  (terms[t]).right (l, i)) *
              A ((finPowSuccEquiv q k).symm (x.1, a))
                ((finPowSuccEquiv q k).symm (x.2, c)) *
              B ((finPowSuccEquiv q k).symm (y.1, c))
                ((finPowSuccEquiv q k).symm (y.2, b)) := by
              rw [← Finset.sum_mul, ← Finset.sum_mul]
      simp only [hfactor]
      have hterms'' : ∀ x y : MatrixMultiplicationExponent.MatrixCoordinate q q,
          (∑ t : Fin terms.length,
            (terms[t]).left x * (terms[t]).middle y *
              (terms[t]).right (l, i)) =
          MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q x y
            (l, i) := by
        intro x y
        rw [hterms x y (l, i)]
        exact Fin.sum_univ_fun_getElem terms
          (fun term ↦ term.eval x y (l, i))
      simp only [hterms'']
      have hcontract : ∀ c : Fin (q ^ k),
          (∑ y : MatrixMultiplicationExponent.MatrixCoordinate q q,
            ∑ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
            MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q x y
                (l, i) *
              A ((finPowSuccEquiv q k).symm (x.1, a))
                ((finPowSuccEquiv q k).symm (x.2, c)) *
              B ((finPowSuccEquiv q k).symm (y.1, c))
                ((finPowSuccEquiv q k).symm (y.2, b))) =
          ((sliceLeft A a c) * (sliceRight B c b)) i l := by
        intro c
        calc (∑ y : MatrixMultiplicationExponent.MatrixCoordinate q q,
                ∑ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
                MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q
                  x y (l, i) *
                  A ((finPowSuccEquiv q k).symm (x.1, a))
                    ((finPowSuccEquiv q k).symm (x.2, c)) *
                  B ((finPowSuccEquiv q k).symm (y.1, c))
                    ((finPowSuccEquiv q k).symm (y.2, b))) =
              (∑ x : MatrixMultiplicationExponent.MatrixCoordinate q q,
                ∑ y : MatrixMultiplicationExponent.MatrixCoordinate q q,
                MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q
                  x y (l, i) *
                  A ((finPowSuccEquiv q k).symm (x.1, a))
                    ((finPowSuccEquiv q k).symm (x.2, c)) *
                  B ((finPowSuccEquiv q k).symm (y.1, c))
                    ((finPowSuccEquiv q k).symm (y.2, b))) :=
              Finset.sum_comm
          _ = MatrixMultiplicationExponent.matrixMultiplicationTensorContraction F
                (sliceLeft A a c) (sliceRight B c b) i l := by
              simp only [MatrixMultiplicationExponent.matrixMultiplicationTensorContraction,
                MatrixMultiplicationExponent.squareMatrixMultiplicationTensor,
                sliceLeft, sliceRight, Matrix.of_apply]
          _ = ((sliceLeft A a c) * (sliceRight B c b)) i l :=
              MatrixMultiplicationExponent.matrixMultiplicationTensorContraction_eq_mul
                F (sliceLeft A a c) (sliceRight B c b) i l
      simp only [hcontract]
      simp only [Matrix.mul_apply, sliceLeft, sliceRight, Matrix.of_apply,
        hsymI, hsymL]
      have hreindex : (∑ c : Fin (q ^ k), ∑ j : Fin q,
            A I ((finPowSuccEquiv q k).symm (j, c)) *
              B ((finPowSuccEquiv q k).symm (j, c)) L)
          = ∑ j : Fin (q ^ (k + 1)), A I j * B j L := by
        rw [Finset.sum_comm]
        have hprod : (∑ j : Fin q, ∑ c : Fin (q ^ k),
              A I ((finPowSuccEquiv q k).symm (j, c)) *
                B ((finPowSuccEquiv q k).symm (j, c)) L)
            = ∑ p : Fin q × Fin (q ^ k),
              A I ((finPowSuccEquiv q k).symm p) *
                B ((finPowSuccEquiv q k).symm p) L :=
          (Fintype.sum_prod_type (fun p : Fin q × Fin (q ^ k) =>
            A I ((finPowSuccEquiv q k).symm p) *
              B ((finPowSuccEquiv q k).symm p) L)).symm
        rw [hprod]
        exact Equiv.sum_comp (finPowSuccEquiv q k).symm
          (fun j : Fin (q ^ (k + 1)) => A I j * B j L)
      exact hreindex

/-- Any rank bound on the `q`-by-`q` tensor yields recursive multiplication
circuits of every size `q ^ k` with at most `r` recursive products per level. -/
theorem exists_recursiveCircuit_isMatrixMultiplication {F : Type u} [Field F]
    {q r : ℕ}
    (h : MatrixMultiplicationExponent.HasTrilinearRankAtMost
      (MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q) r) (k : ℕ) :
    ∃ terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)), terms.length ≤ r ∧
      IsMatrixMultiplication (recursiveCircuit terms k) := by
  obtain ⟨terms, hlength, hterms⟩ := h
  exact ⟨terms, hlength, recursiveCircuit_isMatrixMultiplication terms hterms k⟩

end

end Cslib.Complexity.Algebraic
