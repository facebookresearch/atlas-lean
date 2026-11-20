/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexSectorOrientedSplit









open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



def matrixOrientationWordProduct {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha] (B : Matrix alpha alpha Real) :
    (M : Nat) -> (Fin M -> Bool) -> Matrix alpha alpha Real
  | 0, _ => 1
  | M + 1, word =>
      (if word 0 then B else Bᵀ) *
        matrixOrientationWordProduct B M (Fin.tail word)

@[simp] theorem matrixOrientationWordProduct_zero
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (B : Matrix alpha alpha Real) (word : Fin 0 -> Bool) :
    matrixOrientationWordProduct B 0 word = 1 := rfl

@[simp] theorem matrixOrientationWordProduct_cons
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (B : Matrix alpha alpha Real) (M : Nat) (b : Bool)
    (word : Fin M -> Bool) :
    matrixOrientationWordProduct B (M + 1) (Fin.cons b word) =
      (if b then B else Bᵀ) *
        matrixOrientationWordProduct B M word := by
  simp [matrixOrientationWordProduct]

theorem sum_matrixOrientationWordProduct_succ
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (B : Matrix alpha alpha Real) (M : Nat) :
    (∑ word : Fin (M + 1) -> Bool,
        matrixOrientationWordProduct B (M + 1) word) =
      (B + Bᵀ) *
        ∑ word : Fin M -> Bool,
          matrixOrientationWordProduct B M word := by
  classical
  calc
    (∑ word : Fin (M + 1) -> Bool,
        matrixOrientationWordProduct B (M + 1) word) =
        ∑ bw : Bool × (Fin M -> Bool),
          matrixOrientationWordProduct B (M + 1)
            (Fin.cons bw.1 bw.2) := by
      symm
      apply Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (M + 1) => Bool)
      intro bw
      rfl
    _ = ∑ b : Bool, ∑ word : Fin M -> Bool,
          (if b then B else Bᵀ) *
            matrixOrientationWordProduct B M word := by
      rw [Fintype.sum_prod_type]
      simp only [matrixOrientationWordProduct_cons]
    _ = ∑ b : Bool, (if b then B else Bᵀ) *
          ∑ word : Fin M -> Bool,
            matrixOrientationWordProduct B M word := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
    _ = (B + Bᵀ) *
          ∑ word : Fin M -> Bool,
            matrixOrientationWordProduct B M word := by
      simp only [Fintype.sum_bool]
      noncomm_ring


theorem add_transpose_pow_eq_sum_orientationWords
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (B : Matrix alpha alpha Real) (M : Nat) :
    (B + Bᵀ) ^ M =
      ∑ word : Fin M -> Bool,
        matrixOrientationWordProduct B M word := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [pow_succ']
      rw [ih]
      exact (sum_matrixOrientationWordProduct_succ B M).symm


theorem sixVertexSectorTransfer_pow_eq_sum_orientationWords
    (N n M : Nat) (c : Real) :
    sixVertexSectorTransfer N n c ^ M =
      ∑ word : Fin M -> Bool,
        matrixOrientationWordProduct
          (sixVertexSectorForwardTransfer N n c) M word := by
  rw [sixVertexSectorTransfer_eq_forward_add_transpose]
  exact add_transpose_pow_eq_sum_orientationWords
    (sixVertexSectorForwardTransfer N n c) M


theorem trace_sixVertexSectorTransfer_pow_eq_sum_orientationWords
    (N n M : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N n c ^ M) =
      ∑ word : Fin M -> Bool,
        Matrix.trace (matrixOrientationWordProduct
          (sixVertexSectorForwardTransfer N n c) M word) := by
  rw [sixVertexSectorTransfer_pow_eq_sum_orientationWords]
  exact Matrix.trace_sum Finset.univ fun word =>
    matrixOrientationWordProduct
      (sixVertexSectorForwardTransfer N n c) M word


noncomputable def sixVertexOrientationWordTrace
    (N M : Nat) (c : Real) (n : Nat) (word : Fin M -> Bool) : Real :=
  Matrix.trace (matrixOrientationWordProduct
    (sixVertexSectorForwardTransfer N n c) M word)

theorem trace_sixVertexSectorTransfer_pow_eq_sum_wordTrace
    (N n M : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N n c ^ M) =
      ∑ word : Fin M -> Bool,
        sixVertexOrientationWordTrace N M c n word :=
  trace_sixVertexSectorTransfer_pow_eq_sum_orientationWords N n M c



theorem traceProduct_sixVertexSectorTransfer_pow_eq_sum_wordPairs
    (N nLeft nRight M : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N nLeft c ^ M) *
        Matrix.trace (sixVertexSectorTransfer N nRight c ^ M) =
      ∑ leftWord : Fin M -> Bool,
        ∑ rightWord : Fin M -> Bool,
          sixVertexOrientationWordTrace N M c nLeft leftWord *
            sixVertexOrientationWordTrace N M c nRight rightWord := by
  rw [trace_sixVertexSectorTransfer_pow_eq_sum_wordTrace,
    trace_sixVertexSectorTransfer_pow_eq_sum_wordTrace,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro leftWord hleftWord
  rw [Finset.mul_sum]




theorem sixVertexSectorTrace_logConcave_iff_wordPairSum
    (N M n : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N (n - 1) c ^ M) *
          Matrix.trace (sixVertexSectorTransfer N (n + 1) c ^ M) <=
        Matrix.trace (sixVertexSectorTransfer N n c ^ M) ^ 2 <->
      (∑ leftWord : Fin M -> Bool,
          ∑ rightWord : Fin M -> Bool,
            sixVertexOrientationWordTrace N M c (n - 1) leftWord *
              sixVertexOrientationWordTrace N M c (n + 1) rightWord) <=
        ∑ leftWord : Fin M -> Bool,
          ∑ rightWord : Fin M -> Bool,
            sixVertexOrientationWordTrace N M c n leftWord *
              sixVertexOrientationWordTrace N M c n rightWord := by
  rw [<- traceProduct_sixVertexSectorTransfer_pow_eq_sum_wordPairs,
    <- traceProduct_sixVertexSectorTransfer_pow_eq_sum_wordPairs]
  rw [pow_two]

end

end StatMech.FrontierD
