/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.TensorPower.ShuffleCutDescents

/-!
# Actual successor reindexing of finite weak degree cuts

Each original finite weak cut is identified by its original first length.
Native finite-sum first/last splitting then gives the left/right
successor cut sums. Exact original degree equalities are retained. These
identities reindex actual incoming deconcatenation boundary terms, without
supplying a chain-map or convolution certificate.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace TensorPower

/-- Increment the original first block length and retain its exact successor degree. -/
def leftSuccessorDegreeCut {n : ℕ} (z : ShuffleDegreeCut n) : ShuffleDegreeCut (n + 1) :=
  ⟨(z.val.1 + 1, z.val.2), by have h := z.property; omega⟩

/-- Increment the original second block length and retain its exact successor degree. -/
def rightSuccessorDegreeCut {n : ℕ} (z : ShuffleDegreeCut n) : ShuffleDegreeCut (n + 1) :=
  ⟨(z.val.1, z.val.2 + 1), by have h := z.property; omega⟩

private theorem position_symm_succ (n : ℕ) (i : Fin (n + 1)) :
    (shuffleDegreeCutPosition (n + 1)).symm i.succ =
      leftSuccessorDegreeCut ((shuffleDegreeCutPosition n).symm i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change n + 1 - (i.val + 1) = n - i.val
    omega

private theorem position_symm_castSucc (n : ℕ) (i : Fin (n + 1)) :
    (shuffleDegreeCutPosition (n + 1)).symm i.castSucc =
      rightSuccessorDegreeCut ((shuffleDegreeCutPosition n).symm i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change n + 1 - i.val = (n - i.val) + 1
    have hi := i.isLt
    omega

/-- The actual full weak-cut sum is the original left unit plus the actual first-block successor cuts. -/
theorem sum_shuffleDegreeCuts_left_successor {T : Type*} [AddCommMonoid T]
    (n : ℕ) (f : ShuffleDegreeCut (n + 1) → T) :
    (∑ z : ShuffleDegreeCut (n + 1), f z) =
      f (leftUnitDegreeCut (n + 1)) + ∑ z : ShuffleDegreeCut n, f (leftSuccessorDegreeCut z) := by
  classical
  rw [← (shuffleDegreeCutPosition (n + 1)).symm.sum_comp f, Fin.sum_univ_succ]
  have hzero : (shuffleDegreeCutPosition (n + 1)).symm 0 = leftUnitDegreeCut (n + 1) := by
    apply Subtype.ext
    rfl
  rw [hzero]
  simp_rw [position_symm_succ]
  rw [(shuffleDegreeCutPosition n).symm.sum_comp (fun z => f (leftSuccessorDegreeCut z))]

/-- The actual full weak-cut sum is the actual second-block successor cuts plus the original right unit. -/
theorem sum_shuffleDegreeCuts_right_successor {T : Type*} [AddCommMonoid T]
    (n : ℕ) (f : ShuffleDegreeCut (n + 1) → T) :
    (∑ z : ShuffleDegreeCut (n + 1), f z) =
      (∑ z : ShuffleDegreeCut n, f (rightSuccessorDegreeCut z)) + f (rightUnitDegreeCut (n + 1)) := by
  classical
  rw [← (shuffleDegreeCutPosition (n + 1)).symm.sum_comp f, Fin.sum_univ_castSucc]
  have hlast : (shuffleDegreeCutPosition (n + 1)).symm (Fin.last (n + 1)) =
      rightUnitDegreeCut (n + 1) := by
    apply Subtype.ext
    change (n + 1, n + 1 - (n + 1)) = (n + 1, 0)
    simp
  rw [hlast]
  simp_rw [position_symm_castSucc]
  rw [(shuffleDegreeCutPosition n).symm.sum_comp (fun z => f (rightSuccessorDegreeCut z))]

end TensorPower
