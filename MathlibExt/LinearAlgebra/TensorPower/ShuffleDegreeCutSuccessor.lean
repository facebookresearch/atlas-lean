/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.TensorPower.ShuffleCutDescents

/-!
# Successor formulas for weak shuffle cuts

A weak degree cut of n is a pair (p,q) with p,q≥0 and p+q=n. Increasing the first block sends
(p,q) to (p+1,q); increasing the second sends it to (p,q+1). Sums over cuts of n+1 split at
(0,n+1) or (n+1,0), respectively. The formulas hold with values in any additive commutative
monoid and retain the two empty-block endpoints.

For the use of such cuts in tensor shuffles, see J.-L. Loday, Cyclic Homology, 2nd ed., §4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace TensorPower

/-- Increasing the first block of a weak cut.

For p,q≥0 with p+q=n, the left successor sends the cut (p,q) of n to (p+1,q), a weak cut of
n+1. -/
def leftSuccessorDegreeCut {n : ℕ} (z : ShuffleDegreeCut n) : ShuffleDegreeCut (n + 1) :=
  ⟨(z.val.1 + 1, z.val.2), by have h := z.property; omega⟩

/-- Increasing the second block of a weak cut.

For p,q≥0 with p+q=n, the right successor sends the cut (p,q) of n to (p,q+1), a weak cut of
n+1. -/
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

/-- Splitting a weak-cut sum at the empty first block.

For an additive commutative monoid T and f on weak cuts of n+1, ∑cuts f = f(0,n+1) + ∑p+q=n
f(p+1,q). Both p and q in the second sum may be zero. -/
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

/-- Splitting a weak-cut sum at the empty second block.

For an additive commutative monoid T and f on weak cuts of n+1, ∑cuts f = ∑p+q=n f(p,q+1) +
f(n+1,0), with p,q≥0. -/
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
