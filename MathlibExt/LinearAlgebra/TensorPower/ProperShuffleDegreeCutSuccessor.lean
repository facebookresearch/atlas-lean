/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.TensorPower.ShuffleDegreeCutSuccessor

/-!
# Actual positive-cut successor sums

The original both-positive cut set in degree n+1 is genuinely Fin n.
Native finite-sum first/last splitting therefore separates the actual
endpoint cut (1,n+1) or (n+1,1) from the two corresponding successor-cut
sums. No differential or convolution identity is supplied.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace TensorPower

/-- The original both-positive degree cuts are determined by first length minus one. -/
def properShuffleDegreeCutPosition (n : ℕ) : ProperShuffleDegreeCut (n + 1) ≃ Fin n where
  toFun z := ⟨z.val.val.1 - 1, by
    have hp := z.property.1
    have hq := z.property.2
    have hsum := z.val.property
    omega⟩
  invFun i := by
    refine ⟨⟨(i.val + 1, n - i.val), ?_⟩, ?_, ?_⟩
    · have hi := i.isLt
      omega
    · change 0 < i.val + 1
      omega
    · change 0 < n - i.val
      have hi := i.isLt
      omega
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change (z.val.val.1 - 1) + 1 = z.val.val.1
      have hp := z.property.1
      omega
    · change n - (z.val.val.1 - 1) = z.val.val.2
      have hp := z.property.1
      have hsum := z.val.property
      omega
  right_inv i := by
    apply Fin.ext
    change (i.val + 1) - 1 = i.val
    omega

/-- The actual left endpoint both-positive cut in original degree n+2. -/
def firstProperDegreeCut (n : ℕ) : ProperShuffleDegreeCut (n + 2) :=
  by
    refine ⟨⟨(1, n + 1), ?_⟩, ?_, ?_⟩
    · change 1 + (n + 1) = n + 2
      omega
    · change 0 < (1 : ℕ)
      omega
    · change 0 < n + 1
      omega

/-- The actual right endpoint both-positive cut in original degree n+2. -/
def lastProperDegreeCut (n : ℕ) : ProperShuffleDegreeCut (n + 2) :=
  by
    refine ⟨⟨(n + 1, 1), ?_⟩, ?_, ?_⟩
    · change (n + 1) + 1 = n + 2
      omega
    · change 0 < n + 1
      omega
    · change 0 < (1 : ℕ)
      omega

/-- The original left successor retains both actual positive blocks. -/
def leftSuccessorProperDegreeCut {n : ℕ} (z : ProperShuffleDegreeCut n) : ProperShuffleDegreeCut (n + 1) :=
  ⟨leftSuccessorDegreeCut z.val, by
    change 0 < z.val.val.1 + 1
    omega, z.property.2⟩

/-- The original right successor retains both actual positive blocks. -/
def rightSuccessorProperDegreeCut {n : ℕ} (z : ProperShuffleDegreeCut n) : ProperShuffleDegreeCut (n + 1) :=
  ⟨rightSuccessorDegreeCut z.val, z.property.1, by
    change 0 < z.val.val.2 + 1
    omega⟩

private theorem properPosition_symm_succ (n : ℕ) (i : Fin n) :
    (properShuffleDegreeCutPosition (n + 1)).symm i.succ =
      leftSuccessorProperDegreeCut ((properShuffleDegreeCutPosition n).symm i) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change n + 1 - (i.val + 1) = n - i.val
    omega

private theorem properPosition_symm_castSucc (n : ℕ) (i : Fin n) :
    (properShuffleDegreeCutPosition (n + 1)).symm i.castSucc =
      rightSuccessorProperDegreeCut ((properShuffleDegreeCutPosition n).symm i) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change n + 1 - i.val = (n - i.val) + 1
    have hi := i.isLt
    omega

/-- The actual both-positive successor cut sum splits off the original first cut. -/
theorem sum_properDegreeCuts_left_successor {T : Type*} [AddCommMonoid T]
    (n : ℕ) (f : ProperShuffleDegreeCut (n + 2) → T) :
    (∑ z : ProperShuffleDegreeCut (n + 2), f z) =
      f (firstProperDegreeCut n) +
        ∑ z : ProperShuffleDegreeCut (n + 1), f (leftSuccessorProperDegreeCut z) := by
  classical
  rw [← (properShuffleDegreeCutPosition (n + 1)).symm.sum_comp f, Fin.sum_univ_succ]
  have hzero : (properShuffleDegreeCutPosition (n + 1)).symm 0 = firstProperDegreeCut n := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [hzero]
  simp_rw [properPosition_symm_succ]
  rw [(properShuffleDegreeCutPosition n).symm.sum_comp (fun z => f (leftSuccessorProperDegreeCut z))]

/-- The actual both-positive successor cut sum splits off the original last cut. -/
theorem sum_properDegreeCuts_right_successor {T : Type*} [AddCommMonoid T]
    (n : ℕ) (f : ProperShuffleDegreeCut (n + 2) → T) :
    (∑ z : ProperShuffleDegreeCut (n + 2), f z) =
      (∑ z : ProperShuffleDegreeCut (n + 1), f (rightSuccessorProperDegreeCut z)) +
        f (lastProperDegreeCut n) := by
  classical
  rw [← (properShuffleDegreeCutPosition (n + 1)).symm.sum_comp f, Fin.sum_univ_castSucc]
  have hlast : (properShuffleDegreeCutPosition (n + 1)).symm (Fin.last n) = lastProperDegreeCut n := by
    apply Subtype.ext
    apply Subtype.ext
    change (n + 1, n + 1 - n) = (n + 1, 1)
    simp
  rw [hlast]
  simp_rw [properPosition_symm_castSucc]
  rw [(properShuffleDegreeCutPosition n).symm.sum_comp (fun z => f (rightSuccessorProperDegreeCut z))]

end TensorPower
