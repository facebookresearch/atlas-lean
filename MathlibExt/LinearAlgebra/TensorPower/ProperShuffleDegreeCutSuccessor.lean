/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.TensorPower.ShuffleDegreeCutSuccessor

/-!
# Successor formulas for both-positive shuffle cuts

A proper degree cut of n is a pair (p,q) with p+q=n and p,q>0. The cuts of n+1 are parametrized
by Fin n using p-1. Increasing the first or second block defines successor maps. For an additive
commutative monoid T, sums over cuts of n+2 split into the endpoint (1,n+1) and first-block
successors, or into second-block successors and the endpoint (n+1,1).

These index the both-positive shuffle relations of J.-L. Loday, Cyclic Homology, 2nd ed., §4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace TensorPower

/-- The finite coordinate of a both-positive degree cut.

For n ≥ 0, the proper cuts (p,q) of n+1 with p,q>0 are equivalent to Fin n by (p,q) ↦ p-1.
The inverse sends i to (i+1,n-i). -/
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

/-- The first both-positive cut in degree n+2.

For n ≥ 0, this proper degree cut is (1,n+1). Both block lengths are strictly positive and
their sum is n+2. -/
def firstProperDegreeCut (n : ℕ) : ProperShuffleDegreeCut (n + 2) :=
  by
    refine ⟨⟨(1, n + 1), ?_⟩, ?_, ?_⟩
    · change 1 + (n + 1) = n + 2
      omega
    · change 0 < (1 : ℕ)
      omega
    · change 0 < n + 1
      omega

/-- The last both-positive cut in degree n+2.

For n ≥ 0, this proper degree cut is (n+1,1). Both block lengths are strictly positive and
their sum is n+2. -/
def lastProperDegreeCut (n : ℕ) : ProperShuffleDegreeCut (n + 2) :=
  by
    refine ⟨⟨(n + 1, 1), ?_⟩, ?_, ?_⟩
    · change (n + 1) + 1 = n + 2
      omega
    · change 0 < n + 1
      omega
    · change 0 < (1 : ℕ)
      omega

/-- Increasing the first block of a proper cut.

For a proper cut (p,q) of n, with p,q>0 and p+q=n, the left successor is (p+1,q), a proper
cut of n+1. -/
def leftSuccessorProperDegreeCut {n : ℕ} (z : ProperShuffleDegreeCut n) : ProperShuffleDegreeCut (n
  + 1) :=
  ⟨leftSuccessorDegreeCut z.val, by
    change 0 < z.val.val.1 + 1
    omega, z.property.2⟩

/-- Increasing the second block of a proper cut.

For a proper cut (p,q) of n, with p,q>0 and p+q=n, the right successor is (p,q+1), a proper
cut of n+1. -/
def rightSuccessorProperDegreeCut {n : ℕ} (z : ProperShuffleDegreeCut n) : ProperShuffleDegreeCut (n
  + 1) :=
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

/-- Splitting a proper-cut sum at the first endpoint.

For an additive commutative monoid T and f on proper cuts of n+2, ∑cuts f = f(1,n+1) +
∑(p,q) proper of n+1 f(p+1,q). This also covers n=0, when the successor-cut sum is empty. -/
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
  rw [(properShuffleDegreeCutPosition n).symm.sum_comp (fun z => f (leftSuccessorProperDegreeCut
    z))]

/-- Splitting a proper-cut sum at the last endpoint.

For an additive commutative monoid T and f on proper cuts of n+2, ∑cuts f = ∑(p,q) proper of
n+1 f(p,q+1) + f(n+1,1). The sum uses only strictly positive block lengths. -/
theorem sum_properDegreeCuts_right_successor {T : Type*} [AddCommMonoid T]
    (n : ℕ) (f : ProperShuffleDegreeCut (n + 2) → T) :
    (∑ z : ProperShuffleDegreeCut (n + 2), f z) =
      (∑ z : ProperShuffleDegreeCut (n + 1), f (rightSuccessorProperDegreeCut z)) +
        f (lastProperDegreeCut n) := by
  classical
  rw [← (properShuffleDegreeCutPosition (n + 1)).symm.sum_comp f, Fin.sum_univ_castSucc]
  have hlast : (properShuffleDegreeCutPosition (n + 1)).symm (Fin.last n) = lastProperDegreeCut n :=
    by
    apply Subtype.ext
    apply Subtype.ext
    change (n + 1, n + 1 - n) = (n + 1, 1)
    simp
  rw [hlast]
  simp_rw [properPosition_symm_castSucc]
  rw [(properShuffleDegreeCutPosition n).symm.sum_comp (fun z => f (rightSuccessorProperDegreeCut
    z))]

end TensorPower
