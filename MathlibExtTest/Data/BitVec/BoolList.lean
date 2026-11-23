/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Data.BitVec.BoolList
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open Finset
open scoped BigOperators

namespace ETHBoolWordReference

/-- The original ETH recursive encoder, retained privately to verify the bridge. -/
private def toWord : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, y => decide (y % 2 = 1) :: toWord n (y / 2)

/-- The original ETH recursive decoder, retained privately to verify the bridge. -/
private def ofWord : List Bool → Nat
  | [] => 0
  | b :: w => b.toNat + 2 * ofWord w

/-- The original ETH finite set of words, retained privately to verify the bridge. -/
private def words (n : Nat) : Finset (List Bool) :=
  (range (2 ^ n)).image (toWord n)

private theorem length_toWord (n y : Nat) : (toWord n y).length = n := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp [toWord, ih]

private theorem ofWord_eq_toNat (w : List Bool) :
    ofWord w = (BitVec.ofBoolListLE w).toNat := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      simp [ofWord, BitVec.ofBoolListLE, BitVec.toNat_concat, ih, Nat.add_comm, Nat.mul_comm]

private theorem toBoolListLE_ofNat_succ (n y : Nat) :
    (BitVec.ofNat (n + 1) y).toBoolListLE =
      decide (y % 2 = 1) :: (BitVec.ofNat n (y / 2)).toBoolListLE := by
  unfold BitVec.toBoolListLE
  rw [List.ofFn_succ]
  congr 1
  · rw [BitVec.getLsbD_ofNat]
    change (decide (0 < n + 1) && y.testBit 0) = decide (y % 2 = 1)
    rw [Nat.testBit_zero]
    simp
  · apply congrArg List.ofFn
    funext i
    rw [BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
    change (decide (i.val + 1 < n + 1) && y.testBit (i.val + 1)) =
      (decide (i.val < n) && (y / 2).testBit i.val)
    rw [Nat.testBit_succ]
    simp [i.isLt]

private theorem toWord_eq_toBoolListLE (n y : Nat) :
    toWord n y = (BitVec.ofNat n y).toBoolListLE := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => rw [toWord, toBoolListLE_ofNat_succ, ih]

private theorem ofWord_toWord {n y : Nat} (h : y < 2 ^ n) :
    ofWord (toWord n y) = y := by
  rw [toWord_eq_toBoolListLE, ofWord_eq_toNat, BitVec.toNat_ofBoolListLE_toBoolListLE,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem toWord_ofWord (w : List Bool) : toWord w.length (ofWord w) = w := by
  rw [toWord_eq_toBoolListLE, ofWord_eq_toNat]
  have hbv : BitVec.ofNat w.length (BitVec.ofBoolListLE w).toNat =
      BitVec.ofBoolListLE w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.ofBoolListLE w).isLt]
  rw [hbv]
  have h := congrArg Subtype.val
    ((BitVec.equivBoolListLE w.length).apply_symm_apply
      (⟨w, rfl⟩ : {u : List Bool // u.length = w.length}))
  simpa [BitVec.equivBoolListLE] using h

@[simp] private theorem mem_words {n : Nat} {w : List Bool} : w ∈ words n ↔ w.length = n := by
  simp only [words, mem_image, mem_range]
  constructor
  · rintro ⟨y, _, rfl⟩
    exact length_toWord n y
  · intro hw
    subst n
    have hlt : ofWord w < 2 ^ w.length := by
      rw [ofWord_eq_toNat]
      exact (BitVec.ofBoolListLE w).isLt
    exact ⟨ofWord w, hlt, toWord_ofWord w⟩

private theorem toWord_injOn (n : Nat) : Set.InjOn (toWord n) (range (2 ^ n) : Finset Nat) := by
  intro y hy y' hy' h
  rw [← ofWord_toWord (mem_range.mp hy), h, ofWord_toWord (mem_range.mp hy')]

private theorem card_words (n : Nat) : #(words n) = 2 ^ n := by
  rw [words, card_image_of_injOn (toWord_injOn n), card_range]

private theorem sum_toWord {X : Type*} [AddCommMonoid X] (n : Nat) (G : List Bool → X) :
    ∑ y ∈ range (2 ^ n), G (toWord n y) = ∑ w ∈ words n, G w :=
  (sum_image (toWord_injOn n)).symm

private theorem sum_counter_bitVec {X : Type*} [AddCommMonoid X] (n : Nat)
    (G : List Bool → X) :
    ∑ y ∈ range (2 ^ n), G (toWord n y) = ∑ x : BitVec n, G x.toBoolListLE := by
  refine Finset.sum_bij (fun y _ => BitVec.ofNat n y) (fun _ _ => Finset.mem_univ _)
    (fun y hy y' hy' h => ?_) (fun x _ => ?_) (fun y hy => ?_)
  · have h' := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (mem_range.mp hy),
      Nat.mod_eq_of_lt (mem_range.mp hy')] using h'
  · exact ⟨x.toNat, mem_range.mpr x.isLt, by
      apply BitVec.eq_of_toNat_eq
      simp⟩
  · simp [toWord_eq_toBoolListLE]

private theorem sum_bitVec_boolList {X : Type*} [AddCommMonoid X] (n : Nat)
    (G : List Bool → X) :
    ∑ x : BitVec n, G x.toBoolListLE =
      ∑ w : {w : List Bool // w.length = n}, G w := by
  apply Fintype.sum_equiv (BitVec.equivBoolListLE n)
  intro x
  rfl

example : toWord 0 37 = [] := by decide
example : ofWord [] = 0 := by decide
example : (BitVec.ofNat 0 37).toBoolListLE = [] := by decide

example : toWord 3 3 = [true, true, false] := by decide
example : ofWord [true, true, false] = 3 := by decide
example : ofWord [true, false, false] = 1 := by decide
example : toWord 3 1 = [true, false, false] := by decide
example : toWord 3 14 = [false, true, true] := by decide
example : ofWord (toWord 3 14) = 6 := by decide

example {n y : Nat} (h : y < 2 ^ n) : ofWord (toWord n y) = y :=
  ofWord_toWord h

example (w : List Bool) : toWord w.length (ofWord w) = w :=
  toWord_ofWord w

example : #(words 3) = 8 := by simpa using card_words 3
example : Fintype.card {w : List Bool // w.length = 3} = 8 := by
  simp

example : (∑ y ∈ range (2 ^ 3), ofWord (toWord 3 y)) = 28 := by decide

example : (∑ w ∈ words 3, ofWord w) = 28 := by
  rw [← sum_toWord]
  decide

example : (∑ x : BitVec 3, x.toNat) = 28 := by decide

example : (∑ w : {w : List Bool // w.length = 3}, ofWord w) = 28 := by
  rw [← sum_bitVec_boolList]
  change (∑ x : BitVec 3, (BitVec.ofBoolListLE x.toBoolListLE).toNat) = 28
  simp
  decide

example (G : List Bool → Int) :
    ∑ y ∈ range (2 ^ 3), G (toWord 3 y) =
      ∑ x : BitVec 3, G x.toBoolListLE :=
  sum_counter_bitVec 3 G

example (G : List Bool → Int) :
    ∑ x : BitVec 3, G x.toBoolListLE =
      ∑ w : {w : List Bool // w.length = 3}, G w :=
  sum_bitVec_boolList 3 G

example (G : List Bool → Int) :
    ∑ y ∈ range (2 ^ 3), G (toWord 3 y) = ∑ w ∈ words 3, G w :=
  sum_toWord 3 G

end ETHBoolWordReference

#print axioms BitVec.toBoolListLE
#print axioms BitVec.length_toBoolListLE
#print axioms BitVec.getElem_toBoolListLE
#print axioms BitVec.getD_toBoolListLE
#print axioms BitVec.equivBoolListLE
#print axioms BitVec.toNat_ofBoolListLE_toBoolListLE
#print axioms BitVec.instFinEnumSubtypeListBoolEqNatLength_mathlibExt
#print axioms BitVec.card_boolListLE
