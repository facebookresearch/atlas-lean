/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Octonion.StructureConstants

open Finset

namespace Octonion

private abbrev e (i : Nat) : BitVec 3 := BitVec.ofNat 3 i

/-! The orientation agrees with the source's little-endian coordinates. -/

example : basisSign (e 1) (e 2) = -1 := by decide

example : basisSign (e 2) (e 1) = 1 := by decide

example : (e 1) ^^^ (e 2) = e 3 := by decide

example : structureConstant (e 1) (e 2) (e 3) = -1 := by decide

example : structureConstant (e 2) (e 1) (e 3) = 1 := by decide

example : ∀ p : BitVec 3, p ≠ e 0 → basisSign p p = -1 := by decide

example : ∀ p : BitVec 3, p ≠ e 0 → structureConstant p p (e 0) = -1 := by decide

example : ∀ p : BitVec 3, basisSign (e 0) p = 1 ∧ basisSign p (e 0) = 1 := by decide

example : ∀ p : BitVec 3,
    structureConstant (e 0) p p = 1 ∧ structureConstant p (e 0) p = 1 := by decide

example (p q : BitVec 3) : basisSign p q * basisSign p q = 1 :=
  basisSign_mul_self p q

example (p q p' q' : BitVec 3) (hxor : p ^^^ q = p' ^^^ q') (hne : q ≠ q') :
    basisSign p q * basisSign p' q' + basisSign p q' * basisSign p' q = 0 :=
  basisSign_mul_add_swap hxor hne

example (p q p' q' : BitVec 3) :
    (∑ k : BitVec 3, structureConstant p q k * structureConstant p' q' k) =
      (if p ^^^ q = p' ^^^ q' then basisSign p q * basisSign p' q' else 0) :=
  sum_structureConstant_mul p q p' q'

/-! Diagonal, equal-xor off-diagonal, and unequal-xor crossing cases. -/

example :
    (∑ k : BitVec 3, structureConstant (e 1) (e 2) k *
      structureConstant (e 1) (e 2) k) +
    (∑ k : BitVec 3, structureConstant (e 1) (e 2) k *
      structureConstant (e 1) (e 2) k) = 2 := by decide

example :
    (∑ k : BitVec 3, structureConstant (e 1) (e 2) k *
      structureConstant (e 2) (e 1) k) +
    (∑ k : BitVec 3, structureConstant (e 1) (e 1) k *
      structureConstant (e 2) (e 2) k) = 0 := by decide

example :
    (∑ k : BitVec 3, structureConstant (e 1) (e 2) k *
      structureConstant (e 4) (e 1) k) +
    (∑ k : BitVec 3, structureConstant (e 1) (e 1) k *
      structureConstant (e 4) (e 2) k) = 0 := by decide

example (x y u v : BitVec 3) :
    (∑ k : BitVec 3, structureConstant x y k * structureConstant v u k) +
      (∑ k : BitVec 3, structureConstant x u k * structureConstant v y k) =
        2 * (if x = v ∧ y = u then 1 else 0) :=
  crossing_identity x y u v

/-! Both public bounds are sharp. -/

example (p q k : BitVec 3) : abs (structureConstant p q k) ≤ 1 :=
  abs_structureConstant_le_one p q k

example : abs (structureConstant (e 1) (e 2) (e 3)) = 1 := by decide

example (p q p' q' : BitVec 3) :
    abs (∑ k : BitVec 3, structureConstant p q k * structureConstant p' q' k) ≤ 1 :=
  abs_sum_structureConstant_mul_le_one p q p' q'

example :
    abs (∑ k : BitVec 3, structureConstant (e 1) (e 2) k *
      structureConstant (e 1) (e 2) k) = 1 := by decide

/-! A dense integer-vector product, independent of the basis-vector checks above. -/

private def leftVector (p : BitVec 3) : Int :=
  match p.toNat with
  | 0 => 2 | 1 => -1 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 4 | 6 => -2 | _ => 5

private def rightVector (q : BitVec 3) : Int :=
  match q.toNat with
  | 0 => -3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => -1 | 6 => 5 | _ => 2

private def productVector (k : BitVec 3) : Int :=
  ∑ p : BitVec 3, ∑ q : BitVec 3, structureConstant p q k * leftVector p * rightVector q

example :
    productVector (e 0) = -3 ∧ productVector (e 1) = -33 ∧
    productVector (e 2) = -29 ∧ productVector (e 3) = 31 ∧
    productVector (e 4) = -13 ∧ productVector (e 5) = -19 ∧
    productVector (e 6) = 13 ∧ productVector (e 7) = -1 := by decide

example :
    (∑ k : BitVec 3, productVector k * productVector k) =
      (∑ p : BitVec 3, leftVector p * leftVector p) *
        ∑ q : BitVec 3, rightVector q * rightVector q := by decide

#print axioms basisSign_mul_self
#print axioms basisSign_mul_add_swap
#print axioms sum_structureConstant_mul
#print axioms crossing_identity
#print axioms abs_structureConstant_le_one
#print axioms abs_sum_structureConstant_mul_le_one

end Octonion
