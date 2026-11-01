/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
bridge fixed-width little-endian Boolean lists to Lean's canonical `BitVec` representation,
with an equivalence and finite enumeration.
-/
module

public import Mathlib.Data.FinEnum

/-! # Little-endian Boolean lists and bitvectors

Adapted from the fixed-width Boolean words in
`eth/proof/machines/StepMachines/Prog/Chunks.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace BitVec

/-- The bits of a bitvector in little-endian order, least significant bit first. -/
def toBoolListLE {n : Nat} (x : BitVec n) : List Bool :=
  List.ofFn fun i : Fin n => x.getLsbD i

@[simp] theorem length_toBoolListLE {n : Nat} (x : BitVec n) : x.toBoolListLE.length = n := by
  simp [toBoolListLE]

@[simp] theorem getElem_toBoolListLE {n i : Nat} (x : BitVec n)
    (h : i < x.toBoolListLE.length) : x.toBoolListLE[i] = x.getLsbD i := by
  simpa only [toBoolListLE] using
    (List.getElem_ofFn (f := fun j : Fin n => x.getLsbD j) (i := i) (by simpa using h))

@[simp] theorem getD_toBoolListLE {n i : Nat} (x : BitVec n) :
    x.toBoolListLE.getD i false = x.getLsbD i := by
  by_cases h : i < n
  · simp [toBoolListLE, h]
  · simp [toBoolListLE, h, BitVec.getLsbD_of_ge x i (Nat.le_of_not_gt h)]

/-- Fixed-width little-endian Boolean lists are equivalent to bitvectors of the same width. -/
def equivBoolListLE (n : Nat) : BitVec n ≃ {w : List Bool // w.length = n} where
  toFun x := ⟨x.toBoolListLE, x.length_toBoolListLE⟩
  invFun w := (BitVec.ofBoolListLE w).cast w.property
  left_inv x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, getD_toBoolListLE]
  right_inv w := by
    rcases w with ⟨w, rfl⟩
    apply Subtype.ext
    change List.ofFn (fun i : Fin w.length => (BitVec.ofBoolListLE w).getLsbD i) = w
    conv_rhs => rw [← List.ofFn_getElem (xs := w)]
    apply congrArg List.ofFn
    funext i
    rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem i.isLt]
    rfl

@[simp] theorem toNat_ofBoolListLE_toBoolListLE {n : Nat} (x : BitVec n) :
    (BitVec.ofBoolListLE x.toBoolListLE).toNat = x.toNat := by
  have h := congrArg BitVec.toNat ((equivBoolListLE n).left_inv x)
  simpa [equivBoolListLE] using h

/-- Fixed-width little-endian Boolean lists inherit the canonical finite enumeration of
bitvectors. -/
instance (n : Nat) : FinEnum {w : List Bool // w.length = n} :=
  FinEnum.ofEquiv (BitVec n) (equivBoolListLE n).symm

@[simp] theorem card_boolListLE (n : Nat) :
    Fintype.card {w : List Bool // w.length = n} = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard]
  rfl

end BitVec
