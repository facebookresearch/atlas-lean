/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Data.Bool.Count
import Init.Data.BitVec.Basic

@[expose] public section

@[no_expose] private def emptyBits : List Bool := []

@[no_expose] private def falseBits : List Bool := [false, false, false]

@[no_expose] private def trueBits : List Bool := [true, true, true]

@[no_expose] private def mixedBits : List Bool := [true, false, true]

example : (emptyBits.map Bool.toNat).sum = 0 := by decide
example : emptyBits.count true = 0 := by decide

example : (([false] : List Bool).map Bool.toNat).sum = 0 := by decide
example : ([false] : List Bool).count true = 0 := by decide
example : (([true] : List Bool).map Bool.toNat).sum = 1 := by decide
example : ([true] : List Bool).count true = 1 := by decide

example : (falseBits.map Bool.toNat).sum = 0 := by decide
example : falseBits.count true = 0 := by decide
example : (trueBits.map Bool.toNat).sum = 3 := by decide
example : trueBits.count true = 3 := by decide

example : (mixedBits.map Bool.toNat).sum = 2 := by decide
example : mixedBits.count true = 2 := by decide
example : (BitVec.ofBoolListLE mixedBits).toNat = 5 := by decide

example : (mixedBits.map Bool.toNat).sum = mixedBits.count true :=
  List.sum_map_toNat_eq_count_true mixedBits

example (bits : List Bool) (resetCost : Nat)
    (hcost : resetCost = (bits.map Bool.toNat).sum) :
    resetCost = bits.count true := by
  rw [hcost, List.sum_map_toNat_eq_count_true]
