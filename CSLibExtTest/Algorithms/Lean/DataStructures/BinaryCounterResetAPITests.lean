/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryCounter

set_option autoImplicit false

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BinaryCounter

example {k : Nat} (bits : Vector Bool k) : TimeM Nat (Vector Bool k) :=
  reset bits

example {k : Nat} (bits : Vector Bool k) :
    (reset bits).ret.toList = List.replicate k false :=
  reset_toList bits

example {k : Nat} (bits : Vector Bool k) :
    (BitVec.ofBoolListLE (reset bits).ret.toList).toNat = 0 :=
  reset_value bits

example {k : Nat} (bits : Vector Bool k) :
    (reset bits).time = (bits.toList.map Bool.toNat).sum :=
  reset_time bits

example {k : Nat} (bits : Vector Bool k) :
    (reset bits).time = ((List.range k).map fun i =>
      if bits.toList.getD i false ≠ (reset bits).ret.toList.getD i false
      then 1 else 0).sum :=
  reset_time_changes bits

example {k : Nat} (bits : Vector Bool k) : (reset bits).time ≤ k :=
  reset_time_le bits

example (bits : Vector Bool 0) : (reset bits).time = 0 :=
  reset_time_zero_width bits

example (k : Nat) : (reset (Vector.replicate k false)).time = 0 :=
  reset_time_replicate_false k

example {k : Nat} (bits : Vector Bool k) :
    (reset (reset bits).ret).ret = (reset bits).ret :=
  reset_ret_idempotent bits

example {k : Nat} (bits : Vector Bool k) :
    (reset (reset bits).ret).time = 0 :=
  reset_time_after_reset bits

example {k : Nat} (bits : Vector Bool k) :
    (reset bits).time + ((reset bits).ret.toList.map Bool.toNat).sum =
      (bits.toList.map Bool.toNat).sum :=
  reset_potential bits

#print axioms reset_toList
#print axioms reset_value
#print axioms reset_time
#print axioms reset_time_changes
#print axioms reset_time_le
#print axioms reset_time_zero_width
#print axioms reset_time_replicate_false
#print axioms reset_ret_idempotent
#print axioms reset_time_after_reset
#print axioms reset_potential
