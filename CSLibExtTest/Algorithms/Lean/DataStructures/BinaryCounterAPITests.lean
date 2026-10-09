/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryCounter

/-! # Ordinary-import consumers of all fourteen binary-counter public roles -/

set_option autoImplicit false

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BinaryCounter

public section

#check @increment
#check @increment_value
#check @increment_time
#check @increment_time_le
#check @increment_time_replicate_true
#check @run
#check @run_zero
#check @run_ret_succ
#check @run_time_succ
#check @run_value
#check @run_bit_flips
#check @run_time_eq
#check @run_time_lt
#check @run_time_ge

example {k : Nat} (bits : Vector Bool k) : TimeM Nat (Vector Bool k) := increment bits

example {k : Nat} (bits : Vector Bool k) :
    (BitVec.ofBoolListLE (increment bits).ret.toList).toNat =
      ((BitVec.ofBoolListLE bits.toList).toNat + 1) % 2 ^ k := increment_value bits

example {k : Nat} (bits : Vector Bool k) :
    (increment bits).time = (bits.toList.takeWhile id).length +
      if (bits.toList.takeWhile id).length < k then 1 else 0 := increment_time bits

example {k : Nat} (bits : Vector Bool k) : (increment bits).time ≤ k :=
  increment_time_le bits

example (k : Nat) : (increment (Vector.replicate k true)).time = k :=
  increment_time_replicate_true k

example {k : Nat} (bits : Vector Bool k) (n : Nat) : TimeM Nat (Vector Bool k) := run bits n

example {k : Nat} (bits : Vector Bool k) : run bits 0 = pure bits := run_zero bits

example {k : Nat} (bits : Vector Bool k) (n : Nat) :
    (run bits (n + 1)).ret = (increment (run bits n).ret).ret := run_ret_succ bits n

example {k : Nat} (bits : Vector Bool k) (n : Nat) :
    (run bits (n + 1)).time =
      (run bits n).time + (increment (run bits n).ret).time := run_time_succ bits n

example {k : Nat} (bits : Vector Bool k) (n : Nat) :
    (BitVec.ofBoolListLE (run bits n).ret.toList).toNat =
      ((BitVec.ofBoolListLE bits.toList).toNat + n) % 2 ^ k := run_value bits n

example (k i n : Nat) (hi : i < k) :
    ((List.range n).map fun t =>
      if (run (Vector.replicate k false) t).ret.toList.getD i false ≠
          (run (Vector.replicate k false) (t + 1)).ret.toList.getD i false
        then 1 else 0).sum = n / 2 ^ i := run_bit_flips k i n hi

example (k n : Nat) :
    (run (Vector.replicate k false) n).time =
      ((List.range k).map fun i => n / 2 ^ i).sum := run_time_eq k n

example (k n : Nat) (hn : 0 < n) :
    (run (Vector.replicate k false) n).time < 2 * n := run_time_lt k n hn

example (k n : Nat) (hk : 0 < k) :
    n ≤ (run (Vector.replicate k false) n).time := run_time_ge k n hk

example : (run (Vector.replicate 0 false) 100).time = 0 := by
  simpa using run_time_eq 0 100

example : (increment (Vector.replicate 3 true)).time = 3 :=
  increment_time_replicate_true 3

example : (run (Vector.replicate 8 false) 16).time < 32 := run_time_lt 8 16 (by decide)
