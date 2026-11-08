/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryCounter

/-!
# Binary counter public trust inventory

Ordinary importing checks for the three public executors and twenty-two public
theorems. The axiom output is checked against the named inventory by the gate.
-/

set_option autoImplicit false

#check @Cslib.Algorithms.Lean.BinaryCounter.increment
#check @Cslib.Algorithms.Lean.BinaryCounter.increment_value
#check @Cslib.Algorithms.Lean.BinaryCounter.increment_time
#check @Cslib.Algorithms.Lean.BinaryCounter.increment_time_le
#check @Cslib.Algorithms.Lean.BinaryCounter.run
#check @Cslib.Algorithms.Lean.BinaryCounter.run_zero
#check @Cslib.Algorithms.Lean.BinaryCounter.run_ret_succ
#check @Cslib.Algorithms.Lean.BinaryCounter.run_time_succ
#check @Cslib.Algorithms.Lean.BinaryCounter.run_value
#check @Cslib.Algorithms.Lean.BinaryCounter.run_bit_flips
#check @Cslib.Algorithms.Lean.BinaryCounter.increment_time_replicate_true
#check @Cslib.Algorithms.Lean.BinaryCounter.run_time_eq
#check @Cslib.Algorithms.Lean.BinaryCounter.run_time_lt
#check @Cslib.Algorithms.Lean.BinaryCounter.run_time_ge
#check @Cslib.Algorithms.Lean.BinaryCounter.reset
#check @Cslib.Algorithms.Lean.BinaryCounter.reset_toList
#check @Cslib.Algorithms.Lean.BinaryCounter.reset_value
#check @Cslib.Algorithms.Lean.BinaryCounter.reset_time
#check @Cslib.Algorithms.Lean.BinaryCounter.reset_time_changes
#check @Cslib.Algorithms.Lean.BinaryCounter.reset_time_le
#check @Cslib.Algorithms.Lean.BinaryCounter.reset_time_zero_width
#check @Cslib.Algorithms.Lean.BinaryCounter.reset_time_replicate_false
#check @Cslib.Algorithms.Lean.BinaryCounter.reset_ret_idempotent
#check @Cslib.Algorithms.Lean.BinaryCounter.reset_time_after_reset
#check @Cslib.Algorithms.Lean.BinaryCounter.reset_potential

#print axioms Cslib.Algorithms.Lean.BinaryCounter.increment_value
#print axioms Cslib.Algorithms.Lean.BinaryCounter.increment_time
#print axioms Cslib.Algorithms.Lean.BinaryCounter.increment_time_le
#print axioms Cslib.Algorithms.Lean.BinaryCounter.run_zero
#print axioms Cslib.Algorithms.Lean.BinaryCounter.run_ret_succ
#print axioms Cslib.Algorithms.Lean.BinaryCounter.run_time_succ
#print axioms Cslib.Algorithms.Lean.BinaryCounter.run_value
#print axioms Cslib.Algorithms.Lean.BinaryCounter.run_bit_flips
#print axioms Cslib.Algorithms.Lean.BinaryCounter.increment_time_replicate_true
#print axioms Cslib.Algorithms.Lean.BinaryCounter.run_time_eq
#print axioms Cslib.Algorithms.Lean.BinaryCounter.run_time_lt
#print axioms Cslib.Algorithms.Lean.BinaryCounter.run_time_ge
#print axioms Cslib.Algorithms.Lean.BinaryCounter.reset_toList
#print axioms Cslib.Algorithms.Lean.BinaryCounter.reset_value
#print axioms Cslib.Algorithms.Lean.BinaryCounter.reset_time
#print axioms Cslib.Algorithms.Lean.BinaryCounter.reset_time_changes
#print axioms Cslib.Algorithms.Lean.BinaryCounter.reset_time_le
#print axioms Cslib.Algorithms.Lean.BinaryCounter.reset_time_zero_width
#print axioms Cslib.Algorithms.Lean.BinaryCounter.reset_time_replicate_false
#print axioms Cslib.Algorithms.Lean.BinaryCounter.reset_ret_idempotent
#print axioms Cslib.Algorithms.Lean.BinaryCounter.reset_time_after_reset
#print axioms Cslib.Algorithms.Lean.BinaryCounter.reset_potential
