/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Selection.HireAssistant

/-! Ordinary-import hiring contracts and named helper privacy. -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

#check @hireAssistant
#check @hireAssistant_ret
#check @hireAssistant_hires
#check @hireAssistant_time
#check @hireAssistant_nil
#check @hireAssistant_singleton
#check @hireAssistant_hire_bounds
#check @hireAssistant_increasing

example {α : Type (u + 1)} [LinearOrder α] (xs : List α) :
    TimeM (Nat × Nat) (Option Nat × List Nat) := hireAssistant xs

example {α : Type u} [LinearOrder α] (xs : List α) :
    (hireAssistant xs).ret.1 = xs.maxIdxOn? id := hireAssistant_ret xs

example {α : Type u} [LinearOrder α] (xs : List α) :
    (hireAssistant xs).ret.2 =
      (xs.zipIdx.filter (fun p => (xs.take p.2).all (fun a => decide (a < p.1)))).map
        Prod.snd := hireAssistant_hires xs

example {α : Type u} [LinearOrder α] (xs : List α) :
    (hireAssistant xs).time = (xs.length, (hireAssistant xs).ret.2.length) :=
  hireAssistant_time xs

example {α : Type (u + 1)} [LinearOrder α] :
    hireAssistant ([] : List α) = ⟨(none, []), (0, 0)⟩ := hireAssistant_nil

example {α : Type u} [LinearOrder α] (a : α) :
    hireAssistant [a] = ⟨(some 0, [0]), (1, 1)⟩ := hireAssistant_singleton a

example {α : Type u} [LinearOrder α] (xs : List α) (h : xs ≠ []) :
    1 ≤ (hireAssistant xs).time.2 ∧ (hireAssistant xs).time.2 ≤ xs.length :=
  hireAssistant_hire_bounds xs h

example {α : Type u} [LinearOrder α] (xs : List α) (h : xs.Pairwise (· < ·)) :
    (hireAssistant xs).ret.2 = List.range xs.length ∧
      (hireAssistant xs).time = (xs.length, xs.length) := hireAssistant_increasing xs h

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check interview

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check fold_manager

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check records

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check fold_history

end Cslib.Algorithms.Lean.TimeM
