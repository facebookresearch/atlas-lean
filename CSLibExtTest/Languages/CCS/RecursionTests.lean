/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `9db2af32bec4c1fe1731f17c030e9410961257ed`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Tests for recursive CCS
-/
module

public import CSLibExt.Languages.CCS.RecursiveLaws

@[expose] public section

namespace CslibTest.CCS.Recursion

open Cslib.CCS Cslib.CCS.Recursive Cslib.CCS.Recursive.Process

inductive Channel where
  | coin
  | coffee
  | tea
  deriving DecidableEq

inductive Constant where
  | machine
  | coffeeServer
  | teaServer
  deriving DecidableEq

abbrev P := Process Channel Constant

/-- A machine repeatedly accepts a coin and then offers coffee or tea. -/
def specification : Specification Channel Constant
  | .machine => .prefix (.input .coin)
      (.choice
        (.prefix (.output .coffee) (.constant .machine))
        (.prefix (.output .tea) (.constant .machine)))
  | .coffeeServer =>
      .prefix (.input .coffee) (.prefix .tau (.constant .coffeeServer))
  | .teaServer =>
      .prefix (.input .tea) (.prefix .tau (.constant .teaServer))

example : Specification.Guarded specification := by
  intro constant
  cases constant <;> simp [specification, Guarded, GuardedUnder]

example :
    Step specification (.constant .machine) (.input .coin)
      (.choice
        (.prefix (.output .coffee) (.constant .machine))
        (.prefix (.output .tea) (.constant .machine))) := by
  apply Step.unfold
  exact .prefix _ _

example {action : Label Channel} {next : P} :
    Step specification (.constant .machine) action next ↔
      action = .input .coin ∧
      next = .choice
        (.prefix (.output .coffee) (.constant .machine))
        (.prefix (.output .tea) (.constant .machine)) := by
  simp [constant_step_iff, prefix_step_iff, specification]

example :
    (lts specification).HomBisimilarity (.constant .machine) (specification .machine) :=
  constant_unfold Constant.machine

example :
    (lts specification).HomBisimilarity
      (.choice (.constant .coffeeServer) (.constant .teaServer))
      (.choice (.constant .teaServer) (.constant .coffeeServer)) :=
  choice_comm _ _

example :
    (lts specification).HomBisimilarity
      (.parallel (.constant .coffeeServer) .nil)
      (.constant .coffeeServer) :=
  parallel_nil_right _

example :
    (lts specification).HomBisimilarity
      (.parallel (.constant .coffeeServer) (.constant .teaServer))
      (.parallel (.constant .teaServer) (.constant .coffeeServer)) :=
  parallel_comm _ _

example :
    constants (specification .machine) = [.machine] := by
  simp [specification, constants, constantOccurrences]

example : Constant.coffeeServer ∈
    constants (.parallel (.constant .coffeeServer) (.constant .teaServer) : P) := by
  simp

example : Constant.machine ∈
    constants (.restriction [.coin]
      (.choice (.constant .machine) (.constant .coffeeServer)) : P) := by
  simp

example : Constant.teaServer ∈
    constants (.relabelling ⟨[]⟩ (.constant .teaServer) : P) := by
  simp

end CslibTest.CCS.Recursion
