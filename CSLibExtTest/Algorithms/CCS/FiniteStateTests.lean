/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.CCS.FiniteState

/-!
# Tests for finite-state CCS agents and certificates

* `Y = a.τ.b.Y` is weakly bisimilar, indeed observation congruent, to
  `X = a.b.X`, by a three-pair certificate in which the silent step of `Y` is
  absorbed by staying put (forward) and by a ranked silent detour (backward).
* The certificate check rejects a relation that relates `X` to the wrong state
  of `Y`, and a list order that breaks the ranking.
* `sumOf`, `parSteps` and `restrictSteps` compute the expected transitions.
-/

@[expose] public section

namespace Cslib.Algorithms.CCS.FiniteStateTests

open Cslib.CCS (Label)
open Cslib.CCS.Recursive Cslib.LTS

inductive N | a | b
  deriving DecidableEq

/-- States of `Y = a.τ.b.Y`. -/
inductive Y | y0 | y1 | y2
  deriving DecidableEq

def ySteps : Y → List (Label N × Y)
  | .y0 => [(.input .a, .y1)]
  | .y1 => [(.tau, .y2)]
  | .y2 => [(.output .b, .y0)]

/-- States of `X = a.b.X`. -/
def xSteps : Bool → List (Label N × Bool)
  | false => [(.input .a, true)]
  | true => [(.output .b, false)]

inductive K
  | x (s : Bool)
  | y (s : Y)

def spec : Specification N K
  | .x s => sumOf ((xSteps s).map fun p => (p.1, .constant (.x p.2)))
  | .y s => sumOf ((ySteps s).map fun p => (p.1, .constant (.y p.2)))

theorem realizes_y : Realizes spec (fun s => .constant (K.y s)) ySteps :=
  Realizes.constant K.y ySteps fun _ => rfl

theorem realizes_x : Realizes spec (fun s => .constant (K.x s)) xSteps :=
  Realizes.constant K.x xSteps fun _ => rfl

/-- The certificate: `(y1, true)` comes after `(y2, true)`, its silent
successor. -/
def cert : List (Y × Bool) := [(.y0, false), (.y2, true), (.y1, true)]

example : certCheck ySteps xSteps cert = true := by decide

example : (Process.lts spec).HomWeakBisimilarity
    (.constant (.y .y0)) (.constant (.x false)) :=
  weaklyBisimilar_of_certCheck realizes_y realizes_x (rel := cert) (by decide) (x := .y0)
    (y := false)
    (by decide)

example : (Process.lts spec).RootedWeaklyBisimilar
    (.constant (.y .y0)) (.constant (.x false)) :=
  rootedWeaklyBisimilar_of_certCheck realizes_y realizes_x (rel := cert) (by decide) (x := .y0)
    (y := false)
    (by decide)

/-- Relating `y2` to the state that must perform `a` is rejected. -/
example : certCheck ySteps xSteps [(.y0, false), (.y2, false), (.y1, true)] = false := by
  decide

/-- Listing `y1` before its silent successor breaks the ranking, and the
backward check fails. -/
example : certCheck ySteps xSteps [(.y0, false), (.y1, true), (.y2, true)] = false := by
  decide

/-- `sumOf` lists the transitions of a choice of prefixes. -/
example : Process.Step spec (sumOf [(.input .a, .nil), (.output .b, .nil)]) (.output .b) .nil :=
  (step_sumOf_iff _ _ _).2 (by simp)

/-- Parallel composition of `Y` in state `y2` (offering the output `b`) with
`X` in state `false` (offering the input `a`): two interleavings and no
synchronization. -/
example : parSteps ySteps xSteps (.y2, false) =
    [(.output .b, (.y0, false)), (.input .a, (.y2, true))] := by decide

/-- An input meeting the complementary output: both interleavings and a
synchronization into `τ`. -/
example : parSteps (fun _ : Unit => [((.input .a : Label N), ())])
    (fun _ : Unit => [((.output .a : Label N), ())]) ((), ()) =
    [(.input .a, ((), ())), (.output .a, ((), ())), (.tau, ((), ()))] := by decide

/-- Restriction removes the blocked visible labels and keeps `τ`. -/
example : restrictSteps [N.a] (fun _ : Unit =>
    [((.input .a : Label N), ()), (.output .b, ()), (.tau, ())]) () =
    [(.output .b, ()), (.tau, ())] := by decide

end Cslib.Algorithms.CCS.FiniteStateTests
