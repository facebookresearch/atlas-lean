/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Byzantine.OralMessages
public meta import CSLibExt.Computability.Distributed.Byzantine.OralMessages
public meta import Mathlib.Data.Fintype.Defs

/-!
# Tests for the oral messages algorithm

Concrete runs of `om` with the orders `retreat` (the default), `attack` and `hold`:

* Four generals `Fin 4`, one traitor, `OM(1)`: a traitorous commander that sends a different
  order to each lieutenant (they all retreat), or `attack` to two lieutenants and `retreat` to
  the third (they all attack); a loyal commander ordering `attack` with a traitorous lieutenant
  that lies to everybody, the same lie or different ones (the loyal lieutenants attack).
* `OM(0)` with one traitor among four generals: agreement fails.
* Seven generals `Fin 7`, two traitors, `OM(2)`, with traitors whose lies depend on the relay
  path: agreement (traitorous commander) and validity (loyal commander).
* Three generals `Fin 3`, one traitor, `OM(1)`: validity fails, so the bound `3 m < n` matters.
* The main theorems, instantiated for four generals and one traitor.
-/

@[expose] public section

namespace Cslib.Distributed.Byzantine.Tests

open Cslib.Distributed.Byzantine.OralMessages

/-- Orders a commander can give. -/
inductive Order where
  /-- Retreat, the default order, taken when there is no majority. -/
  | retreat
  /-- Attack. -/
  | attack
  /-- Hold the position. -/
  | hold
  deriving DecidableEq, Repr

/-- The default order is `retreat`. -/
instance : Inhabited Order := ⟨.retreat⟩

/-- The lieutenants of commander `0` among four generals. -/
abbrev lieutenants : Finset (Fin 4) := Finset.univ.erase 0

/-- A traitorous commander that sends `attack` to lieutenant `1`, `retreat` to `2` and `hold`
to `3`. -/
def splitThree : List (Fin 4) → Fin 4 → Order :=
  fun _ r ↦ if r = 1 then .attack else if r = 2 then .retreat else .hold

/-- A traitorous commander that sends `attack` to lieutenants `1` and `2`, `retreat` to `3`. -/
def splitTwo : List (Fin 4) → Fin 4 → Order :=
  fun _ r ↦ if r = 3 then .retreat else .attack

/-- A traitor that relays `retreat` to everybody. -/
def alwaysRetreat : List (Fin 4) → Fin 4 → Order := fun _ _ ↦ .retreat

/-- A traitor that relays `retreat` to `1` and `hold` to everybody else. -/
def mixedLies : List (Fin 4) → Fin 4 → Order :=
  fun _ r ↦ if r = 1 then .retreat else .hold

-- Commander `0` is the traitor and sends three different orders: no lieutenant sees a
-- majority, so all of them retreat (and agree).
#guard (List.map (om (· ≠ 0) splitThree 1 0 lieutenants .attack []) [1, 2, 3]) =
  [.retreat, .retreat, .retreat]

-- Commander `0` is the traitor and sends `attack` to two lieutenants: all of them attack.
#guard (List.map (om (· ≠ 0) splitTwo 1 0 lieutenants .retreat []) [1, 2, 3]) =
  [.attack, .attack, .attack]

-- Commander `0` is loyal and orders `attack`; lieutenant `3` is the traitor and relays
-- `retreat` to everybody: the loyal lieutenants `1` and `2` attack.
#guard (List.map (om (· ≠ 3) alwaysRetreat 1 0 lieutenants .attack []) [1, 2]) =
  [.attack, .attack]

-- Lieutenant `3` tells different lies to `1` and `2`: they still attack.
#guard (List.map (om (· ≠ 3) mixedLies 1 0 lieutenants .attack []) [1, 2]) =
  [.attack, .attack]

-- `OM(0)` with the traitorous commander: lieutenants `1` and `2` take the orders they
-- received and disagree.
#guard om (· ≠ 0) splitThree 0 0 lieutenants .attack [] 1 = .attack
#guard om (· ≠ 0) splitThree 0 0 lieutenants .attack [] 2 = .retreat

-- Three generals, `OM(1)`: commander `0` is loyal and orders `attack`, lieutenant `2` is the
-- traitor and relays `retreat`. Lieutenant `1` sees `attack` and `retreat` once each, so
-- there is no majority and it retreats: validity fails.
#guard om (· ≠ (2 : Fin 3)) (fun _ _ ↦ Order.retreat) 1 0 (Finset.univ.erase 0) .attack [] 1 =
  .retreat

/-! ### Two traitors among seven generals, `OM(2)` -/

/-- The lieutenants of commander `0` among seven generals. -/
abbrev lieutenants7 : Finset (Fin 7) := Finset.univ.erase 0

/-- Traitors whose lies depend on the relay path: by the parity of its length and of the
recipient. -/
def pathLies : List (Fin 7) → Fin 7 → Order := fun σ r ↦
  if σ.length % 2 = 0 then (if r.val % 2 = 0 then .attack else .hold)
  else if r.val % 3 = 0 then .retreat else .attack

/-- The decisions of the lieutenants `1, …, 6` under `OM(2)` with commander `0`, order
`attack`, the given traitors and the path-dependent adversary. -/
def decisions7 (traitor : Fin 7 → Bool) : List Order :=
  [1, 2, 3, 4, 5, 6].map (om (fun g ↦ traitor g = false) pathLies 2 0 lieutenants7 .attack [])

/-- The decisions of the loyal lieutenants. -/
def loyalDecisions7 (traitor : Fin 7 → Bool) : List Order :=
  (([1, 2, 3, 4, 5, 6] : List (Fin 7)).filter (traitor · = false)).map
    (om (fun g ↦ traitor g = false) pathLies 2 0 lieutenants7 .attack [])

-- Traitors `0` (the commander) and `3`: the loyal lieutenants agree.
#guard let d := loyalDecisions7 (fun g ↦ g = 0 || g = 3); d.all (· == d.headD .retreat)

-- Traitors `3` and `5`, loyal commander ordering `attack`: the loyal lieutenants attack.
#guard (loyalDecisions7 (fun g ↦ g = 3 || g = 5)).all (· == .attack)

-- Traitors `2` and `5`: the loyal lieutenants attack, while the traitors' own entries need not.
#guard (loyalDecisions7 (fun g ↦ g = 2 || g = 5)).all (· == .attack)

/-- With the commander splitting three ways, no order fills more than half of what lieutenant `1`
sees, so it retreats by `majority_eq_default`. -/
example : majority ({.attack, .retreat, .hold} : Multiset Order) = .retreat :=
  majority_eq_default fun x ↦ by cases x <;> decide

/-- The `OM(1)` run with the commander splitting three ways, checked by the kernel. -/
example : om (· ≠ 0) splitThree 1 0 lieutenants .attack [] 1 = .retreat := by decide

/-- The `OM(0)` run disagrees, checked by the kernel. -/
example : om (· ≠ 0) splitThree 0 0 lieutenants .attack [] 1 ≠
    om (· ≠ 0) splitThree 0 0 lieutenants .attack [] 2 := by decide

/-- Agreement for four generals with at most one traitor, for every adversary and order. -/
example (loyal : Fin 4 → Prop) [DecidablePred loyal] (adv : List (Fin 4) → Fin 4 → Order)
    (v : Order) (h : (Finset.univ.filter (¬ loyal ·)).card ≤ 1) {p p' : Fin 4} (hp : p ≠ 0)
    (hp' : p' ≠ 0) (hpl : loyal p) (hpl' : loyal p') :
    om loyal adv 1 0 lieutenants v [] p = om loyal adv 1 0 lieutenants v [] p' :=
  (byzantine_generals 0 v (by decide) h).1 p p' hp hp' hpl hpl'

/-- Validity when lieutenant `3` is the only traitor, for every adversary and order. -/
example (adv : List (Fin 4) → Fin 4 → Order) (v : Order) :
    om (· ≠ 3) adv 1 0 lieutenants v [] 1 = v :=
  (byzantine_generals 0 v (by decide) (by decide)).2 (by decide) 1 (by decide) (by decide)

/-- Lemma 1 with a loyal commander: `2 k + m < n` for `k = 1`, `m = 1` and `n = 4`. -/
example (loyal : Fin 4 → Prop) [DecidablePred loyal] (adv : List (Fin 4) → Fin 4 → Order)
    (v : Order) (h0 : loyal 0) (h : ((insert 0 lieutenants).filter (¬ loyal ·)).card ≤ 1)
    {p : Fin 4} (hp : p ∈ lieutenants) (hpl : loyal p) :
    om loyal adv 1 0 lieutenants v [] p = v :=
  om_eq_of_loyal (k := 1) v [] h0 (by decide) h hp hpl

end Cslib.Distributed.Byzantine.Tests
