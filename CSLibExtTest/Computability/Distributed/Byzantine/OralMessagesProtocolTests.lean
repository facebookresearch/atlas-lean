/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Byzantine.OralMessagesProtocol
public meta import CSLibExt.Computability.Distributed.Byzantine.OralMessagesProtocol
public meta import Mathlib.Data.Fintype.Defs

/-!
# Tests for `OM(m)` as an oral-message protocol

Concrete runs of `toProtocol` with boolean orders, where `false` (the default) is retreat:

* Four generals `Fin 4`, one traitor, `OM(1)` in two rounds: a traitorous commander that sends
  different orders (the loyal lieutenants still agree, also checked by the kernel), and a loyal
  commander with a traitorous lieutenant that lies to everybody (the loyal lieutenants follow the
  commander). After one round instead of two, a loyal lieutenant decides wrongly.
* Seven generals `Fin 7`, two traitors, `OM(2)` in three rounds, with lies that depend on the
  round, the sender, the recipient and the path: agreement and validity.
* Three generals `Fin 3`, one traitor, `OM(1)`: validity fails, so the bound `3 m < n` matters.

Runs with natural-number orders other than the default `0` and commanders other than `0`, all
checked by the kernel:

* Four generals, traitorous commander `2`, `OM(1)` in two rounds: the loyal lieutenants agree on
  the majority of its round-`0` orders, although it sends other values in round `1`. Its
  round-`0` entry survives two extra rounds, and `OM(0)` in one round lets two loyal lieutenants
  disagree.
* Three generals, loyal commander `1`, `OM(1)`: the tie between the order and the lie gives
  `default`, which is neither of them.
* Seven generals, traitors `1` and `4` (the commander): `OM(1)` in two rounds breaks agreement,
  and `OM(2)` in three rounds makes the five loyal lieutenants decide the same value.

Then the API: `decision_toProtocol`, also after more rounds (`decision_toProtocol_of_le`), and
the simp lemma for `advOfMessages`; `solves_toProtocol` for four generals and one traitor, seven
generals and two traitors, a single general and no traitor, and generals and orders in arbitrary
universes; the characterization for four generals in arbitrary universes (solvable) and three
generals (not solvable) with one traitor; two generals, where `OM(1)` tolerates one traitor
although `3 * 1 < 2` fails, so the hypothesis `3 ≤ n` of the characterization cannot be dropped;
and a single order, where `toProtocol` tolerates any number of traitors, so the hypothesis
`Nontrivial V` cannot be dropped either.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Cslib.Distributed.Byzantine.OralMessagesProtocol.Tests

open Cslib.Distributed.Byzantine Impossibility OralMessages

/-- `OM(1)` with commander `0` for the generals `Fin 4` and boolean orders. -/
abbrev om1 : OralProtocol (Fin 4) Bool (List (Fin 4) → Bool) (List (Fin 4) → Bool) :=
  toProtocol 0 1

/-- A traitor that sends `true` to the generals `1` and `3` and `false` to `2`, for every path and
in every round. -/
def splitOrder (_ : ℕ) (_ i : Fin 4) (_ : List (Fin 4)) : Bool := i != 2

/-- A traitor that sends `false` for every path, to everybody, in every round. -/
def alwaysFalse {G : Type} (_ : ℕ) (_ _ : G) (_ : List G) : Bool := false

-- Commander `0` is the traitor: lieutenants `1`, `2`, `3` receive `true`, `false`, `true`, relay
-- these values to each other in round `1`, and all decide the majority `true`.
#guard ([1, 2, 3] : List (Fin 4)).map (om1.decision 0 false {0} splitOrder 2) = [true, true, true]

-- Commander `0` is loyal and orders `true`; lieutenant `3` is the traitor and relays `false` to
-- everybody: the loyal lieutenants `1` and `2` decide `true`.
#guard ([1, 2] : List (Fin 4)).map (om1.decision 0 true {3} alwaysFalse 2) = [true, true]

-- One round is not enough: after round `0` the tables hold no relayed values, so the decision
-- of `OM(1)` reads `default` entries, and lieutenant `1` decides `false` although the loyal
-- commander ordered `true`.
#guard om1.decision 0 true {3} alwaysFalse 1 1 = false

/-! ### Two traitors among seven generals, `OM(2)` -/

/-- `OM(2)` with commander `0` for the generals `Fin 7` and boolean orders. -/
abbrev om2 : OralProtocol (Fin 7) Bool (List (Fin 7) → Bool) (List (Fin 7) → Bool) :=
  toProtocol 0 2

/-- Traitors whose lies depend on the round, the sender, the recipient and the path. -/
def pathLies (r : ℕ) (j i : Fin 7) (τ : List (Fin 7)) : Bool :=
  (r + j.val + 2 * i.val + (τ.map Fin.val).sum) % 3 == 0

/-- The decisions of the loyal lieutenants under `OM(2)` after three rounds, with commander `0`
and order `true`. -/
def loyalDecisions7 (traitors : Finset (Fin 7)) : List Bool :=
  (([1, 2, 3, 4, 5, 6] : List (Fin 7)).filter (· ∉ traitors)).map
    (om2.decision 0 true traitors pathLies 3)

-- Traitors `0` (the commander) and `3`: the loyal lieutenants agree.
#guard let d := loyalDecisions7 {0, 3}; d.all (· == d.headD false)

-- Traitors `3` and `5`, loyal commander ordering `true`: the loyal lieutenants decide `true`.
#guard (loyalDecisions7 {3, 5}).all (· == true)

-- Traitors `2` and `6`: the loyal lieutenants decide `true`.
#guard (loyalDecisions7 {2, 6}).all (· == true)

/-! ### Three generals -/

-- Three generals, `OM(1)`: commander `0` is loyal and orders `true`, lieutenant `2` is the
-- traitor and relays `false`. Lieutenant `1` holds `true` and `false` once each, so there is no
-- majority and it decides `false`: validity fails.
#guard (toProtocol (G := Fin 3) (V := Bool) 0 1).decision 0 true {2} alwaysFalse 2 1 = false

/-- The `OM(1)` run with the traitorous commander, checked by the kernel. -/
example : om1.decision 0 false {0} splitOrder 2 2 = true := by decide

/-! ### Natural-number orders and commanders other than `0`, checked by the kernel -/

/-- A traitorous commander that, for every path, sends `7` to general `0` and `11` to everybody
else in round `0`, and `99` in every later round. -/
def commanderLies (r : ℕ) (_ p : Fin 4) (_ : List (Fin 4)) : ℕ :=
  if r = 0 then if p = 0 then 7 else 11 else 99

/-- `OM(1)` with the traitorous commander `2`: the lieutenants `0`, `1` and `3` receive `7`, `11`
and `11` in round `0` and all decide the majority `11`, although the commander sends `99` in
round `1`. -/
example : ([0, 1, 3] : List (Fin 4)).map
    ((toProtocol (G := Fin 4) (V := ℕ) 2 1).decision 2 17 {2} commanderLies 2) =
      [11, 11, 11] := by
  decide

/-- After four rounds, two more than `OM(1)` needs, lieutenant `0` still holds at the path `[2]`
the order `7` that the commander sent it in round `0`. -/
example : (toProtocol (G := Fin 4) (V := ℕ) 2 1).state 2 17 {2} commanderLies 4 0 [2] = 7 := by
  decide

/-- `OM(0)` in one round, with no relay round, lets the traitorous commander split the loyal
lieutenants `0` and `1`. -/
example : (toProtocol (G := Fin 4) (V := ℕ) 2 0).decision 2 17 {2} commanderLies 1 0 ≠
    (toProtocol (G := Fin 4) (V := ℕ) 2 0).decision 2 17 {2} commanderLies 1 1 := by
  decide

/-- Three generals, `OM(1)`: commander `1` is loyal and orders `2`, lieutenant `2` is the traitor
and relays `5`. Lieutenant `0` holds `2` and `5` once each, so there is no majority and it decides
`default`, which is `0`, neither the order nor the lie: validity fails. -/
example : (toProtocol (G := Fin 3) (V := ℕ) 1 1).decision 1 2 {2} (fun _ _ _ _ ↦ 5) 2 0 = 0 := by
  decide

/-- Traitors whose messages depend on the round and the path. In round `0` a traitor sends `6` to
the generals `5` and `6` and `5` to everybody else; in round `1` it sends, at the path `[4]`, `6`
to general `0` and `5` to everybody else; every other entry is at least `70` and depends on the
round, the sender, the recipient and the length of the path. -/
def tableLies7 (r : ℕ) (j p : Fin 7) (τ : List (Fin 7)) : ℕ :=
  if r = 0 then if p = 5 ∨ p = 6 then 6 else 5
  else if r = 1 ∧ τ = [4] then if p = 0 then 6 else 5
  else 70 + r + j.val + p.val + τ.length

/-- Seven generals, traitors `1` and `4` (the commander): `OM(1)` in two rounds is one level of
relays short of `OM(2)`, and the loyal lieutenants `0` and `5` decide `0` and `5`. -/
example : (toProtocol (G := Fin 7) (V := ℕ) 4 1).decision 4 19 {1, 4} tableLies7 2 0 = 0 ∧
    (toProtocol (G := Fin 7) (V := ℕ) 4 1).decision 4 19 {1, 4} tableLies7 2 5 = 5 := by
  decide

/-- `OM(2)` in three rounds against the same traitors: the five loyal lieutenants all decide
`5`. -/
example : ([0, 2, 3, 5, 6] : List (Fin 7)).map
    ((toProtocol (G := Fin 7) (V := ℕ) 4 2).decision 4 19 {1, 4} tableLies7 3) =
      [5, 5, 5, 5, 5] := by
  decide

/-! ### The main theorems -/

/-- The decisions of `toProtocol` are the values of `om`. -/
example (adv : ℕ → Fin 4 → Fin 4 → List (Fin 4) → Bool) (v : Bool) (p : Fin 4) :
    om1.decision 0 v {3} adv 2 p =
      om (· ∉ ({3} : Finset (Fin 4))) (advOfMessages adv) 1 0 (Finset.univ.erase 0) v [] p :=
  decision_toProtocol 0 1 v {3} adv p

/-- More rounds than `OM(1)` needs: the decisions of `toProtocol` are still the values of
`om`. -/
example (adv : ℕ → Fin 4 → Fin 4 → List (Fin 4) → Bool) (v : Bool) (p : Fin 4) :
    om1.decision 0 v {3} adv 5 p =
      om (· ∉ ({3} : Finset (Fin 4))) (advOfMessages adv) 1 0 (Finset.univ.erase 0) v [] p :=
  decision_toProtocol_of_le 0 1 v {3} adv (by decide) p

/-- The relays of a traitor are read off its messages. -/
example (adv : ℕ → Fin 4 → Fin 4 → List (Fin 4) → Bool) (path : List (Fin 4)) (q p : Fin 4) :
    advOfMessages adv (path ++ [q]) p = adv path.length q p path.reverse := by
  simp

/-- `OM(1)` solves the problem for four generals and one traitor in two rounds. -/
example : om1.Solves 0 1 2 := solves_toProtocol 0 (by decide)

/-- `OM(2)` solves the problem for seven generals and two traitors in three rounds. -/
example : om2.Solves 0 2 3 := solves_toProtocol 0 (by decide)

/-- `OM(0)` solves the problem for a single general and no traitor in one round. -/
example : (toProtocol (G := Fin 1) (V := Bool) 0 0).Solves 0 0 1 :=
  solves_toProtocol 0 (by decide)

/-- `OM(1)` with generals and orders in arbitrary universes. -/
example :
    (toProtocol (G := ULift.{u} (Fin 4)) (V := ULift.{v} Bool) ⟨0⟩ 1).Solves ⟨0⟩ 1 2 :=
  solves_toProtocol _ (by simp)

/-- The booleans lifted to the universe `v` have two distinct values. -/
instance : Nontrivial (ULift.{v} Bool) := nontrivial_of_ne ⟨false⟩ ⟨true⟩ (by simp)

/-- Four generals, one traitor: some protocol solves the problem, in arbitrary universes. -/
example : ∃ (σ M : Type (max u v)) (P : OralProtocol (ULift.{u} (Fin 4)) (ULift.{v} Bool) σ M)
    (T : ℕ), P.Solves ⟨0⟩ 1 T :=
  (exists_solves_iff_three_mul_lt_card _ 1 (by simp)).2 (by simp)

/-- Three generals, one traitor: no protocol solves the problem. -/
example : ¬ ∃ (σ M : Type) (P : OralProtocol (Fin 3) Bool σ M) (T : ℕ), P.Solves 0 1 T :=
  fun h ↦ absurd ((exists_solves_iff_three_mul_lt_card 0 1 (by decide)).1 h) (by decide)

/-- With two generals `OM(1)` tolerates one traitor although `3 * 1 < 2` fails, so the hypothesis
`3 ≤ n` of `exists_solves_iff_three_mul_lt_card` cannot be dropped. -/
example : (toProtocol (G := Fin 2) (V := Bool) 0 1).Solves 0 1 2 := by
  intro v traitors _ adv
  refine ⟨fun i j hi hj _ _ ↦ by rw [Fin.eq_one_of_ne_zero i hi, Fin.eq_one_of_ne_zero j hj],
    fun hc i hi _ ↦ ?_⟩
  rw [Fin.eq_one_of_ne_zero i hi, decision_toProtocol, om]
  apply majority_eq_of_lt_count
  have h : (Finset.univ.erase 0 : Finset (Fin 2)) = {1} := by decide
  simp [h, received, hc]

/-- Two generals, one traitor: `3 * 1 < 2` fails. -/
example : ¬ 3 * 1 < Fintype.card (Fin 2) := by decide

/-- With a single order, `toProtocol c m` solves the problem for every number of traitors, even
among three generals, so the hypothesis `Nontrivial V` of `exists_solves_iff_three_mul_lt_card`
cannot be dropped. -/
example (m : ℕ) (c : Fin 3) : (toProtocol (V := Unit) c m).Solves c m (m + 1) := by
  intro v traitors _ adv
  exact ⟨fun _ _ _ _ _ _ ↦ Subsingleton.elim _ _, fun _ _ _ _ ↦ Subsingleton.elim _ _⟩

end Cslib.Distributed.Byzantine.OralMessagesProtocol.Tests
