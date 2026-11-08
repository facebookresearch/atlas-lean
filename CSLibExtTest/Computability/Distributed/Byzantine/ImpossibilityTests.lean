/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Byzantine.Impossibility

/-!
# Tests for the Byzantine generals impossibility

The naive protocol: in one round the commander tells every lieutenant its order, and each
lieutenant decides what the commander told it.

* With three generals, a traitorous commander telling lieutenant `1` "true" and lieutenant
  `2` "false" breaks IC1. This run matches the execution the hexagon argument builds for the
  nodes `1, 2` when the commander nodes `0` and `3` have the orders `true` and `false`: on the
  hexagon, node `1` hears the commander node `0` and node `2` hears the commander node `3`.
* With a loyal commander and a traitorous lieutenant, IC1 and IC2 hold, and with no traitor
  the naive protocol solves the problem: the conditions are not vacuous.
* The main theorems apply to it.
* With two generals the naive protocol tolerates one traitor, so the hypothesis `3 ≤ n` of
  `not_solves_of_card_le_three_mul` cannot be dropped.

A positive control with a traitor: algorithm OM(1) of Lamport, Shostak and Pease for four
generals satisfies IC1 and IC2, with no traitor and with every single traitor, for every order
and every traitor behaviour that does not depend on the round.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.Byzantine.Impossibility.Tests

/-- The naive one-round protocol for the generals `Fin (n + 1)` with commander `0`: states and
messages are booleans, every general sends its state, the commander keeps its order, and a
lieutenant adopts and decides the commander's message. -/
def naive (n : ℕ) : OralProtocol (Fin (n + 1)) Bool Bool Bool where
  init _ := false
  initCommander v := v
  send _ _ s _ := s
  recv _ i s msg := if i = 0 then s else msg 0
  decide _ s := s

/-- A traitor that sends `true` to general `1` and `false` to everyone else. -/
def splitOrder (_ : ℕ) (_ i : Fin 3) : Bool := i == 1

/-- The traitorous commander makes lieutenants `1` and `2` decide differently. -/
example : (naive 2).decision 0 true {0} splitOrder 1 1 = true := by decide

/-- Lieutenant `2` decides `false`. -/
example : (naive 2).decision 0 true {0} splitOrder 1 2 = false := by decide

/-- IC1 fails with the traitorous commander. -/
example : ¬ (naive 2).Agreement 0 true {0} splitOrder 1 := by decide

/-- IC2 holds vacuously when the commander is a traitor. -/
example : (naive 2).Validity 0 true {0} splitOrder 1 := by decide

/-- With a loyal commander and a traitorous lieutenant, IC1 and IC2 hold. -/
example : (naive 2).Agreement 0 false {2} splitOrder 1 ∧
    (naive 2).Validity 0 false {2} splitOrder 1 := by decide

/-- Without traitors the naive protocol solves the problem for three generals. -/
example : (naive 2).Solves 0 0 1 := by
  intro v traitors ht adv
  obtain rfl := Finset.card_eq_zero.1 (Nat.le_zero.1 ht)
  have hd : ∀ i : Fin 3, i ≠ 0 → (naive 2).decision 0 v ∅ adv 1 i = v := by
    intro i hi
    simp [OralProtocol.decision, OralProtocol.state, OralProtocol.initState, naive, hi]
  exact ⟨fun i j hi hj _ _ => (hd i hi).trans (hd j hj).symm, fun _ i hi _ => hd i hi⟩

/-- The main theorem: the naive protocol does not tolerate one traitor. -/
example : ¬ (naive 2).Solves 0 1 1 := (naive 2).not_solves_three 1

/-- The main theorem in its existential form, for any number of rounds. -/
example (T : ℕ) : ∃ (v : Bool) (t : Fin 3) (adv : ℕ → Fin 3 → Fin 3 → Bool),
    ¬ ((naive 2).Agreement 0 v {t} adv T ∧ (naive 2).Validity 0 v {t} adv T) :=
  (naive 2).exists_violation_three T

/-- No protocol for six generals tolerates two traitors. -/
example {V σ M : Type} [Nontrivial V] (P : OralProtocol (Fin 6) V σ M) (c : Fin 6) (T : ℕ) :
    ¬ P.Solves c 2 T :=
  P.not_solves_of_card_le_three_mul c (by simp) (by simp) T

/-- No protocol for four generals tolerates two traitors. -/
example {V σ M : Type} [Nontrivial V] (P : OralProtocol (Fin 4) V σ M) (T : ℕ) :
    ¬ P.Solves 3 2 T :=
  P.not_solves_of_card_le_three_mul 3 (by simp) (by simp) T

/-- With two generals the naive protocol tolerates one traitor. -/
example : (naive 1).Solves 0 1 1 := by
  intro v traitors _ adv
  refine ⟨fun i j hi hj _ _ => ?_, fun hc i hi _ => ?_⟩
  · rw [Fin.eq_one_of_ne_zero i hi, Fin.eq_one_of_ne_zero j hj]
  · simp [OralProtocol.decision, OralProtocol.state, OralProtocol.initState, naive, hi, hc]

/-! ### A positive control: OM(1) for four generals -/

/-- The majority of three booleans. -/
def maj3 (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Algorithm OM(1) for the four generals `Fin 4` with commander `0`, in two rounds. In round
`0` the commander sends its order; in round `1` every lieutenant relays the order it received.
A lieutenant's state records the order it received at index `0` and, at each index `j ≠ 0`,
the order lieutenant `j` relayed to it (its own entry is the order it received); every general
sends entry `0` of its state. A lieutenant decides the majority of entries `1`, `2`, `3`. -/
def om1 : OralProtocol (Fin 4) Bool (Fin 4 → Bool) Bool where
  init _ _ := false
  initCommander v _ := v
  send _ _ s _ := s 0
  recv r i s msg :=
    if i = 0 then s else if r = 0 then fun _ => msg 0 else fun j => if j = 0 then s 0 else msg j
  decide _ s := maj3 (s 1) (s 2) (s 3)

/-- The traitor behaviour sending `b₁`, `b₂`, `b₃` to the generals `1`, `2`, `3` in every
round. -/
def sendBits (b₁ b₂ b₃ : Bool) (_ : ℕ) (_ i : Fin 4) : Bool :=
  if i = 1 then b₁ else if i = 2 then b₂ else i = 3 && b₃

/-- OM(1) satisfies IC1 and IC2 without traitors. -/
example : ∀ v : Bool, om1.Agreement 0 v ∅ (sendBits false false false) 2 ∧
    om1.Validity 0 v ∅ (sendBits false false false) 2 := by decide

/-- OM(1) satisfies IC1 and IC2 for every order, every single traitor and every
round-independent traitor behaviour. Its code reads only the commander's messages in round `0`
and the lieutenants' messages in round `1`, so these behaviours cover what a traitor can do. -/
example : ∀ (v : Bool) (t : Fin 4) (b₁ b₂ b₃ : Bool),
    om1.Agreement 0 v {t} (sendBits b₁ b₂ b₃) 2 ∧ om1.Validity 0 v {t} (sendBits b₁ b₂ b₃) 2 := by
  decide

/-- A traitorous commander splitting its order still cannot break agreement under OM(1): all
loyal lieutenants decide `true`. -/
example : ∀ i : Fin 4, i ≠ 0 → om1.decision 0 false {0} (sendBits true false true) 2 i = true := by
  decide

end Cslib.Distributed.Byzantine.Impossibility.Tests
