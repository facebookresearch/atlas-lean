/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Databases.QueryMPC
import Mathlib.Data.Fin.VecNotation
import Mathlib.Probability.Distributions.Bernoulli

/-!
# A three-worker join, with a public coin choosing the collector

Each of three unary relations on a one-element domain is encoded by its membership bit. One
legal distributed placement gives one word to each worker, in schema order. In the first round
two workers send their bits to the collector. Only after that barrier can it test the join. In
the second round it tells worker 1 whether to report the tuple. The alternative placement on
three input servers instead delivers all three bits from their relation servers in round one.
-/

namespace Cslib.Databases.QueryMPCTests

open QueryMPC MeasureTheory

private def collect (coin : Bool) : Fin 3 := if coin then 2 else 0
private def words (a b c : Bool) : Database 3 := ![[a], [b], [c]]
private def answer (a b c : Bool) : Finset Unit := if a && b && c then {()} else ∅

private def joinProtocol : Protocol 3 3 Bool Unit where
  send coin w v dst := match v.history with
    | [] => if dst = collect coin then v.initial else []
    | [m] => if w = collect coin ∧ dst = 1 then
        [((List.ofFn m.worker).flatten ++ v.initial ++ (List.ofFn m.source).flatten).all id]
      else []
    | _ => []
  inject coin _ data dst := if dst = collect coin then data else []
  report coin w v := match v.history with
    | m :: _ :: _ => if w = 1 ∧ m.worker (collect coin) = [true] then {()} else ∅
    | _ => ∅

private def schemaLayout : Layout 3 (fun _ : Fin 3 => 1) where
  slots := fun _ => 1
  balanced := by decide
  wire := Equiv.refl _

private def localInput (a b c : Bool) : Start 3 3 :=
  (Schedule.distributed schemaLayout).place (fun j _ => ![a, b, c] j)

-- Flipping both remote bits cannot reveal the global conjunction at worker 0.
example (b c : Bool) : (localInput true b c).initial 0 = (localInput true (!b) (!c)).initial 0 := by
  rfl

example : let I := localInput true false true
    let mail := joinProtocol.mail false I 0 I.initial
    (mail 0).worker 1 = [false] ∧ (mail 0).worker 2 = [true] ∧ (mail 0).worker 0 = [] ∧
    (mail 1).worker 2 = [] ∧ roundLoad mail = 2 := by decide

-- Add a third one-bit edge, this time to a different recipient. Network traffic grows
-- from two to three bits without changing the maximum received from two.
example : let I := localInput true false true
    let fork := {joinProtocol with send := fun coin u v dst =>
      if u = 1 ∧ dst = 2 then v.initial else joinProtocol.send coin u v dst}
    let m := fork.mail false I 0 I.initial
    (m 0).worker 1 = [false] ∧ (m 0).worker 2 = [true] ∧
    (m 2).worker 1 = [false] ∧ roundLoad m = 2 := by decide

-- Worker 1 has exactly the same view after the first barrier on these two inputs; its
-- report can distinguish them only after the collector forwards the test in round two.
private def observed (I : Start 3 3) (r : ℕ) :=
  (joinProtocol.run false I 2 r).map fun v => ((v 1).initial, (v 1).history.map (·.worker 0))

example : observed (localInput true true true) 1 = some ([true], [[]]) ∧
    observed (localInput false true true) 1 = some ([true], [[]]) ∧
    observed (localInput true true true) 2 = some ([true], [[true], []]) ∧
    observed (localInput false true true) 2 = some ([true], [[false], []]) := by decide

example (coin a b c : Bool) : joinProtocol.output coin (localInput a b c) 1 2 = none := by
  decide +revert

private theorem twoRounds (coin a b c : Bool) :
    joinProtocol.output coin (localInput a b c) 2 2 = some (answer a b c) := by decide +revert

-- The random law does not depend on the database. The event has mass one under either
-- choice of collector, hence also under the fair Bernoulli mixture.
example (a b c : Bool) :
    ProbabilityTheory.bernoulliMeasure true false ⟨1/2, by constructor <;> norm_num⟩
      {coin | joinProtocol.output coin (localInput a b c) 2 2 = some (answer a b c)} = 1 := by
  simp [twoRounds]

example (a b c coin : Bool) :
    let I : Start 3 3 := .separate (words a b c)
    roundLoad (joinProtocol.mail coin I 0 I.initial) = 3 ∧
    joinProtocol.output coin I 3 2 = some (answer a b c) := by decide +revert

example (C ε : ℝ) (M : ℕ) (p : ℕ+) : receiveCap C ε 0 p = 0 ∧
    receiveCap C ε M 1 = ⌊C * M⌋₊ ∧ receiveCap C 0 M p = ⌊C * M / (p : ℝ)⌋₊ ∧
    receiveCap C 1 M p = ⌊C * M⌋₊ := by simp [receiveCap]

-- A single worker receives nothing in the distributed convention, in every round, even
-- if its send function would try to fill the diagonal slot. It retains its own initial bits.
example (A : Protocol 1 3 Bool Unit) (s : Fin 1 → Bits) (ω : Bool) (r : ℕ)
    (v : Fin 1 → View 1 3) : roundLoad (A.mail ω (.distributed s) r v) = 0 := by
  simp [roundLoad, Protocol.mail]

end Cslib.Databases.QueryMPCTests
