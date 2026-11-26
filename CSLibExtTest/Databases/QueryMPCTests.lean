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

-- On this example domain p ≤ M and both relation words are nonempty. This is a chosen
-- encoding/regime, not a restriction attributed to BKS. Each word is a unary relation's
-- membership bitmap; the query asks whether its first element belongs to both relations.
private def bitDomain (p : ℕ+) (n : Fin 2 → ℕ) : Prop :=
  0 < n 0 ∧ 0 < n 1 ∧ (p : ℕ) ≤ n 0 + n 1

private def memberBit (s : Bits) : Bool := s.head? == some true

private def intersectionAtFirst (D : Database 2) : Finset Unit :=
  if memberBit (D 0) && memberBit (D 1) then {()} else ∅

private def twoSenders (p : ℕ+) : Protocol p 2 Bool Unit where
  send _ _ _ _ := []
  inject _ _ d dst := if dst = 0 then [memberBit d] else []
  report _ w v := if w = 0 then match v.history with
    | [] => ∅
    | m :: _ => intersectionAtFirst m.source
    else ∅

private theorem twoSenders_ok (p : ℕ+) (D : Database 2) (L : ℕ) (hL : 2 ≤ L) (ω : Bool) :
    (twoSenders p).output ω (.separate D) L 1 = some (intersectionAtFirst D) := by
  let I : Start p 2 := .separate D
  let m := (twoSenders p).mail ω I 0 I.initial
  have fit : roundLoad m ≤ L := by
    rw [roundLoad_le_iff]; intro w
    by_cases hw : w = 0 <;> simp [m, I, Protocol.mail, twoSenders, hw, hL]
  have ran : (twoSenders p).run ω I L 1 =
      some (fun w => {(I.initial w) with history := [m w]}) :=
    (Protocol.run_succ_eq_some_iff _ _ _ _ 0 _).2 ⟨_, rfl, fit, rfl⟩
  rw [Protocol.output, ran]; apply congrArg some; ext a
  have onlyCollector (S : Finset Unit) : (∃ w : Fin p, a ∈ if w = 0 then S else ∅) ↔ a ∈ S := by
    constructor
    · rintro ⟨w, hw⟩; split at hw <;> simp_all
    · intro ha; exact ⟨0, by simpa using ha⟩
  simpa +contextual [m, I, Protocol.mail, Start.initial, twoSenders, intersectionAtFirst,
    memberBit] using onlyCollector (intersectionAtFirst D)

-- The protocol communicates two actual bits under the ε=0 reporting predicate, not just
-- on a finite trace: C=2 fits them throughout the domain, even for unbounded p and M.
example (μ : Measure Bool) [IsProbabilityMeasure μ] :
    Computes μ .separate bitDomain (fun _ _ => 0) (fun _ => True) intersectionAtFirst
      (fun p _ _ => twoSenders p) 1 0 := by
  refine ⟨by constructor <;> norm_num, 2, by norm_num, ?_⟩
  intro p n hn; refine ⟨by constructor <;> norm_num, ?_⟩; intro s x _; cases s
  have size : (p : ℕ) ≤ inputBits x.words := by
    simpa [inputBits, Payload.words, Fin.sum_univ_two] using hn.2.2
  have cap : 2 ≤ receiveCap 2 0 (inputBits x.words) p := by
    apply (le_receiveCap_iff (by norm_num) ..).2
    have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.pos
    have hm : (p : ℝ) ≤ inputBits x.words := by exact_mod_cast size
    simp only [sub_zero, Real.rpow_one, Nat.cast_ofNat]; apply (le_div_iff₀ hp).2; linarith
  simp [Schedule.place, twoSenders_ok p x.words _ cap]
  have allBits : ({false, true} : Set Bool) = Set.univ := by ext b; cases b <;> simp
  rw [allBits, measure_univ]

example : ¬ bitDomain 3 (fun _ => 1) := by unfold bitDomain; decide
example (p : ℕ+) : bitDomain p (fun _ => p) := ⟨p.pos, p.pos, Nat.le_add_right ..⟩
example : intersectionAtFirst ![[true], [true]] = {()} ∧
    intersectionAtFirst ![[true], [false]] = ∅ := by decide

end Cslib.Databases.QueryMPCTests
