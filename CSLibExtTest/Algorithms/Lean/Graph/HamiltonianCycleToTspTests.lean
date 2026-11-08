/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Graph.HamiltonianCycleToTsp
public meta import Cslib.Algorithms.Lean.TimeM

@[expose] public meta section

open Cslib.Algorithms.Lean.Graph

namespace HamiltonianCycleToTspTests

private def strictDecision {n : Nat} {G : SimpleGraph (Fin n)} {a : Fin n}
    (p : G.Walk a a) : Decidable p.IsHamiltonianCycle :=
  decidable_of_iff
    (p.edges.Nodup ∧ ¬p.Nil ∧ p.support.tail.Nodup ∧
      ∀ v : Fin n, p.tail.support.count v = 1) (by
    constructor
    · rintro ⟨he, hn, hs, hc⟩
      refine ⟨⟨⟨⟨he⟩, ?_⟩, hs⟩, hc⟩
      intro h
      subst p
      exact hn .nil
    · intro h
      exact ⟨h.isTrail.edges_nodup, h.not_nil, h.support_nodup, h.isHamiltonian_tail⟩)

private def fixtureGraph {n : Nat} (edges : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ((i, j) ∈ edges ∨ (j, i) ∈ edges)
  symm := by
    constructor
    intro i j h
    exact ⟨Ne.symm h.1, h.2.elim Or.inr Or.inl⟩
  loopless := by
    constructor
    intro i h
    exact h.1 rfl

@[instance_reducible]
private def fixtureDecidable {n : Nat} (edges : List (Fin n × Fin n)) :
    DecidableRel (fixtureGraph edges).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ((i, j) ∈ edges ∨ (j, i) ∈ edges)))

private def checkArray (label : String) (input expected : Array Bool) (time : Nat) : IO Unit := do
  let actual := hamiltonianCycleToTsp input
  unless actual.ret == expected do
    throw (IO.userError s!"{label}: matrix expected={expected} actual={actual.ret}")
  unless actual.ret.size == input.size do
    throw (IO.userError s!"{label}: size")
  unless actual.time == time do
    throw (IO.userError s!"{label}: cost expected={time} actual={actual.time}")
  IO.println s!"U124_ARRAY {label} input={input} output={actual.ret} time={actual.time}"

private def checkTour {n : Nat} {a : Fin n} (label : String)
    (input expected : Array Bool) (time : Nat) (edges : List (Fin n × Fin n))
    (p : (SimpleGraph.completeGraph (Fin n)).Walk a a)
    (support : List Nat) (cost : Nat) (strict sourceCycle : Bool) : IO Unit := do
  checkArray label input expected time
  let actual := hamiltonianCycleToTsp input
  unless input.size == n * n do
    throw (IO.userError s!"{label}: graph shape")
  for i in (List.ofFn fun i : Fin n => i) do
    for j in (List.ofFn fun j : Fin n => j) do
      unless input[i.val * n + j.val]? ==
          some (@decide ((fixtureGraph edges).Adj i j) (fixtureDecidable edges i j)) do
        throw (IO.userError s!"{label}: source adjacency {i.val},{j.val}")
  unless p.support.map Fin.val == support do
    throw (IO.userError s!"{label}: canonical support")
  let some values := p.darts.mapM
    (fun d => actual.ret[d.fst.val * n + d.snd.val]?.map Bool.toNat)
    | throw (IO.userError s!"{label}: missing tour matrix cell")
  unless values.sum == cost do
    throw (IO.userError s!"{label}: tour cost expected={cost} actual={values.sum}")
  let isStrict := @decide p.IsHamiltonianCycle (strictDecision p)
  unless isStrict == strict do
    throw (IO.userError s!"{label}: strict canonical cycle")
  let usable := p.darts.all fun d =>
    @decide ((fixtureGraph edges).Adj d.fst d.snd) (fixtureDecidable edges d.fst d.snd)
  unless (isStrict && usable) == sourceCycle do
    throw (IO.userError s!"{label}: source cycle")
  IO.println s!"U124_TOUR {label} support={support} darts={p.darts.map fun d =>
    (d.fst.val, d.snd.val)} cells={values} total={values.sum} \
    strict={isStrict} source={isStrict && usable}"

private def walk2 : (SimpleGraph.completeGraph (Fin 2)).Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 0) (by decide) .nil)

private def walk3 : (SimpleGraph.completeGraph (Fin 3)).Walk 0 0 :=
  .cons (v := 1) (by decide)
    (.cons (v := 2) (by decide) (.cons (v := 0) (by decide) .nil))

private def walk3rev : (SimpleGraph.completeGraph (Fin 3)).Walk 0 0 :=
  .cons (v := 2) (by decide)
    (.cons (v := 1) (by decide) (.cons (v := 0) (by decide) .nil))

private def walk4 : (SimpleGraph.completeGraph (Fin 4)).Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 2) (by decide)
    (.cons (v := 3) (by decide) (.cons (v := 0) (by decide) .nil)))

private def walk4bad : (SimpleGraph.completeGraph (Fin 4)).Walk 0 0 :=
  .cons (v := 2) (by decide) (.cons (v := 1) (by decide)
    (.cons (v := 3) (by decide) (.cons (v := 0) (by decide) .nil)))

private def runCases : IO Unit := do
  checkArray "empty" #[] #[] 0
  checkTour "singleton" #[false] #[true] 2 []
    (.nil : (SimpleGraph.completeGraph (Fin 1)).Walk 0 0) [0] 0 false false
  checkTour "two-vertices" #[false, true, true, false] #[true, false, false, true] 8
    [(0, 1)] walk2 [0, 1, 0] 0 false false
  checkTour "triangle" #[false, true, true, true, false, true, true, true, false]
    #[true, false, false, false, true, false, false, false, true] 18
    [(0, 1), (0, 2), (1, 2)] walk3 [0, 1, 2, 0] 0 true true
  checkTour "triangle-reversed" #[false, true, true, true, false, true, true, true, false]
    #[true, false, false, false, true, false, false, false, true] 18
    [(0, 1), (0, 2), (1, 2)] walk3rev [0, 2, 1, 0] 0 true true
  checkTour "missing-closing" #[false, true, false, true, false, true, false, true, false]
    #[true, false, true, false, true, false, true, false, true] 18
    [(0, 1), (1, 2)] walk3 [0, 1, 2, 0] 1 true false
  checkTour "square" #[false, true, false, true, true, false, true, false,
      false, true, false, true, true, false, true, false]
    #[true, false, true, false, false, true, false, true,
      true, false, true, false, false, true, false, true] 32
    [(0, 1), (0, 3), (1, 2), (2, 3)] walk4 [0, 1, 2, 3, 0] 0 true true
  checkTour "square-nonedge-order" #[false, true, false, true, true, false, true, false,
      false, true, false, true, true, false, true, false]
    #[true, false, true, false, false, true, false, true,
      true, false, true, false, false, true, false, true] 32
    [(0, 1), (0, 3), (1, 2), (2, 3)] walk4bad [0, 2, 1, 3, 0] 2 true false
  checkTour "complete-four" #[false, true, true, true, true, false, true, true,
      true, true, false, true, true, true, true, false]
    #[true, false, false, false, false, true, false, false,
      false, false, true, false, false, false, false, true] 32
    [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] walk4 [0, 1, 2, 3, 0] 0 true true
  checkArray "arbitrary-empty" #[] #[] 0
  checkArray "arbitrary-one" #[true] #[false] 2
  checkArray "arbitrary-three" #[true, false, true] #[false, true, false] 6
  checkArray "arbitrary-five" #[false, true, false, true, true]
    #[true, false, true, false, false] 10
  IO.println "U124_DONE representative=9 arbitrary=4"

#eval runCases

end HamiltonianCycleToTspTests
