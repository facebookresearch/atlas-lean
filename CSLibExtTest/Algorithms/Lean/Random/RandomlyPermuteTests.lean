/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Random.RandomlyPermute
public meta import Cslib.Algorithms.Lean.TimeM

@[expose] public meta section

namespace Cslib.Algorithms.Lean.TimeM.RandomlyPermuteTests

universe u

open Cslib.Algorithms.Lean.TimeM

private def check {α : Type u} [BEq α] [Repr α]
    (name : String) (actual expected : α) : IO Unit := do
  if actual != expected then
    throw <| IO.userError s!"{name}: expected {repr expected}, actual {repr actual}"
  IO.println s!"{name}: {repr actual}"

private def historyTwo (a : Fin 2) (i : Fin 2) : Fin (2 - i.val) :=
  if h : i.val = 0 then ⟨a.val, by have := a.isLt; omega⟩
  else ⟨0, by omega⟩

private def historyThree (a : Fin 3) (b : Fin 2) (i : Fin 3) : Fin (3 - i.val) :=
  if h0 : i.val = 0 then ⟨a.val, by have := a.isLt; omega⟩
  else if h1 : i.val = 1 then ⟨b.val, by have := b.isLt; omega⟩
  else ⟨0, by omega⟩

private def allSelf {n : Nat} (i : Fin n) : Fin (n - i.val) := ⟨0, by omega⟩

private def runCases (args : List String) : IO Unit := do
  let empty : Vector Empty 0 := ⟨#[], rfl⟩
  let emptyResult := randomlyPermute empty (fun i => Fin.elim0 i)
  check "empty vector size" emptyResult.ret.size 0
  check "empty events" emptyResult.time (0, 0)
  let singleton : Vector String 1 := ⟨#["a"], rfl⟩
  let singleResult := randomlyPermute singleton allSelf
  check "singleton" singleResult.ret.toList ["a"]
  check "singleton includes draw and self-swap" singleResult.time (1, 1)
  let two : Vector Nat 2 := ⟨#[0, 1], rfl⟩
  let outputsTwo := (List.finRange 2).map fun a =>
    let result := randomlyPermute two (historyTwo a)
    ((List.finRange 2).map fun i => (historyTwo a i).val, result.ret.toList, result.time)
  check "every n2 history" outputsTwo
    [([0, 0], [0, 1], (2, 2)), ([1, 0], [1, 0], (2, 2))]
  let three : Vector Nat 3 := ⟨#[0, 1, 2], rfl⟩
  let outputsThree := (List.finRange 3).flatMap fun a =>
    (List.finRange 2).map fun b =>
      let result := randomlyPermute three (historyThree a b)
      ((List.finRange 3).map fun i => (historyThree a b i).val, result.ret.toList, result.time)
  check "every n3 history" outputsThree
    [([0, 0, 0], [0, 1, 2], (3, 3)), ([0, 1, 0], [0, 2, 1], (3, 3)),
     ([1, 0, 0], [1, 0, 2], (3, 3)), ([1, 1, 0], [1, 2, 0], (3, 3)),
     ([2, 0, 0], [2, 1, 0], (3, 3)), ([2, 1, 0], [2, 0, 1], (3, 3))]
  check "n2 history count" outputsTwo.length 2
  check "n3 history count" outputsThree.length 6
  let permOutputs := outputsThree.map fun row => row.2.1
  let prefixTable := (List.range 4).map fun k =>
    (k, permOutputs.map fun out =>
      (out.take k, permOutputs.countP fun other => other.take k == out.take k))
  check "all n3 injective prefixes and completion counts" prefixTable
    [(0, [([], 6), ([], 6), ([], 6), ([], 6), ([], 6), ([], 6)]),
     (1, [([0], 2), ([0], 2), ([1], 2), ([1], 2), ([2], 2), ([2], 2)]),
     (2, [([0, 1], 1), ([0, 2], 1), ([1, 0], 1), ([1, 2], 1), ([2, 1], 1), ([2, 0], 1)]),
     (3, [([0, 1, 2], 1), ([0, 2, 1], 1), ([1, 0, 2], 1), ([1, 2, 0], 1),
       ([2, 1, 0], 1), ([2, 0, 1], 1)])]
  check "unsupported event-count support" (outputsThree.countP fun row => row.2.2 == (2, 3)) 0
  let cycle := randomlyPermute three (historyThree ⟨1, by decide⟩ ⟨1, by decide⟩)
  check "three-cycle original-label orientation" cycle.ret.toList
    (if args == ["wrong-orientation"] then [2, 0, 1] else [1, 2, 0])
  let repeated : Vector String 3 := ⟨#["a", "a", "b"], rfl⟩
  let repeatedResult := randomlyPermute repeated (historyThree ⟨2, by decide⟩ ⟨1, by decide⟩)
  check "repeated values" repeatedResult.ret.toList ["b", "a", "a"]
  check "repeated counts" repeatedResult.time (3, 3)
  let repeatedOutputs := (List.finRange 3).flatMap fun a =>
    (List.finRange 2).map fun b => (randomlyPermute repeated (historyThree a b)).ret.toList
  check "all repeated-value outputs" repeatedOutputs
    [["a", "a", "b"], ["a", "b", "a"], ["a", "a", "b"], ["a", "b", "a"],
      ["b", "a", "a"], ["b", "a", "a"]]
  check "coalesced history masses over denominator six"
    ([ ["a", "a", "b"], ["a", "b", "a"], ["b", "a", "a"] ].map fun out =>
      (out, repeatedOutputs.countP fun other => other == out))
    [(["a", "a", "b"], 2), (["a", "b", "a"], 2), (["b", "a", "a"], 2)]
  let four : Vector (String × Nat) 4 :=
    ⟨#[("a", 0), ("b", 1), ("c", 2), ("d", 3)], rfl⟩
  let mixedHistory (i : Fin 4) : Fin (4 - i.val) :=
    if h0 : i.val = 0 then ⟨2, by omega⟩
    else if h1 : i.val = 1 then ⟨2, by omega⟩
    else ⟨0, by omega⟩
  let mixed := randomlyPermute four mixedHistory
  check "mixed full saved fields" mixed.ret.toList
    (if args == ["wrong-output"] then four.toList
     else [("c", 2), ("d", 3), ("a", 0), ("b", 1)])
  check "mixed values" (mixed.ret.toList.map Prod.fst) ["c", "d", "a", "b"]
  check "mixed labels" (mixed.ret.toList.map Prod.snd) [2, 3, 0, 1]
  check "mixed counts" mixed.time
    (if args == ["wrong-draw-count"] then (3, 4)
     else if args == ["wrong-swap-count"] then (4, 3) else (4, 4))
  check "mixed absolute choices" ((List.finRange 4).map fun i => i.val + (mixedHistory i).val)
    [2, 3, 2, 3]
  let self := randomlyPermute four allSelf
  check "all self-swaps saved fields" self.ret.toList four.toList
  check "all self-swap events" self.time (4, 4)

#eval runCases []

end Cslib.Algorithms.Lean.TimeM.RandomlyPermuteTests

end
