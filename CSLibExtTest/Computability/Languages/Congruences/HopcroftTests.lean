/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Hopcroft
public meta import CSLibExt.Computability.Languages.Congruences.Hopcroft

/-!
# Tests for Hopcroft's minimization algorithm

* The automata of the Moore tests: `parity4` (number of `true`s modulo 4, accepting `0` and `2`)
  has the final partition `{0, 2} | {1, 3}`; `withDead` keeps its unreachable accepting state `2`
  in a block of its own (Hopcroft works on all states; the quotient of the reachable states drops
  it); `parity8` ends with two blocks; `still12` (twelve accepting states, no moves) starts and
  ends with one block and an empty waiting list.
* Random fixtures (fixed seed): 300 automata over a two-letter alphabet with 2 to 14 states.
  For each, Hopcroft's relation equals Moore's, the waiting list is exhausted within the
  `|Σ| (|Q| + 1)` rounds, and the final partition has one block per class of Moore's relation.
* Closed checks evaluate the partition with `decide +kernel` and instantiate the main theorems.
-/

@[expose] public section

namespace DFA.HopcroftTests

/-- The two Booleans, enumerated. -/
@[instance_reducible]
def finEnumBool : FinEnum Bool := FinEnum.ofList [false, true] (by decide)

attribute [local instance] finEnumBool

/-- Number of `true`s modulo 4; accept counts `0` and `2`. -/
def parity4 : DFA Bool (Fin 4) := ⟨fun s b => if b then s + 1 else s, 0, {0, 2}⟩

instance : DecidablePred (· ∈ parity4.accept) :=
  inferInstanceAs (DecidablePred (· ∈ ({0, 2} : Set (Fin 4))))

/-- Parity of `true`s on states `0, 1`, plus an unreachable accepting state `2`. -/
def withDead : DFA Bool (Fin 3) :=
  ⟨fun s b => if s = 2 then 2 else if b then 1 - s else s, 0, {0, 2}⟩

instance : DecidablePred (· ∈ withDead.accept) :=
  inferInstanceAs (DecidablePred (· ∈ ({0, 2} : Set (Fin 3))))

/-- Number of `true`s modulo 8; accept even counts. -/
def parity8 : DFA Bool (Fin 8) := ⟨fun s b => if b then s + 1 else s, 0, {s | s.val % 2 = 0}⟩

instance : DecidablePred (· ∈ parity8.accept) :=
  inferInstanceAs (DecidablePred fun s : Fin 8 => s.val % 2 = 0)

/-- Twelve states, all accepting, no moves. -/
def still12 : DFA Bool (Fin 12) := ⟨fun s _ => s, 0, Set.univ⟩

instance : DecidablePred (· ∈ still12.accept) :=
  inferInstanceAs (DecidablePred (· ∈ (Set.univ : Set (Fin 12))))

#eval parity4.hopcroftPartition
#eval withDead.hopcroftPartition
#eval parity8.hopcroftPartition
#eval still12.hopcroftPartition

example : ((0 : Fin 4), (2 : Fin 4)) ∈ parity4.hopcroftRel := by decide +kernel
example : ((0 : Fin 4), (1 : Fin 4)) ∉ parity4.hopcroftRel := by decide +kernel
example : parity4.hopcroftPartition.length = 2 := by decide +kernel
example : withDead.hopcroftPartition.length = 3 := by decide +kernel
example : parity8.hopcroftPartition.length = 2 := by decide +kernel
example : still12.hopcroftPartition = [Finset.univ] := by decide +kernel

/-! Random automata over `Fin 2` -/

/-- An automaton from a transition table (`step s a = table[2 s + a] mod (k + 1)`) and an
acceptance list. -/
def tableDFA (k : ℕ) (tbl : List ℕ) (acc : List Bool) : DFA (Fin 2) (Fin (k + 1)) :=
  ⟨fun s a => ⟨tbl.getD (2 * s.val + a.val) 0 % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩, 0,
    {s | acc.getD s.val false = true}⟩

instance (k : ℕ) (tbl : List ℕ) (acc : List Bool) :
    DecidablePred (· ∈ (tableDFA k tbl acc).accept) := fun s =>
  inferInstanceAs (Decidable (acc.getD s.val false = true))

/-- A deterministic linear congruential generator. -/
def nextSeed (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

#eval show IO Unit from do
  let mut s := 7
  let mut blocks := 0
  for run in [0:300] do
    s := nextSeed s
    let k := 1 + s / 7 % 13
    let mut tbl : List ℕ := []
    let mut acc : List Bool := []
    for _ in [0:2 * (k + 1)] do
      s := nextSeed s
      tbl := tbl ++ [s / 11]
    for _ in [0:k + 1] do
      s := nextSeed s
      acc := acc ++ [s / 13 % 3 == 0]
    let M := tableDFA k tbl acc
    unless M.hopcroftRel == M.mooreRel do
      throw (IO.userError s!"run {run}: Hopcroft and Moore disagree")
    unless (M.hopcroftLoop (2 * (k + 2)) (Hopcroft.initP M) (Hopcroft.initW M)).2.isEmpty do
      throw (IO.userError s!"run {run}: waiting list not exhausted")
    let classes := (Finset.univ.image fun q : Fin (k + 1) =>
      Finset.univ.filter fun r => (q, r) ∈ M.mooreRel).card
    unless M.hopcroftPartition.length == classes do
      throw (IO.userError s!"run {run}: {M.hopcroftPartition.length} blocks, {classes} classes")
    blocks := blocks + classes
  IO.println s!"300 random automata (2 to 14 states, 2 letters): Hopcroft's relation equals \
    Moore's, the waiting list is exhausted, one block per class ({blocks} blocks in total)"

/-! Closed checks -/

example : parity4.hopcroftRel = parity4.mooreRel := parity4.hopcroftRel_eq_mooreRel

example (p q : Fin 4) :
    (p, q) ∈ parity4.hopcroftRel ↔ parity4.acceptsFrom p = parity4.acceptsFrom q :=
  parity4.mem_hopcroftRel_iff

example {α σ : Type*} [Fintype α] [FinEnum α] [Fintype σ] [DecidableEq σ] (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] : M.hopcroftRel = M.mooreRel :=
  M.hopcroftRel_eq_mooreRel

#print axioms DFA.hopcroftRel_eq_mooreRel
#print axioms DFA.mem_hopcroftRel_iff
#print axioms DFA.hopcroftLoop_waiting_eq_nil

end DFA.HopcroftTests
