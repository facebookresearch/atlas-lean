/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL BLOCKS-WORLD PLANNING is NP-complete

Source:
N. Gupta and D. S. Nau, "On the complexity of blocks-world planning", Artificial Intelligence
56 (1992), 223-254, doi:10.1016/0004-3702(92)90028-V (Section 1: the Elementary Blocks World;
Section 5: PBW PLAN, the special case with a completely specified goal state; Section 7,
results 2 and 5: deciding whether there is a plan of length `L` or less is NP-complete, also
when the goal state is completely specified).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalBlocksWorldPlanning

/-!
# OPTIMAL BLOCKS-WORLD PLANNING is NP-complete

The Elementary Blocks World (Gupta and Nau, Section 1): a finite number of blocks and a table
large enough to hold all of them. Each block is on a single other object (another block or the
table), and on each block sits at most one block. The only action is to move a single clear block
(one with nothing on it) either from another block onto the table, or from an object onto
another clear block; afterwards it sits on its destination.

INSTANCE: an initial state `I` and a completely specified goal state `G` of the same `n`
blocks, and an integer `L > 0`.
QUESTION: is there a plan (a sequence of moves) of length `L` or less transforming `I` into `G`?
This is Gupta and Nau's PBW PLAN.

The blocks are `Fin n`. A state is `Fin n → Option (Fin n)`: `none` means on the table and
`some d` means on block `d`. The instance gives a state as the list `on₀, …, on_{n-1}` with
`0` for the table and `d + 1` for block `d` (`decodeState`); a well-formed list describes a
configuration of stacks: no block is under two blocks and no block is above itself.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the initial state, the goal state (each as a list, see the module docstring),
and the plan length bound `L`. -/
abbrev OptimalBlocksWorldPlanningInstance := List ℕ × List ℕ × ℕ

/-- A state of `n` blocks: the object each block sits on (`none` is the table). -/
abbrev State (n : ℕ) := Fin n → Option (Fin n)

/-- The state described by a list: entry `0` is the table and entry `d + 1` is block `d`. -/
def decodeState (n : ℕ) (l : List ℕ) : State n := fun b =>
  match l.getD b 0 with
  | 0 => none
  | d + 1 => if h : d < n then some ⟨d, h⟩ else none

/-- A list describes a configuration of `n` blocks: it has one entry per block, every entry
names the table or a block, no two blocks sit on the same block, and no block is above itself
(the relation "sits on" has no cycle). -/
def IsConfiguration (n : ℕ) (l : List ℕ) : Prop :=
  l.length = n ∧ (∀ v ∈ l, v ≤ n) ∧
    (∀ a b d : Fin n, decodeState n l a = some d → decodeState n l b = some d → a = b) ∧
    ∀ b : Fin n, ¬ Relation.TransGen (fun x y => decodeState n l x = some y) b b

/-- Well-formedness of an instance: the initial and goal lists are configurations of the same
`n = |I|` blocks, and `L > 0`. -/
def WellFormed (i : OptimalBlocksWorldPlanningInstance) : Prop :=
  IsConfiguration i.1.length i.1 ∧ IsConfiguration i.1.length i.2.1 ∧ 0 < i.2.2

/-- Block `b` is clear in state `s`: no block sits on it. -/
def Clear {n : ℕ} (s : State n) (b : Fin n) : Prop :=
  ∀ a, s a ≠ some b

/-- One move from `s` to `t`: a clear block `b` moves either from another block onto the
table, or onto another clear block `d`. -/
def Move {n : ℕ} (s t : State n) : Prop :=
  ∃ b, Clear s b ∧
    ((s b ≠ none ∧ t = Function.update s b none) ∨
      ∃ d, d ≠ b ∧ Clear s d ∧ t = Function.update s b (some d))

/-- Some plan of at most `L` moves leads from the initial state to the goal state: the states
`I = s₀, s₁, …, s_k = G` with `k ≤ L`, each obtained from the previous one by a move. -/
def OptimalBlocksWorldPlanningFeasible (i : OptimalBlocksWorldPlanningInstance) : Prop :=
  ∃ ps : List (State i.1.length), ps.length ≤ i.2.2 ∧
    List.IsChain Move (decodeState i.1.length i.1 :: ps) ∧
    (decodeState i.1.length i.1 :: ps).getLast (List.cons_ne_nil _ _) =
      decodeState i.1.length i.2.1

open Classical in
/-- OPTIMAL BLOCKS-WORLD PLANNING as a decision problem over bitstrings. -/
noncomputable def optimalBlocksWorldPlanningDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OptimalBlocksWorldPlanningInstance) x with
  | some i => decide (WellFormed i ∧ OptimalBlocksWorldPlanningFeasible i)
  | none => false

/-- **OPTIMAL BLOCKS-WORLD PLANNING is NP-complete.** Source: Gupta and Nau (1992). -/
public theorem_wanted optimalBlocksWorldPlanning_npComplete :
    optimalBlocksWorldPlanningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L optimalBlocksWorldPlanningDec

end MetaMathlibExt.Complexity.NPComplete.OptimalBlocksWorldPlanning
