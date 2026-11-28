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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OptimalBlocksWorldPlanningDefs

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

/-- **OPTIMAL BLOCKS-WORLD PLANNING is NP-complete.** Source: Gupta and Nau (1992). -/
public theorem_wanted optimalBlocksWorldPlanning_npComplete :
    optimalBlocksWorldPlanningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L optimalBlocksWorldPlanningDec

end MetaMathlibExt.Complexity.NPComplete.OptimalBlocksWorldPlanning
