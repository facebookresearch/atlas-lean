/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STACKER-CRANE PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND26] STACKER-CRANE, comment
(p. 213: "The analogous path problem (with or without specified endpoints) is also
NP-complete");
G. N. Frederickson, M. S. Hecht, and C. E. Kim, "Approximation algorithms for
some routing problems", SIAM Journal on Computing 7 (1978), 178-193,
doi:10.1137/0207017 (the entry's reference for STACKER-CRANE).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.StackerCraneWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StackerCranePath

open MetaMathlibExt.Complexity.NPComplete.StackerCrane (StackerCraneInstance moves)

/-!
# STACKER-CRANE PATH is NP-complete

INSTANCE: a mixed graph `G = (V, A, E)` (`A` directed edges, `E` undirected edges), a length
`l(e) ∈ ℤ₀⁺` for each `e ∈ A ∪ E`, and a bound `B ∈ ℤ⁺`. QUESTION: is there a path in `G`
that includes each directed edge in `A` at least once, traversing such edges only in the
specified direction, and that has total length no more than `B`?

This is the path analogue, without specified endpoints, recorded in the comment of Garey and
Johnson's [ND26] STACKER-CRANE (`StackerCraneWanted`). The instance type, the list of allowed
traversals `StackerCrane.moves` and `StackerCrane.WellFormed` are the parent's, unchanged. As
the parent's cycle is a closed walk, the path is a walk (edges may be repeated, as "at least
once" requires) that need not return to its start: a list of moves, each traversing a directed
edge from its tail to its head or an undirected edge in either direction, where each move
starts at the vertex where the previous one ended. Its length is the sum of the lengths of its
moves, counted with repetition; a walk with no moves stays at one vertex, so the empty graph
has no path. Numbers use the binary encoding. The comment's variant with
specified endpoints is a separate problem and is not stated here.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A walk, given as a list `c` of indices into `StackerCrane.moves i`, in which each move
starts where the previous one ends, every directed edge (index `< |A|`) occurs, and the total
length is at most `B`. A walk has a start vertex even when it has no moves, so `V` is
nonempty (`0 < n`). -/
def StackerCranePathFeasible (i : StackerCraneInstance) : Prop :=
  0 < i.1 ∧ ∃ c : List (Fin (moves i).length),
    (∀ j (h : j + 1 < c.length),
      ((moves i)[c[j]]).2.1 = ((moves i)[c[j + 1]]).1) ∧
    (∀ a : Fin (moves i).length, (a : ℕ) < i.2.1.length → a ∈ c) ∧
    (c.map fun m => ((moves i)[m]).2.2).sum ≤ i.2.2.2

open Classical in
/-- STACKER-CRANE PATH as a decision problem over bitstrings. -/
noncomputable def stackerCranePathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StackerCraneInstance) x with
  | some i => decide (StackerCrane.WellFormed i ∧ StackerCranePathFeasible i)
  | none => false

/-- **STACKER-CRANE PATH is NP-complete.** Source: Garey and Johnson (1979), [ND26],
comment. -/
public theorem_wanted stackerCranePath_npComplete :
    stackerCranePathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stackerCranePathDec

end MetaMathlibExt.Complexity.NPComplete.StackerCranePath
