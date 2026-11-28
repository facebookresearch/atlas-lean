/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STACKER-CRANE PATH: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.StackerCraneDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StackerCranePath

open MetaMathlibExt.Complexity.NPComplete.StackerCrane (StackerCraneInstance moves)

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

end MetaMathlibExt.Complexity.NPComplete.StackerCranePath
