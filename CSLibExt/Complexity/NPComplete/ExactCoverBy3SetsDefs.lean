/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

/-!
# EXACT COVER BY 3-SETS: definitions

A universe of size `3q` (elements `0, …, 3q - 1`) and a list of three-element subsets. The
question is whether some subcollection covers every element exactly once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EXACT COVER BY 3-SETS.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3Sets

/-- **Instances of EXACT COVER BY 3-SETS.** An instance of EXACT COVER BY 3-SETS is a pair
$(q, C)$ of a natural number $q$ and a finite list $C$ of finite lists of natural numbers. The
intended universe is $\{0, \dots, 3q - 1\}$ and the entries of $C$ are the candidate
three-element subsets; that each entry lists three distinct elements of the universe is
required by well-formedness, not by the type of instances. -/
abbrev ExactCoverBy3SetsInstance := ℕ × List (List ℕ)

/-- **Well-formed EXACT COVER BY 3-SETS instances.** An instance $(q, C)$ of EXACT COVER BY
3-SETS is well formed when every entry of $C$ is a list of exactly three pairwise distinct
natural numbers, each less than $3q$. -/
def WellFormed (i : ExactCoverBy3SetsInstance) : Prop :=
  ∀ s ∈ i.2, s.length = 3 ∧ s.Nodup ∧ ∀ x ∈ s, x < 3 * i.1

/-- **Feasible EXACT COVER BY 3-SETS instances.** An instance $(q, C)$ of EXACT COVER BY 3-SETS
is feasible when $C$ has a sublist $S$, obtained by deleting some entries of $C$, such that for
every natural number $x < 3q$ there is exactly one list that occurs in $S$ and contains $x$. -/
def ExactCoverBy3SetsFeasible
    (i : ExactCoverBy3SetsInstance) : Prop :=
  ∃ sub : List (List ℕ), sub.Sublist i.2 ∧
    ∀ x < 3 * i.1, ∃! s ∈ sub, x ∈ s

open Classical in
/-- **EXACT COVER BY 3-SETS as a decision problem.** The decision problem EXACT COVER BY 3-SETS
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs
of a natural number and a list of lists of natural numbers, to an instance of EXACT COVER BY
3-SETS that is well formed and feasible; bitstrings that do not decode are rejected. -/
noncomputable def exactCoverBy3SetsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExactCoverBy3SetsInstance) x with
  | some i => decide (WellFormed i ∧ ExactCoverBy3SetsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3Sets
