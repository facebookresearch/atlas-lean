/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EXACT COVER is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM EXACT COVER (decision version);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (EXACT COVER is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.ExactCoverWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumExactCover

/-!
# MINIMUM EXACT COVER is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `S`, and a bound `K`. QUESTION: is there
a set cover `C' ⊆ C` for `S` (every element of `S` belongs to some member of `C'`) with
`∑_{c ∈ C'} |c| ≤ K`?

This is the decision version of the compendium's MINIMUM EXACT COVER, whose only
difference from MINIMUM SET COVER is the objective (the total size of the chosen sets). A cover
has `∑_{c ∈ C'} |c| ≥ |S|`, with equality exactly when its members are pairwise disjoint, so
the case `K = |S|` is EXACT COVER, NP-complete by Karp (1972); that is the reduction behind the
theorem.

`S = {0, …, n - 1}` and the members of `C` are listed as lists of elements, with the
well-formedness of `ExactCoverWanted` (each member without repetition, so its length is its
size, and with elements below `n`). `C'` is a set of positions in the list, so a subset listed
twice in `C` is two members.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the size `n` of `S`, the members of `C` in order, and the bound `K`. -/
abbrev MinimumExactCoverInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: `(n, C)` is a well-formed `ExactCoverWanted` instance. -/
def WellFormed (i : MinimumExactCoverInstance) : Prop :=
  ExactCover.WellFormed (i.1, i.2.1)

/-- Some set `C'` of positions in the list of members covers every element of `S`, and the
lengths of the selected list entries sum to at most `K` (a member listed with a repeated element
counts it twice; for well-formed members the length is the size). -/
def MinimumExactCoverFeasible (i : MinimumExactCoverInstance) : Prop :=
  ∃ C' : Finset (Fin i.2.1.length), (∀ x < i.1, ∃ j ∈ C', x ∈ i.2.1.get j) ∧
    ∑ j ∈ C', (i.2.1.get j).length ≤ i.2.2

open Classical in
/-- MINIMUM EXACT COVER as a decision problem over bitstrings. -/
noncomputable def minimumExactCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumExactCoverInstance) x with
  | some i => decide (WellFormed i ∧ MinimumExactCoverFeasible i)
  | none => false

/-- **MINIMUM EXACT COVER is NP-complete.** Source: Crescenzi and Kann, MINIMUM EXACT COVER; Karp
(1972). -/
public theorem_wanted minimumExactCover_npComplete :
    minimumExactCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumExactCoverDec

end MetaMathlibExt.Complexity.NPComplete.MinimumExactCover
