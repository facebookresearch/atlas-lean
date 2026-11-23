/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONTINUOUS MULTIPLE CHOICE KNAPSACK with blocks of at most two elements is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP11] CONTINUOUS MULTIPLE CHOICE
KNAPSACK, comment (p. 247): "Solvable in pseudo-polynomial time, but remains NP-complete even
if `|Uᵢ| ≤ 2`, `1 ≤ i ≤ m`" (reference of the entry: [Ibaraki, 1978]; transformation from
PARTITION);
T. Ibaraki, "Approximate algorithms for the multiple-choice continuous knapsack problems",
Journal of the Operations Research Society of Japan 23 (1980), 28-63,
doi:10.15807/jorsj.23.28.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsackWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsackTwoElementBlocks

open ContinuousMultipleChoiceKnapsack (ContinuousMultipleChoiceKnapsackInstance
  ContinuousMultipleChoiceKnapsackFeasible)

/-!
# CONTINUOUS MULTIPLE CHOICE KNAPSACK with blocks of at most two elements is NP-complete

INSTANCE: a finite set `U`, for each `u ∈ U` a size `s(u) ∈ Z⁺` and a value `v(u) ∈ Z⁺`, a
partition of `U` into disjoint sets `U₁, U₂, …, U_m` with `|Uᵢ| ≤ 2` for `1 ≤ i ≤ m`, and
positive integers `B` and `K`.
QUESTION: is there a choice of a unique element `uᵢ ∈ Uᵢ`, `1 ≤ i ≤ m`, and an assignment of
rational numbers `rᵢ`, `0 ≤ rᵢ ≤ 1`, to these elements, such that `∑ rᵢ · s(uᵢ) ≤ B` and
`∑ rᵢ · v(uᵢ) ≥ K`?

This is the restriction of [MP11] CONTINUOUS MULTIPLE CHOICE KNAPSACK
(`WantedExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsackWanted`) stated in its comment.
The instance type (the blocks `Uᵢ` as lists of `(s(u), v(u))` pairs, `B`, `K`),
`ContinuousMultipleChoiceKnapsack.WellFormed` (nonempty blocks, positive sizes, values and
bounds) and `ContinuousMultipleChoiceKnapsackFeasible` are reused unchanged; the restriction
`|Uᵢ| ≤ 2` is added to well-formedness. The comment also notes the problem is solvable by greedy
algorithms when every `|Uᵢ| = 1`, so blocks of two elements are where hardness appears. Numbers
use the binary encoding (the problem is solvable in pseudo-polynomial time).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed CONTINUOUS MULTIPLE CHOICE KNAPSACK instance
whose blocks have at most two elements. -/
def WellFormed (i : ContinuousMultipleChoiceKnapsackInstance) : Prop :=
  ContinuousMultipleChoiceKnapsack.WellFormed i ∧ ∀ g ∈ i.1, g.length ≤ 2

open Classical in
/-- CONTINUOUS MULTIPLE CHOICE KNAPSACK with blocks of at most two elements as a decision
problem over bitstrings. -/
noncomputable def continuousMultipleChoiceKnapsackTwoElementBlocksDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ContinuousMultipleChoiceKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ ContinuousMultipleChoiceKnapsackFeasible i)
  | none => false

/-- **CONTINUOUS MULTIPLE CHOICE KNAPSACK with blocks of at most two elements is NP-complete.**
Source: Garey and Johnson (1979), [MP11], comment; Ibaraki (1980). -/
public theorem_wanted continuousMultipleChoiceKnapsackTwoElementBlocks_npComplete :
    continuousMultipleChoiceKnapsackTwoElementBlocksDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L continuousMultipleChoiceKnapsackTwoElementBlocksDec

end MetaMathlibExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsackTwoElementBlocks
