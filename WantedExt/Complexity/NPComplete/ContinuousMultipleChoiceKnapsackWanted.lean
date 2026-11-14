/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONTINUOUS MULTIPLE CHOICE KNAPSACK is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP11] CONTINUOUS
MULTIPLE CHOICE KNAPSACK;
T. Ibaraki, "Approximate algorithms for the multiple-choice continuous knapsack
problems", Journal of the Operations Research Society of Japan 23 (1980), 28-63,
doi:10.15807/jorsj.23.28.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsack

/-!
# CONTINUOUS MULTIPLE CHOICE KNAPSACK is NP-complete

INSTANCE: a finite set `U`, for each `u ∈ U` a size `s(u) ∈ ℤ⁺` and a value `v(u) ∈ ℤ⁺`, a
partition of `U` into disjoint sets `U₁, U₂, …, Uₘ`, and positive integers `B` and `K`.
QUESTION: is there a choice of a unique element `uᵢ ∈ Uᵢ`, `1 ≤ i ≤ m`, and an assignment of
rational numbers `rᵢ`, `0 ≤ rᵢ ≤ 1`, to these elements, such that `∑ rᵢ s(uᵢ) ≤ B` and
`∑ rᵢ v(uᵢ) ≥ K`?

The partition is given block by block: a list of `m` nonempty lists, block `Uᵢ` listing its
elements as (size, value) pairs. The choice is a list with one entry from each block, in block
order (`List.Forall₂ (· ∈ ·)`, the shape of CSLibExt's
`Cslib.Algorithms.Lean.MultipleChoiceKnapsack.IsSelection`), and `rᵢ` is the `i`-th entry of a
list of rationals of the same length. The problem is NP-complete in the ordinary sense for the
binary encoding of the numbers (it is solvable in pseudo-polynomial time).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the blocks `U₁, …, Uₘ` of the partition, each a list of (size, value) pairs,
then the bounds `B` and `K`. -/
abbrev ContinuousMultipleChoiceKnapsackInstance := List (List (ℕ × ℕ)) × ℕ × ℕ

/-- Well-formedness of an instance: every block is nonempty, every size and value is positive,
and `B` and `K` are positive. -/
def WellFormed (i : ContinuousMultipleChoiceKnapsackInstance) : Prop :=
  (∀ g ∈ i.1, g ≠ [] ∧ ∀ u ∈ g, 0 < u.1 ∧ 0 < u.2) ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- One element `uᵢ` is chosen from each block `Uᵢ`, with rational weights `0 ≤ rᵢ ≤ 1`, such
that `∑ rᵢ s(uᵢ) ≤ B` and `∑ rᵢ v(uᵢ) ≥ K`. -/
def ContinuousMultipleChoiceKnapsackFeasible (i : ContinuousMultipleChoiceKnapsackInstance) :
    Prop :=
  ∃ choice : List (ℕ × ℕ), List.Forall₂ (fun u g => u ∈ g) choice i.1 ∧
    ∃ r : List ℚ, r.length = choice.length ∧ (∀ q ∈ r, 0 ≤ q ∧ q ≤ 1) ∧
      (List.zipWith (fun q u => q * (u.1 : ℚ)) r choice).sum ≤ (i.2.1 : ℚ) ∧
      (i.2.2 : ℚ) ≤ (List.zipWith (fun q u => q * (u.2 : ℚ)) r choice).sum

open Classical in
/-- CONTINUOUS MULTIPLE CHOICE KNAPSACK as a decision problem over bitstrings. -/
noncomputable def continuousMultipleChoiceKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ContinuousMultipleChoiceKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ ContinuousMultipleChoiceKnapsackFeasible i)
  | none => false

/-- **CONTINUOUS MULTIPLE CHOICE KNAPSACK is NP-complete.** Source: Garey and Johnson (1979),
[MP11]; Ibaraki (1980). -/
public theorem_wanted continuousMultipleChoiceKnapsack_npComplete :
    continuousMultipleChoiceKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L continuousMultipleChoiceKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsack
