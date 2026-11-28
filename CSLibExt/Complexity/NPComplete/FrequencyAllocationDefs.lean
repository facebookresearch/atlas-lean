/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FREQUENCY ALLOCATION: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MAXIMUM FREQUENCY ALLOCATION;
E. Malesińska and A. Panconesi, "On the hardness of allocating frequencies for hybrid networks",
Theoret. Comput. Sci. 209 (1998), 347-363, doi:10.1016/S0304-3975(98)00156-X (the channel
stability number; Section 1: the problem generalizes list coloring);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ListColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FrequencyAllocation

/-- An instance: node count `n`, edge list, lists `L(u)` of available frequencies, bounds
`M_u` and the bound `K`. -/
abbrev FrequencyAllocationInstance := ℕ × List (ℕ × ℕ) × List (List ℕ) × List ℕ × ℕ

/-- Well-formedness of an instance: the graph and the `n` frequency lists form a well-formed
LIST COLORING instance; each list has distinct positive entries; there is one bound `M_u` per
node; and `0 < K`. -/
def WellFormed (i : FrequencyAllocationInstance) : Prop :=
  ListColoring.WellFormed (i.1, i.2.1, i.2.2.1) ∧
    (∀ l ∈ i.2.2.1, l.Nodup ∧ ∀ x ∈ l, 0 < x) ∧ i.2.2.2.1.length = i.1 ∧ 0 < i.2.2.2.2

/-- An allocation `S` with stability number at least `K`: each node `u` gets between `1` and
`M_u` distinct frequencies from `L(u)`, adjacent nodes get disjoint sets, and the sizes sum to at
least `K`. -/
def FrequencyAllocationFeasible (i : FrequencyAllocationInstance) : Prop :=
  ∃ S : List (List ℕ), S.length = i.1 ∧
    (∀ u < i.1, (S.getD u []).Nodup ∧ S.getD u [] ⊆ i.2.2.1.getD u [] ∧
      1 ≤ (S.getD u []).length ∧ (S.getD u []).length ≤ i.2.2.2.1.getD u 0) ∧
    (∀ e ∈ i.2.1, (S.getD e.1 []).Disjoint (S.getD e.2 [])) ∧
    i.2.2.2.2 ≤ (S.map List.length).sum

open Classical in
/-- FREQUENCY ALLOCATION as a decision problem over bitstrings. -/
noncomputable def frequencyAllocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FrequencyAllocationInstance) x with
  | some i => decide (WellFormed i ∧ FrequencyAllocationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FrequencyAllocation
