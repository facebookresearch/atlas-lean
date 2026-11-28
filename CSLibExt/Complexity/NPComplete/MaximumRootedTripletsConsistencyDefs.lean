/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM ROOTED TRIPLETS CONSISTENCY: definitions

Source:
J. Jansson, "On the complexity of inferring rooted evolutionary trees", Electronic Notes in
Discrete Mathematics 7 (2001), 50-53, doi:10.1016/S1571-0653(04)00222-7;
D. Bryant, *Building Trees, Hunting for Trees, and Comparing Trees: Theory and Methods in
Phylogenetic Analysis*, PhD thesis, University of Canterbury (1997);
B. Y. Wu, "Constructing the maximum consensus tree from rooted triples", Journal of
Combinatorial Optimization 8 (2004), 29-39, doi:10.1023/B:JOCO.0000021936.04215.68.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Bioinformatics.Phylogenetics.Splits

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumRootedTripletsConsistency

open Cslib.Bioinformatics.Phylogenetics.Splits (IsHierarchy Triplet DisplaysTriplet)

/-- An instance: the number `n` of species, the triplets `ab|c` as triples `(a, b, c)`, and the
bound `K`. -/
abbrev MaximumRootedTripletsConsistencyInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: there is at least one species, every triplet consists of
three distinct species listed with `a < b`, and no triplet is listed twice. -/
def WellFormed (i : MaximumRootedTripletsConsistencyInstance) : Prop :=
  0 < i.1 ∧ (∀ t ∈ i.2.1, t.1 < t.2.1 ∧ t.2.1 < i.1 ∧ t.2.2 < i.1 ∧ t.2.2 ≠ t.1 ∧
    t.2.2 ≠ t.2.1) ∧ i.2.1.Nodup

/-- Some rooted tree with leaf set `X`, given by its hierarchy of clusters, is consistent with
at least `K` of the triplets. -/
def MaximumRootedTripletsConsistencyFeasible
    (i : MaximumRootedTripletsConsistencyInstance) : Prop :=
  ∃ H : Finset (Finset ℕ), IsHierarchy (Finset.range i.1) H ∧
    ∃ R : List (ℕ × ℕ × ℕ), R.Sublist i.2.1 ∧ i.2.2 ≤ R.length ∧
      ∀ t ∈ R, DisplaysTriplet H ⟨t.1, t.2.1, t.2.2⟩

open Classical in
/-- MAXIMUM ROOTED TRIPLETS CONSISTENCY as a decision problem over bitstrings. -/
noncomputable def maximumRootedTripletsConsistencyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumRootedTripletsConsistencyInstance) x with
  | some i => decide (WellFormed i ∧ MaximumRootedTripletsConsistencyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumRootedTripletsConsistency
