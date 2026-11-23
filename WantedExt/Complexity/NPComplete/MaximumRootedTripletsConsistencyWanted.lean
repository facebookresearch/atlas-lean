/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM ROOTED TRIPLETS CONSISTENCY is NP-complete

Source:
J. Jansson, "On the complexity of inferring rooted evolutionary trees", Electronic Notes in
Discrete Mathematics 7 (2001), 50-53, doi:10.1016/S1571-0653(04)00222-7;
D. Bryant, *Building Trees, Hunting for Trees, and Comparing Trees: Theory and Methods in
Phylogenetic Analysis*, PhD thesis, University of Canterbury (1997);
B. Y. Wu, "Constructing the maximum consensus tree from rooted triples", Journal of
Combinatorial Optimization 8 (2004), 29-39, doi:10.1023/B:JOCO.0000021936.04215.68.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Bioinformatics.Phylogenetics.Splits

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumRootedTripletsConsistency

open Cslib.Bioinformatics.Phylogenetics.Splits (IsHierarchy Triplet DisplaysTriplet)

/-!
# MAXIMUM ROOTED TRIPLETS CONSISTENCY is NP-complete

INSTANCE: a finite set `X` of species, a set `R` of rooted triplets `ab|c` (three distinct
species of `X`), and an integer `K`.
QUESTION: is there a rooted phylogenetic tree with leaf set `X` that is consistent with at least
`K` triplets of `R`? A tree is consistent with `ab|c` when the lowest common ancestor of `a`
and `b` is a proper descendant of the lowest common ancestor of `a`, `b` and `c`.

The species are `X = {0, ..., n - 1}` with `n > 0` (there is no rooted tree with an empty leaf
set). A triplet `ab|c` is the triple `(a, b, c)`, listed with `a < b` since `ab|c` and `ba|c` are
the same triplet, and no triplet is listed twice, so the list is the set `R`. A tree is given by
its cluster system: the leaf sets below its vertices. The cluster systems of the rooted trees
with leaf set `X` are exactly the hierarchies on `X` (`IsHierarchy`), and a tree is consistent
with `ab|c` iff some cluster contains `a` and `b` but not `c` (`DisplaysTriplet`). Every
hierarchy is contained in a binary one (`exists_isBinaryHierarchy_superset`), and adding
clusters keeps every displayed triplet displayed, so the question has the same answer whether
the tree is required to be binary, as in some of the sources, or not.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MAXIMUM ROOTED TRIPLETS CONSISTENCY is NP-complete.** Source: Jansson (2001); Bryant
(1997); Wu (2004). -/
public theorem_wanted maximumRootedTripletsConsistency_npComplete :
    maximumRootedTripletsConsistencyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumRootedTripletsConsistencyDec

end MetaMathlibExt.Complexity.NPComplete.MaximumRootedTripletsConsistency
