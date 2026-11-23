/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARATIVE CONTAINMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP10] COMPARATIVE CONTAINMENT,
p. 223 ("Reference: [Plaisted, 1976]. Transformation from VERTEX COVER.");
D. A. Plaisted, "Some polynomial and integer divisibility problems are NP-hard",
Proc. 17th Annual Symposium on Foundations of Computer Science (FOCS 1976), 264-267,
doi:10.1109/SFCS.1976.29.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeContainment

/-!
# COMPARATIVE CONTAINMENT is NP-complete

INSTANCE: two collections `R = {R₁, …, R_k}` and `S = {S₁, …, S_l}` of subsets of a finite set
`X`, weights `w(R_i) ∈ ℤ⁺`, `1 ≤ i ≤ k`, and `w(S_j) ∈ ℤ⁺`, `1 ≤ j ≤ l`. QUESTION: is there a
subset `Y ⊆ X` such that `∑_{Y ⊆ R_i} w(R_i) ≥ ∑_{Y ⊆ S_j} w(S_j)`?

The ground set is `X = Fin n`. Each collection is an indexed list of (subset, weight) pairs,
as `R₁, …, R_k` with one weight per index; a subset is a list of distinct elements of `X`.
Weights use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the size `n` of `X = Fin n`, the collection `R` as a list of pairs
`(R_i, w(R_i))`, and the collection `S` as a list of pairs `(S_j, w(S_j))`. -/
abbrev ComparativeContainmentInstance := ℕ × List (List ℕ × ℕ) × List (List ℕ × ℕ)

/-- A weighted subset `(T, w)` of `Fin n` is well formed when `T` lists distinct elements of
`Fin n` and the weight `w` is positive. -/
def WeightedSubsetWellFormed (n : ℕ) (T : List ℕ × ℕ) : Prop :=
  T.1.Nodup ∧ (∀ x ∈ T.1, x < n) ∧ 0 < T.2

/-- Well-formedness of an instance: every member of `R` and of `S` is a subset of `X` with a
positive weight. -/
def WellFormed (i : ComparativeContainmentInstance) : Prop :=
  (∀ T ∈ i.2.1, WeightedSubsetWellFormed i.1 T) ∧ ∀ T ∈ i.2.2, WeightedSubsetWellFormed i.1 T

/-- The total weight `∑_{Y ⊆ T} w(T)` of the members `T` of a weighted collection that
contain `Y`. -/
def containingWeight {n : ℕ} (C : List (List ℕ × ℕ)) (Y : Finset (Fin n)) : ℕ :=
  (C.map fun T => if ∀ y ∈ Y, (y : ℕ) ∈ T.1 then T.2 else 0).sum

/-- Some subset `Y ⊆ X` has `∑_{Y ⊆ R_i} w(R_i) ≥ ∑_{Y ⊆ S_j} w(S_j)`. -/
def ComparativeContainmentFeasible (i : ComparativeContainmentInstance) : Prop :=
  ∃ Y : Finset (Fin i.1), containingWeight i.2.2 Y ≤ containingWeight i.2.1 Y

open Classical in
/-- COMPARATIVE CONTAINMENT as a decision problem over bitstrings. -/
noncomputable def comparativeContainmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ComparativeContainmentInstance) x with
  | some i => decide (WellFormed i ∧ ComparativeContainmentFeasible i)
  | none => false

/-- **COMPARATIVE CONTAINMENT is NP-complete.** Source: Garey and Johnson (1979), [SP10];
Plaisted (1976). -/
public theorem_wanted comparativeContainment_npComplete :
    comparativeContainmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L comparativeContainmentDec

end MetaMathlibExt.Complexity.NPComplete.ComparativeContainment
