/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXPECTED COMPONENT SUM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP18] EXPECTED COMPONENT SUM,
pp. 224-225 ("Reference: [Garey and Johnson, ——]. Transformation from X3C. The problem is due
to [Witsenhausen, 1978] and corresponds to finding a partition that maximizes the expected
value of the largest component sum, assuming all sets in the partition are equally likely.").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSum

/-!
# EXPECTED COMPONENT SUM is NP-complete

INSTANCE: a collection `C` of `m`-dimensional vectors `v = (v₁, v₂, …, v_m)` with non-negative
integer entries, positive integers `K` and `B`. QUESTION: is there a partition of `C` into
disjoint sets `C₁, C₂, …, C_K` such that
`∑_{i=1}^{K} max_{1 ≤ j ≤ m} (∑_{v ∈ C_i} v_j) ≥ B`?

The vectors of `C` are indexed by `Fin |C|`, one per listed vector, so a vector may occur
more than once. A partition into `C₁, …, C_K` is a surjective map `f : Fin |C| → Fin K` with
`C_k = f⁻¹(k)`, so every block is non-empty and there is no partition when `K > |C|`. (For
`K ≤ |C|`, allowing empty blocks would not change the answer: moving one vector of a block with
two or more vectors into an empty block does not decrease the component sum.) The maximum over
`j` is `Finset.sup` in `ℕ`. All numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the dimension `m`, the vectors of `C` (each a list of `m` entries), the number
`K` of parts and the bound `B`. -/
abbrev ExpectedComponentSumInstance := ℕ × List (List ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: every vector has `m` entries, and `K` and `B` are
positive. -/
def WellFormed (i : ExpectedComponentSumInstance) : Prop :=
  (∀ v ∈ i.2.1, v.length = i.1) ∧ 0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- The component sum `∑_{k} max_{j < m} (∑_{v ∈ C_k} v_j)` of the partition of the vectors
`C` into the parts `C_k = f⁻¹(k)`. -/
def componentSum (m : ℕ) (C : List (List ℕ)) {K : ℕ} (f : Fin C.length → Fin K) : ℕ :=
  ∑ k : Fin K, Finset.univ.sup fun j : Fin m =>
    ∑ c ∈ Finset.univ.filter (fun c => f c = k), (C.get c).getD j 0

/-- Some partition of `C` into `K` non-empty disjoint sets has component sum at least `B`. -/
def ExpectedComponentSumFeasible (i : ExpectedComponentSumInstance) : Prop :=
  ∃ f : Fin i.2.1.length → Fin i.2.2.1, Function.Surjective f ∧
    i.2.2.2 ≤ componentSum i.1 i.2.1 f

open Classical in
/-- EXPECTED COMPONENT SUM as a decision problem over bitstrings. -/
noncomputable def expectedComponentSumDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExpectedComponentSumInstance) x with
  | some i => decide (WellFormed i ∧ ExpectedComponentSumFeasible i)
  | none => false

/-- **EXPECTED COMPONENT SUM is NP-complete.** Source: Garey and Johnson (1979), [SP18]. -/
public theorem_wanted expectedComponentSum_npComplete :
    expectedComponentSumDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L expectedComponentSumDec

end MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSum
