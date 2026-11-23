/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMATIC NUMBER for fixed K ≥ 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT3] DOMATIC NUMBER, p. 190
(comment: "Remains NP-complete for any fixed K ≥ 3"; reference: Garey, Johnson, and Tarjan,
1976b).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DomaticNumberWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DomaticNumberFixedK

/-!
# DOMATIC NUMBER for fixed K ≥ 3 is NP-complete

For a fixed integer `K ≥ 3`:

INSTANCE: a graph `G = (V, E)`.
QUESTION: is the domatic number of `G` at least `K`, i.e. can `V` be partitioned into `k ≥ K`
disjoint sets `V₁, ..., Vₖ` such that each `Vᵢ` is a dominating set for `G`?

This is DOMATIC NUMBER ([GT3], `DomaticNumberWanted`) with the bound `K` fixed instead of part
of the instance. An instance is a graph `(n, E)`; it is decided as the DOMATIC NUMBER instance
`(n, E, K)` (`withBound K`), whose `DomaticNumber.WellFormed` (simple edge list,
`0 < K ≤ |V|`) and `DomaticNumber.DomaticNumberFeasible` are reused unchanged. A graph with
fewer than `K` vertices is therefore a no-instance: a partition of fewer than `K` vertices into
`K` or more sets has an empty set, which dominates no nonempty graph. Garey and Johnson note
that the domatic number is at least 2 unless `G` has an isolated vertex, so the fixed-`K`
problem is easy for `K ≤ 2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list; the bound `K` is fixed. -/
abbrev DomaticNumberFixedKInstance := ℕ × List (ℕ × ℕ)

/-- The DOMATIC NUMBER instance `(n, E, K)` of a graph `(n, E)` and the fixed bound `K`. -/
def withBound (K : ℕ) (i : DomaticNumberFixedKInstance) :
    DomaticNumber.DomaticNumberInstance :=
  (i.1, i.2, K)

open Classical in
/-- DOMATIC NUMBER for a fixed bound `K` as a decision problem over bitstrings. -/
noncomputable def domaticNumberFixedKDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DomaticNumberFixedKInstance) x with
  | some i => decide (DomaticNumber.WellFormed (withBound K i) ∧
      DomaticNumber.DomaticNumberFeasible (withBound K i))
  | none => false

/-- **DOMATIC NUMBER is NP-complete for every fixed `K ≥ 3`.** Source: Garey and Johnson (1979),
[GT3], comment (Garey, Johnson, and Tarjan, 1976b). -/
public theorem_wanted domaticNumberFixedK_npComplete (K : ℕ) (hK : 3 ≤ K) :
    domaticNumberFixedKDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (domaticNumberFixedKDec K)

end MetaMathlibExt.Complexity.NPComplete.DomaticNumberFixedK
