/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTED DIAMETER with `K = 2` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT64] ORIENTED DIAMETER, p. 205
(comment: "Both problems remain NP-complete for `K = 2`.");
V. Chvátal and C. Thomassen, "Distances in orientations of graphs", Journal of
Combinatorial Theory, Series B 24 (1978), 61-75,
doi:10.1016/0095-8956(78)90078-3 (also Stanford report STAN-CS-75-517, 1975: deciding whether
a graph admits an orientation of diameter two is NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.OrientedDiameterWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OrientedDiameterTwo

/-!
# ORIENTED DIAMETER with `K = 2` is NP-complete

INSTANCE: a graph `G = (V, E)` (with `|V| ≥ 2`). QUESTION: can the edges of `G` be oriented
so that the resulting directed graph is strongly connected and has diameter no more than `2`?

This is the restriction of ORIENTED DIAMETER ([GT64], `OrientedDiameterWanted`) to instances
with `K = 2`. The instance type, `OrientedDiameter.WellFormed` and
`OrientedDiameter.OrientedDiameterFeasible` are the parent's, unchanged; `WellFormed` adds that
the bound is `2`. The parent's condition `K ≤ |V|` is kept, so graphs with fewer than two
vertices are not instances.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n` and
`0 < K ≤ |V|`) and `K = 2`. -/
def WellFormed (i : OrientedDiameter.OrientedDiameterInstance) : Prop :=
  OrientedDiameter.WellFormed i ∧ i.2.2 = 2

open Classical in
/-- ORIENTED DIAMETER with `K = 2` as a decision problem over bitstrings. -/
noncomputable def orientedDiameterTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OrientedDiameter.OrientedDiameterInstance) x with
  | some i => decide (WellFormed i ∧ OrientedDiameter.OrientedDiameterFeasible i)
  | none => false

/-- **ORIENTED DIAMETER is NP-complete for `K = 2`.** Source: Garey and Johnson (1979), [GT64],
comment; Chvátal and Thomassen (1978). -/
public theorem_wanted orientedDiameterTwo_npComplete :
    orientedDiameterTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L orientedDiameterTwoDec

end MetaMathlibExt.Complexity.NPComplete.OrientedDiameterTwo
