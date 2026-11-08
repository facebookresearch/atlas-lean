/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO PATHS OF LENGTH 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PARTITION INTO PATHS; M.
E. Dyer and A. M. Frieze, "On the complexity of partitioning graphs into connected subgraphs",
Discrete Applied Mathematics 10 (1985), 139-153.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoP3s

/-!
# PARTITION INTO PATHS OF LENGTH 2 is NP-complete

An undirected graph. The question is whether the vertices can be partitioned into triples, each
containing a path on three vertices: two consecutive edges of the triple. The path need not be
induced: a triangle triple qualifies, using two of its three edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list. -/
abbrev PartitionIntoP3sInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PartitionIntoP3sInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2


/-- Well-formedness of an instance. -/
def WellFormed (i : PartitionIntoP3sInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- A partition into paths of length 2. -/
def PartitionIntoP3sFeasible
    (i : PartitionIntoP3sInstance) : Prop :=
  ∃ triples : List (List (Fin i.1)), triples.flatten.Perm (List.finRange i.1) ∧
    (∀ t ∈ triples, t.length = 3 ∧ t.Nodup) ∧
    ∀ t ∈ triples, ∃ x ∈ t, ∃ y ∈ t, ∃ z ∈ t,
      x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ (Graph i).Adj x y ∧ (Graph i).Adj y z

open Classical in
/-- PARTITION INTO PATHS OF LENGTH 2 as a decision problem over bitstrings. -/
noncomputable def partitionIntoP3sDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoP3sInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoP3sFeasible i)
  | none => false

/-- **PARTITION INTO PATHS OF LENGTH 2 is NP-complete.** Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), PARTITION INTO PATHS; M. E. Dyer and A. M.
Frieze, "On the complexity of partitioning graphs into connected subgraphs", Discrete
Applied Mathematics 10 (1985), 139-153. -/
public theorem_wanted partitionIntoP3s_npComplete :
    partitionIntoP3sDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoP3sDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoP3s
