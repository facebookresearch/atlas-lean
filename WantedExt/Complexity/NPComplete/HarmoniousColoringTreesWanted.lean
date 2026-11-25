/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HARMONIOUS COLORING OF TREES is NP-complete

Source:
K. Edwards and C. McDiarmid, "The complexity of harmonious colouring for trees", Discrete
Applied Mathematics 57 (1995), 133-144, doi:10.1016/0166-218X(94)00100-R.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HarmoniousColoringWanted
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HarmoniousColoringTrees

/-!
# HARMONIOUS COLORING OF TREES is NP-complete

INSTANCE: a tree `T` and a positive integer `K`. QUESTION: does `T` have a harmonious coloring
with at most `K` colors, that is, a proper vertex coloring in which every pair of colors appears
on at most one edge?

This is HARMONIOUS COLORING (`WantedExt.Complexity.NPComplete.HarmoniousColoringWanted`)
restricted to trees: the instance, the graph, the well-formedness conditions and the question
are that module's, and the restriction (Mathlib's `SimpleGraph.IsTree`) is an extra conjunct of
`WellFormed`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MetaMathlibExt.Complexity.NPComplete.HarmoniousColoring
  (HarmoniousColoringInstance Graph HarmoniousColoringFeasible)

/-- Well-formedness of an instance: well-formed for HARMONIOUS COLORING (simple edge list,
`0 < K`), and the graph is a tree. -/
def WellFormed (i : HarmoniousColoringInstance) : Prop :=
  MetaMathlibExt.Complexity.NPComplete.HarmoniousColoring.WellFormed i ∧ (Graph i).IsTree

open Classical in
/-- HARMONIOUS COLORING OF TREES as a decision problem over bitstrings. -/
noncomputable def harmoniousColoringTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HarmoniousColoringInstance) x with
  | some i => decide (WellFormed i ∧ HarmoniousColoringFeasible i)
  | none => false

/-- **HARMONIOUS COLORING OF TREES is NP-complete.** Source: Edwards and McDiarmid (1995). -/
public theorem_wanted harmoniousColoringTrees_npComplete :
    harmoniousColoringTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L harmoniousColoringTreesDec

end MetaMathlibExt.Complexity.NPComplete.HarmoniousColoringTrees
