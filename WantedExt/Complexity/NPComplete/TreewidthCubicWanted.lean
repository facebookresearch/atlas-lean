/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF CUBIC GRAPHS is NP-complete

Source:
H. L. Bodlaender, É. Bonnet, L. Jaffke, D. Knop, P. T. Lima, M. Milanič, S. Ordyniak, S. Pandey
and O. Suchý, "Treewidth is NP-complete on cubic graphs", Electronic Journal of Combinatorics
32(3) (2025), #P3.36, doi:10.37236/13205 (arXiv:2301.10031, "Treewidth is NP-complete on cubic
graphs (and related results)", Theorem 4.1: "Treewidth is NP-complete on regular graphs of
degree 3").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TreewidthWanted
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthCubic

open MetaMathlibExt.Complexity.NPComplete.Treewidth

/-!
# TREEWIDTH OF CUBIC GRAPHS is NP-complete

INSTANCE: a cubic graph `G = (V, E)` (every vertex has degree exactly 3) and an integer `K`.
QUESTION: is the treewidth of `G` at most `K`?

This is TREEWIDTH (`WantedExt.Complexity.NPComplete.TreewidthWanted`) restricted to cubic
graphs: the instance type, graph, well-formedness and question are those of that module, and
the restriction `SimpleGraph.IsRegularOfDegree 3` (Mathlib) is added to well-formedness.
Bodlaender et al. define "a graph `G` is `d`-regular if each vertex has degree `d`" and "`G` is
cubic if `G` is 3-regular", and prove NP-completeness in their Theorem 4.1.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is cubic: every vertex has degree exactly 3. -/
def CubicWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ (Graph i).IsRegularOfDegree 3

open Classical in
/-- TREEWIDTH OF CUBIC GRAPHS as a decision problem over bitstrings. -/
noncomputable def treewidthCubicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (CubicWellFormed i ∧ TreewidthFeasible i)
  | none => false

/-- **TREEWIDTH OF CUBIC GRAPHS is NP-complete.** Source: Bodlaender et al. (2025),
Theorem 4.1. -/
public theorem_wanted treewidthCubic_npComplete :
    treewidthCubicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treewidthCubicDec

end MetaMathlibExt.Complexity.NPComplete.TreewidthCubic
