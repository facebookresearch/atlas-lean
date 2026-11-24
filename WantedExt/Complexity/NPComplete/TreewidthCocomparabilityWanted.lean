/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF COCOMPARABILITY GRAPHS is NP-complete

Source:
H. L. Bodlaender, "A tourist guide through treewidth", Acta Cybernetica 11 (1993), 1-21
(Table 1: TREEWIDTH is NP-complete on cocomparability graphs, citing Arnborg, Corneil and
Proskurowski and Habib and Möhring);
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024;
M. Habib and R. H. Möhring, "Treewidth of cocomparability graphs and a new order-theoretic
parameter", Order 11 (1994), 47-60, doi:10.1007/BF01462229;
H. L. Bodlaender, É. Bonnet, L. Jaffke, D. Knop, P. T. Lima, M. Milanič, S. Ordyniak, S. Pandey
and O. Suchý, "Treewidth is NP-complete on cubic graphs", Electronic Journal of Combinatorics
32(3) (2025), #P3.36, doi:10.37236/13205 (arXiv:2301.10031, Corollary 3.2: "Treewidth is
NP-complete on co-bipartite graphs", attributed in Section 1 to Arnborg, Corneil and
Proskurowski).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted
public import WantedExt.Complexity.NPComplete.TreewidthWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthCocomparability

open MetaMathlibExt.Complexity.NPComplete.Treewidth

/-!
# TREEWIDTH OF COCOMPARABILITY GRAPHS is NP-complete

INSTANCE: a cocomparability graph `G = (V, E)` (its complement is a comparability graph) and an
integer `K`.
QUESTION: is the treewidth of `G` at most `K`?

This is TREEWIDTH (`WantedExt.Complexity.NPComplete.TreewidthWanted`) restricted to
cocomparability graphs: the instance type, graph, well-formedness and question are those of that
module, and the restriction is added to well-formedness. The complement is Mathlib's `Gᶜ`, and
comparability graphs are `ComparabilityGraphSandwich.IsComparabilityGraph` (some strict partial
order makes two vertices adjacent exactly when they are comparable), as in
`PathwidthCocomparabilityGraphsWanted`. Co-bipartite graphs (complements of bipartite graphs) are
cocomparability graphs, since a bipartite graph is the comparability graph of the order that puts
one side below the other; so Corollary 3.2 of Bodlaender et al. (co-bipartite graphs) gives the
hardness. ISGCI (class `gc_147`) records TREEWIDTH as NP-complete on this class, citing Bodlaender
(1993).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is a cocomparability graph: its complement is a comparability graph. -/
def CocomparabilityWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ ComparabilityGraphSandwich.IsComparabilityGraph (Graph i)ᶜ

open Classical in
/-- TREEWIDTH OF COCOMPARABILITY GRAPHS as a decision problem over bitstrings. -/
noncomputable def treewidthCocomparabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (CocomparabilityWellFormed i ∧ TreewidthFeasible i)
  | none => false

/-- **TREEWIDTH OF COCOMPARABILITY GRAPHS is NP-complete.** Source: Bodlaender (1993), Table 1;
Arnborg, Corneil and Proskurowski (1987); Bodlaender et al. (2025), Corollary 3.2. -/
public theorem_wanted treewidthCocomparability_npComplete :
    treewidthCocomparabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treewidthCocomparabilityDec

end MetaMathlibExt.Complexity.NPComplete.TreewidthCocomparability
