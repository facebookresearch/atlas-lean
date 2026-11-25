/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUBFOREST ISOMORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), Section 4.2, Theorem 4.6 ("SUBFOREST
ISOMORPHISM is NP-complete"), pp. 104-106, and problem [GT48] SUBGRAPH ISOMORPHISM, p. 202
(comment: "remains NP-complete if `G` is a tree and `H` is a forest (see Chapter 4)").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import WantedExt.Complexity.NPComplete.SubgraphIsomorphismWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SubforestIsomorphism

open MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphism
  (SubgraphIsomorphismInstance GraphHost)

/-!
# SUBFOREST ISOMORPHISM is NP-complete

INSTANCE: a tree `G = (V₁, E₁)` and a forest `H = (V₂, E₂)`. QUESTION: does `G` contain a
subgraph isomorphic to `H`, i.e., is there an injective map from `V₂` to `V₁` sending every edge
of `H` to an edge of `G`?

Garey and Johnson give the name SUBFOREST ISOMORPHISM to "the subproblem of SUBGRAPH ISOMORPHISM
in which `G` is required to be a tree and `H` is required to be a forest", and prove it
NP-complete in the strong sense (Theorem 4.6, by a pseudo-polynomial transformation from
3-PARTITION). This is the restriction of SUBGRAPH ISOMORPHISM
(`WantedExt.Complexity.NPComplete.SubgraphIsomorphismWanted`) to such instances. The instance
type, the host graph `G` (`SubgraphIsomorphism.GraphHost`), the parent well-formedness condition
(both edge lists simple) and the question are that module's; the restriction is added to
`WellFormed`. The pattern `H` is the same construction, `Cslib.Complexity.Karp.edgeGraph`, on
the pattern's vertex count and edge list. A tree is Mathlib's `SimpleGraph.IsTree` (connected,
which needs at least one vertex, and acyclic); a forest is an acyclic graph, Mathlib's
`SimpleGraph.IsAcyclic`.

Garey and Johnson's question asks for `V ⊆ V₁` and `E ⊆ E₁` with `|V| = |V₂|`, `|E| = |E₂|` and
a one-to-one `f : V₂ → V` with `{u, v} ∈ E₂` if and only if `{f(u), f(v)} ∈ E`; taking `E` to be
the image of `E₂` shows that this is the existence of an injective map sending every edge of `H`
to an edge of `G`, the parent's question.

The vertex counts are binary numbers, but `|V₁| ≤ |E₁| + 1` because `G` is a tree, and a
yes-instance has `|V₂| ≤ |V₁|`, so an injective map is a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed SUBGRAPH ISOMORPHISM instance (both edge
lists simple), the host `G` is a tree, and the pattern `H`, the graph
`Cslib.Complexity.Karp.edgeGraph |V₂| E₂`, is a forest. -/
def WellFormed (i : SubgraphIsomorphismInstance) : Prop :=
  SubgraphIsomorphism.WellFormed i ∧ (GraphHost i).IsTree ∧
    (Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2).IsAcyclic

open Classical in
/-- SUBFOREST ISOMORPHISM as a decision problem over bitstrings. -/
noncomputable def subforestIsomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SubgraphIsomorphismInstance) x with
  | some i => decide (WellFormed i ∧ SubgraphIsomorphism.SubgraphIsomorphismFeasible i)
  | none => false

/-- **SUBFOREST ISOMORPHISM is NP-complete.** Source: Garey and Johnson (1979), Theorem 4.6 and
[GT48], comment. -/
public theorem_wanted subforestIsomorphism_npComplete :
    subforestIsomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L subforestIsomorphismDec

end MetaMathlibExt.Complexity.NPComplete.SubforestIsomorphism
