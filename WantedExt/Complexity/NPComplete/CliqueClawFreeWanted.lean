/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE for claw-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE;
S. Poljak, "A note on stable sets and colorings of graphs", Commentationes
Mathematicae Universitatis Carolinae 15 (1974), 307-309;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueClawFree

/-!
# CLIQUE for claw-free graphs is NP-complete

INSTANCE: a claw-free graph `G = (V, E)` (no induced `K₁,₃`) and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain a clique of size `K` or more, i.e. a subset `V' ⊆ V` with
`|V'| ≥ K` such that every two vertices of `V'` are joined by an edge of `E`?

This is CLIQUE ([GT19]) restricted to claw-free graphs. Johnson's 1985 table lists this entry as
apparently open; the 2022 revision of the table by de Figueiredo, de Melo, Sasaki and Silva lists
it as NP-complete, citing Poljak. Poljak's construction proves INDEPENDENT SET NP-complete on
triangle-free graphs (`TriangleFreeIndependentSetWanted`): replacing every edge of a graph with
`m` edges by a path of three edges yields a triangle-free graph whose independence number is
larger by exactly `m`. The complement of a triangle-free graph has no independent set of more
than 2 vertices, so it is claw-free (a claw has 3 pairwise non-adjacent vertices), and its
cliques are the independent sets of the triangle-free graph. Complementing Poljak's graphs
(whose vertex count is polynomial in the input) therefore reduces INDEPENDENT SET to this
problem. Membership in NP: for `K ≥ 2` a clique of size `K` lies among the non-isolated vertices
(at most two per edge), and for `K = 1` the answer is yes because `1 ≤ |V|`; so the binary vertex
count does not make the problem succinct, and claw-freeness is checked in polynomial time.

The graph is given by its vertex count and edge list (`Cslib.Complexity.Karp.edgeGraph`), as in
`CliqueBOneVPGWanted`; the clique is a `Finset` whose coercion is `SimpleGraph.IsClique`.
Claw-freeness is MathlibExt's `SimpleGraph.IsClawFree` (from
`MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly`, as in `PolarityClawFreeWanted`): no
vertex `c` with three distinct, pairwise non-adjacent neighbours `l₁, l₂, l₃`, equivalently
(`SimpleGraph.isClawFree_iff_not_isIndContained`) no induced `K₁,₃`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex count `n` (vertices `0, ..., n - 1`), the edge list, and the bound
`K`. -/
abbrev CliqueClawFreeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueClawFreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is
claw-free, and `0 < K ≤ n`. -/
def WellFormed (i : CliqueClawFreeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsClawFree ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- The graph has a clique of size `K` or more. -/
def CliqueClawFreeFeasible (i : CliqueClawFreeInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1))

open Classical in
/-- CLIQUE for claw-free graphs as a decision problem over bitstrings. -/
noncomputable def cliqueClawFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueClawFreeInstance) x with
  | some i => decide (WellFormed i ∧ CliqueClawFreeFeasible i)
  | none => false

/-- **CLIQUE for claw-free graphs is NP-complete.** Source: Garey and Johnson (1979), [GT19];
Poljak (1974); de Figueiredo, de Melo, Sasaki and Silva (2022), Table 1. -/
public theorem_wanted cliqueClawFree_npComplete :
    cliqueClawFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueClawFreeDec

end MetaMathlibExt.Complexity.NPComplete.CliqueClawFree
