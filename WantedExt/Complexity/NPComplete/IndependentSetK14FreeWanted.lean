/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on K_1,4-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 195, problem [GT20] INDEPENDENT SET,
comment: "Remains NP-complete for cubic planar graphs [Garey, Johnson, and Stockmeyer, 1976],
[Garey and Johnson, 1977a], [Maier and Storer, 1977]";
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_388` (K_1,4-free),
problem Independent set: NP-complete (with the subclasses "cubic ∩ hamiltonian ∩ planar" and
"2-connected ∩ cubic ∩ planar" also recorded as NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetK14Free

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-!
# INDEPENDENT SET on K_1,4-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` with no induced subgraph isomorphic to the star `K_1,4` (a
vertex with four pairwise non-adjacent neighbours), and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) on the ISGCI class `gc_388`. The instance type (vertex count
`n`, edge list, bound `K`), the graph (`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the
question (a `Finset` of at least `K` vertices whose coercion is Mathlib's
`SimpleGraph.IsIndepSet`) are those of the edge-list INDEPENDENT SET statement on `main`,
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`, whose triangle-free
restriction lives only in its `WellFormed`, which this module does not use. `WellFormed` here
asks for a simple edge list on `Fin n`, `0 < K ≤ |V|` ([GT20]'s instance class), and the class:
"`K_1,4`-free" means no induced subgraph isomorphic to `K_1,4`, Mathlib's
`SimpleGraph.IsIndContained` (an induced embedding) with the star
`completeBipartiteGraph (Fin 1) (Fin 4)`, as in `DominatingSetGirthNineHX85K14FreeWanted`.

Garey and Johnson record INDEPENDENT SET as NP-complete on cubic planar graphs, citing Garey,
Johnson and Stockmeyer (1976) among others. A cubic graph has no vertex with four neighbours,
so it is `K_1,4`-free, and those instances are instances of this problem with the same answer.
ISGCI records this class as NP-complete.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) with no induced
`K_1,4`, and `0 < K ≤ |V|`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    ¬ (completeBipartiteGraph (Fin 1) (Fin 4)).IsIndContained (Graph i) ∧
      0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on `K_1,4`-free graphs as a decision problem over bitstrings. -/
noncomputable def independentSetK14FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

/-- **INDEPENDENT SET on `K_1,4`-free graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT20], comment (cubic planar graphs); Garey, Johnson and Stockmeyer (1976); ISGCI (`gc_388`). -/
public theorem_wanted independentSetK14Free_npComplete :
    independentSetK14FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetK14FreeDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetK14Free
