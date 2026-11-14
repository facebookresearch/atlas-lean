/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT for K₃,₃-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, comment:
remains NP-complete if `G` is planar, cubic, 3-connected, and has no face with fewer than 5 edges;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "K3,3-free", column HAMILTONIAN CIRCUIT);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (row K3,3-FREE*, column HAM CIR: "N [GJ]").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted
public import WantedExt.Complexity.NPComplete.DominatingSetK33FreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitK33Free

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)
open MetaMathlibExt.Complexity.NPComplete.DominatingSetK33Free (HasK33Subdivision)

/-!
# HAMILTONIAN CIRCUIT for K₃,₃-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` with no subgraph homeomorphic to `K₃,₃`. QUESTION: does `G`
contain a Hamiltonian circuit?

This is the restriction of HAMILTONIAN CIRCUIT
(`WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted`, [GT37]) to the class that
Johnson's 1985 table calls "K3,3-free" and de Figueiredo et al. call K3,3-FREE*: "the class of
graphs that contain no subgraphs homeomorphic to K3,3; in other words, the class of graphs that do
not contain K3,3 as a topological minor". The predicate is `DominatingSetK33Free.HasK33Subdivision`
(a subgraph homeomorphic to `K₃,₃`, i.e. a subdivision of `K₃,₃`: six distinct branch vertices
joined by nine paths that meet only at common endpoints). The instance, the graph, the parent
well-formedness condition (`n > 0`, a simple edge list) and the question (`3 ≤ n` and Mathlib's
`SimpleGraph.IsHamiltonian`) are that module's; the restriction is added to `WellFormed`. Every
planar graph is K3,3-free (Kuratowski), so the class contains the planar cubic graphs on which
[GT37] records the problem NP-complete; de Figueiredo et al. derive the K3,3-free entries from the
planar ones in this way.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (`n > 0`, simple
edge list) whose graph has no subgraph homeomorphic to `K₃,₃`. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ ¬ HasK33Subdivision (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT for K₃,₃-free graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitK33FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT for K₃,₃-free graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT37], comment; Johnson (1985), Table 1; de Figueiredo, de Melo, Sasaki and Silva (2022), Table 1.
-/
public theorem_wanted hamiltonianCircuitK33Free_npComplete :
    hamiltonianCircuitK33FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitK33FreeDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitK33Free
