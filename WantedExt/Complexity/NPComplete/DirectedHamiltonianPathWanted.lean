/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED HAMILTONIAN PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH, comment
("Corresponding DIRECTED HAMILTONIAN PATH problem is also NP-complete"), and Section 3.1.4,
p. 60 (undirected Hamiltonian problems transformed to their directed counterparts);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.HamPath
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianCycleDirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedHamiltonianPath

open HamiltonianCycleDirected (HamiltonianCycleDirectedInstance WellFormed)

/-!
# DIRECTED HAMILTONIAN PATH is NP-complete

INSTANCE: a directed graph `G = (V, A)`.
QUESTION: does `G` contain a directed Hamiltonian path, i.e., an ordering `v₁, ..., vₙ` of `V`
(`n = |V|`) with `(vᵢ, vᵢ₊₁) ∈ A` for `1 ≤ i < n`?

Garey and Johnson record in the comment to [GT39] that the "corresponding DIRECTED HAMILTONIAN
PATH problem is also NP-complete". In Section 3.1.4 (p. 60) they define a Hamiltonian path in a
directed graph as above and observe that each undirected Hamiltonian problem transforms to its
directed counterpart by replacing every edge `{u, v}` with the two arcs `(u, v)` and `(v, u)`;
HAMILTONIAN PATH is NP-complete there, and Karp's 1972 paper proves the directed and undirected
Hamiltonian circuit problems NP-complete. Neither endpoint is specified: the variant with both
endpoints given is the proved HAMPATH of `CSLibExt.Computability.Complexity.Karp.HamPath`.

The instance and its well-formedness are those of DIRECTED HAMILTONIAN CIRCUIT ([GT38],
`HamiltonianCycleDirectedWanted`), reused unchanged: a vertex count `n` with an arc list on the
vertices `0, ..., n - 1` (`HamiltonianCycleDirected.WellFormed`: `0 < n`, no duplicate arcs, no
loops, endpoints in range). The question reuses the Hamiltonian path predicate of the proved
HAMPATH, `Cslib.Complexity.Karp.IsHamPath n A s t p` (the list `p` contains each vertex below
`n` exactly once, starts at `s`, ends at `t`, and consecutive entries are joined by arcs of
`A`), with both endpoints existentially quantified.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some list of the vertices is a directed Hamiltonian path of the digraph, between some start
vertex `s` and some end vertex `t` (`Cslib.Complexity.Karp.IsHamPath`). -/
def DirectedHamiltonianPathFeasible (i : HamiltonianCycleDirectedInstance) : Prop :=
  ∃ s t : ℕ, ∃ p : List ℕ, Cslib.Complexity.Karp.IsHamPath i.1 i.2 s t p

open Classical in
/-- DIRECTED HAMILTONIAN PATH as a decision problem over bitstrings. -/
noncomputable def directedHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleDirectedInstance) x with
  | some i => decide (WellFormed i ∧ DirectedHamiltonianPathFeasible i)
  | none => false

/-- **DIRECTED HAMILTONIAN PATH is NP-complete.** Source: Garey and Johnson (1979), [GT39] and
Section 3.1.4; Karp (1972). -/
public theorem_wanted directedHamiltonianPath_npComplete :
    directedHamiltonianPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedHamiltonianPathDec

end MetaMathlibExt.Complexity.NPComplete.DirectedHamiltonianPath
