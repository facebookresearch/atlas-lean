/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN COMPLETION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT34] HAMILTONIAN COMPLETION;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT);
D. Gamarnik and M. Sviridenko, "Hamiltonian completions of sparse random graphs", Discrete
Applied Mathematics 152 (2005), 139-158, doi:10.1016/j.dam.2005.05.001.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCompletion

/-!
# HAMILTONIAN COMPLETION is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is there a superset
`E'` containing `E` such that `|E' - E| ≤ K` and the graph `G' = (V, E')` has a Hamiltonian
circuit?

The superset `E'` is a simple graph `H ≥ G` on the same vertices, `|E' - E|` is
`(H.edgeSet \ G.edgeSet).ncard`, and a Hamiltonian circuit is a closed walk `p` with
`p.IsHamiltonianCycle` (a cycle through every vertex exactly once). Mathlib's
`SimpleGraph.IsHamiltonian` holds vacuously on one vertex, so the existence of a Hamiltonian
cycle is stated directly; it fails on fewer than three vertices.

The vertex set is given explicitly as the list `[0, 1, ..., n - 1]`, as in Garey and Johnson's
standard graph encoding (a vertex list and an edge list), so an instance's encoding has length at
least `|V|`. With `n` given only in binary, an edgeless graph with `K = |V|` would be a
yes-instance of `O(log |V|)` bits whose natural certificate (the added edges) is exponentially
longer, a succinct variant that the cited results do not cover.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN COMPLETION is NP-complete.** Source: Garey and Johnson (1979), [GT34];
Karp (1972); Gamarnik and Sviridenko (2005). -/
public theorem_wanted hamiltonianCompletion_npComplete :
    hamiltonianCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCompletionDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCompletion
