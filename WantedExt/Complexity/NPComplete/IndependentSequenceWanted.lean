/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SEQUENCE is NP-complete

Source:
M. M. Halldórsson, "Approximations of weighted independent set and hereditary subset
problems", Journal of Graph Algorithms and Applications 4(1) (2000), 1-16,
doi:10.7155/jgaa.00020, Section 2.1, problem Max Independent Sequence (introduced by Blundo)
and Proposition 2.3 (a size-preserving reduction from INDEPENDENT SET);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM INDEPENDENT SEQUENCE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IndependentSequenceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSequence

/-!
# INDEPENDENT SEQUENCE is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there an independent sequence for `G` of length at least `K`, i.e., a sequence
`v₁, …, v_m` of independent vertices of `G` with `m ≥ K` such that, for all `i < m`, a vertex
`v̄ᵢ ∈ V` exists which is adjacent to `v_{i+1}` but is not adjacent to any `v_j` for `j ≤ i`?

The sequence is a list `l` (0-indexed, so `v_{i+1}` is `l[i]` and `v₁, …, vᵢ` is `l.take i`)
whose entries form an independent set (Mathlib's `SimpleGraph.IsIndepSet`). The witness
condition forces the entries to be distinct: if `v_{i+1} = v_j` with `j ≤ i`, a vertex adjacent
to `v_{i+1}` is adjacent to `v_j`. The graph is given by a vertex count `n` (vertices `Fin n`)
and a simple edge list. The bound `K ≤ |V|` follows the convention of Garey and Johnson's
[GT20] INDEPENDENT SET.

Halldórsson shows that feasibility of a sequence is checked in polynomial time, so the problem
is in NP, and Proposition 2.3 maps a graph `G` on `v₁, …, vₙ` to the graph `H_G` that adds a
clique `w₁, …, wₙ` with `vᵢ wⱼ` an edge iff `i ≥ j`; `G` has an independent set of size `K`
iff `H_G` has an independent sequence of length `K`, which reduces INDEPENDENT SET to this
problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDEPENDENT SEQUENCE is NP-complete.** Source: Halldórsson (2000), Section 2.1 and
Proposition 2.3; Crescenzi and Kann, MAXIMUM INDEPENDENT SEQUENCE. -/
public theorem_wanted independentSequence_npComplete :
    independentSequenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSequenceDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSequence
