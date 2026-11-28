/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGISTER SUFFICIENCY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO1] REGISTER SUFFICIENCY;
R. Sethi, "Complete register allocation problems", SIAM Journal on Computing 4 (1975),
226-248, doi:10.1137/0204020.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RegisterSufficiencyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegisterSufficiency

/-!
# REGISTER SUFFICIENCY is NP-complete

Given a directed acyclic graph `G = (V, A)` and a positive integer `K`, is there a computation
for `G` that uses `K` or fewer registers, i.e., an ordering `v₁, …, vₙ` of the vertices in `V`,
where `n = |V|`, and a sequence `S₀, …, Sₙ` of subsets of `V`, each satisfying `|Sᵢ| ≤ K`, such
that `S₀` is empty, `Sₙ` contains all vertices with in-degree `0` in `G`, and, for
`1 ≤ i ≤ n`, `vᵢ ∈ Sᵢ`, `Sᵢ - {vᵢ} ⊆ Sᵢ₋₁`, and `Sᵢ₋₁` contains all vertices `u` for which
`(vᵢ, u) ∈ A`?

An arc `(v, u)` says that `u` is an operand of `v`; `Sᵢ` is the set of values held in registers
after the `i`-th step, which computes `vᵢ`. Each vertex is computed exactly once.

The digraph has vertices `Fin n` and is given by its arc list, with no repeated arcs; it is
acyclic, and `K ≥ 1` (`WellFormed`). The ordering is a permutation `v` of `Fin n`, with
`v k` the vertex computed at step `k + 1`; `S k` is `Sₖ` for `k : Fin (n + 1)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **REGISTER SUFFICIENCY is NP-complete.** Source: Garey and Johnson (1979), [PO1];
Sethi (1975). -/
public theorem_wanted registerSufficiency_npComplete :
    registerSufficiencyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L registerSufficiencyDec

end MetaMathlibExt.Complexity.NPComplete.RegisterSufficiency
