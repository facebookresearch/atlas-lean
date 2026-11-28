/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STORAGE-TIME SEQUENCING is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry MINIMUM
STORAGE-TIME SEQUENCING (the instance, schedule and storage-time measure);
S. Rao and A. W. Richa, "New approximation techniques for some linear ordering problems", SIAM
Journal on Computing 34(2) (2005), 388-404, doi:10.1137/S0097539702413197 (records minimum
storage-time product as NP-hard);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT43] DIRECTED OPTIMAL LINEAR ARRANGEMENT
(the special case of unit lengths and weights, up to the additive constant `|E|`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StorageTimeSequencingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StorageTimeSequencing

/-!
# STORAGE-TIME SEQUENCING is NP-complete

INSTANCE: a set `T` of tasks, a directed acyclic graph `G = (T, E)` of precedence constraints,
for each task a length `l(t) ∈ Z⁺`, for each edge `⟨t₁, t₂⟩` a weight `w(t₁, t₂)` (the storage
needed to save the intermediate results of `t₁` until `t₂` consumes them), and a positive integer
`K`. QUESTION: is there a one-processor schedule obeying the precedence constraints, i.e. a
permutation `π` of `[1..|T|]` with `π⁻¹(i) < π⁻¹(j)` for every edge `⟨tᵢ, tⱼ⟩ ∈ E`, whose total
storage-time product
`∑_{⟨t_{π(i)}, t_{π(j)}⟩ ∈ E} w(t_{π(i)}, t_{π(j)}) · ∑_{k = min(i,j)}^{max(i,j)} l(t_{π(k)})`
is at most `K`?

The tasks are `0, …, n - 1`, where `n` is the length of the list of task lengths. An edge is a
triple `(t₁, t₂, w)`: the arc `⟨t₁, t₂⟩` with weight `w ∈ ℕ` (the compendium gives no range for
the weights). As in `WantedExt.Complexity.NPComplete.DirectedOptimalLinearArrangementWanted`, a
schedule is a permutation `perm` of `List.range n` listing the tasks in processing order:
position `k` holds task `perm[k]` (the compendium's `π(k + 1)`, positions counted from `0`), and
the position of task `t` is `perm.idxOf t`. The storage of edge `⟨t₁, t₂⟩` is weighted by the
total length of the tasks in positions `min(p₁, p₂), …, max(p₁, p₂)`, where `pᵢ` is the position
of `tᵢ`. Each edge carries one weight, so the edge list has no repeated arc; the digraph is
acyclic.

With unit lengths and unit weights the storage-time product of a schedule is
`∑_{⟨t₁, t₂⟩ ∈ E} (p₂ - p₁ + 1)`, the DIRECTED OPTIMAL LINEAR ARRANGEMENT cost ([GT43]) plus
`|E|`. Membership in NP: the schedule is a certificate, and its storage-time product is computed
in polynomial time. Numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STORAGE-TIME SEQUENCING is NP-complete.** Source: Crescenzi and Kann, MINIMUM
STORAGE-TIME SEQUENCING; Rao and Richa (2005); Garey and Johnson (1979), [GT43] (special case). -/
public theorem_wanted storageTimeSequencing_npComplete :
    storageTimeSequencingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L storageTimeSequencingDec

end MetaMathlibExt.Complexity.NPComplete.StorageTimeSequencing
