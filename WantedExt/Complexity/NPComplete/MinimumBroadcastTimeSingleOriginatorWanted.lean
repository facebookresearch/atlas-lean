/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BROADCAST TIME with a single originator is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND49] MINIMUM BROADCAST TIME,
p. 219 (comment: "The special case where `|V₀| = 1` remains NP-complete");
P. J. Slater, E. J. Cockayne and S. T. Hedetniemi, "Information dissemination in trees", SIAM
Journal on Computing 10 (1981), 692-701, doi:10.1137/0210052.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumBroadcastTimeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTimeSingleOriginator

open MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTime (MinimumBroadcastTimeInstance)

/-!
# MINIMUM BROADCAST TIME with a single originator is NP-complete

INSTANCE: a graph `G = (V, E)`, a subset `V₀ ⊆ V` with `|V₀| = 1`, and a positive integer `K`.
QUESTION: can a message be "broadcast" from the base set `V₀` to all other vertices in time `K`,
that is, is there a sequence `V₀, E₁, V₁, E₂, …, E_K, V_K` such that each `Vᵢ ⊆ V`, each
`Eᵢ ⊆ E`, `V_K = V`, and, for `1 ≤ i ≤ K`, (1) each edge in `Eᵢ` has exactly one endpoint in
`Vᵢ₋₁`, (2) no two edges in `Eᵢ` share a common endpoint, and (3)
`Vᵢ = Vᵢ₋₁ ∪ {v : {u, v} ∈ Eᵢ}`?

This is the special case `|V₀| = 1` of MINIMUM BROADCAST TIME ([ND49],
`MinimumBroadcastTimeWanted`): broadcasting from one originator `v₀`. Slater, Cockayne and
Hedetniemi show that determining the minimum time to broadcast from an arbitrary vertex of an
arbitrary graph is NP-complete. The instance type, `MinimumBroadcastTime.WellFormed` (simple
edge list, `V₀` a list of distinct vertices, `0 < K`) and
`MinimumBroadcastTime.MinimumBroadcastTimeFeasible` are the parent's, unchanged; `WellFormed`
adds that the list `V₀` has exactly one entry (its entries are distinct, so `|V₀| = 1`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MINIMUM BROADCAST TIME instance whose base set
`V₀` is a single vertex. -/
def WellFormed (i : MinimumBroadcastTimeInstance) : Prop :=
  MinimumBroadcastTime.WellFormed i ∧ i.2.2.1.length = 1

open Classical in
/-- MINIMUM BROADCAST TIME with a single originator as a decision problem over bitstrings. -/
noncomputable def minimumBroadcastTimeSingleOriginatorDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MinimumBroadcastTimeInstance) x with
  | some i => decide (WellFormed i ∧ MinimumBroadcastTime.MinimumBroadcastTimeFeasible i)
  | none => false

/-- **MINIMUM BROADCAST TIME is NP-complete with a single originator.** Source: Garey and
Johnson (1979), [ND49], comment; Slater, Cockayne and Hedetniemi (1981). -/
public theorem_wanted minimumBroadcastTimeSingleOriginator_npComplete :
    minimumBroadcastTimeSingleOriginatorDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumBroadcastTimeSingleOriginatorDec

end MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTimeSingleOriginator
