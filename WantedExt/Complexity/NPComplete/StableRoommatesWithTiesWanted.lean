/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STABLE ROOMMATES WITH TIES (weak stability, complete lists) is NP-complete

Source:
E. Ronn, "NP-complete stable matching problems", Journal of Algorithms 11 (1990), 285-304,
doi:10.1016/0196-6774(90)90007-2;
problem definitions as in Á. Cseh, R. W. Irving and D. F. Manlove, "The stable roommates
problem with short lists", Theory of Computing Systems 63 (2019), 128-149,
doi:10.1007/s00224-017-9810-9, Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StableRoommatesWithTiesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StableRoommatesWithTies

/-!
# STABLE ROOMMATES WITH TIES (weak stability, complete lists) is NP-complete

Cseh, Irving and Manlove (2019), Section 1: in the Stable Roommates problem with Incomplete
lists (SRI) a graph `G = (A, E)` and preference lists are given; agent `aᵢ`'s list `≺ᵢ` is a
linear order on the agents adjacent to `aᵢ`. For a matching `M` of `G`, `M(aᵢ)` is the partner
of `aᵢ`. An edge `aᵢaⱼ ∉ M` blocks `M` if `aᵢ` is unmatched or prefers `aⱼ` to `M(aᵢ)`, and
similarly `aⱼ` is unmatched or prefers `aᵢ` to `M(aⱼ)`; `M` is stable if no edge blocks it,
and an instance is solvable if it admits a stable matching. In SRTI each `≺ᵢ` is a strict weak
ordering (ties allowed), preference meaning strict preference; SRT is the special case
`G = Kₙ` (every agent ranks all others). Ronn (1990) proved that deciding whether a given SRT
instance is solvable is NP-complete.

Agents are `0, …, n - 1`. Agent `v`'s strict weak ordering is given by ranks: `v` prefers `w`
to `w'` iff `rank v w < rank v w'`, and equal ranks are ties (every strict weak ordering of a
finite set arises this way; the rank of `v` itself is ignored). A matching of `Kₙ` is given by
its partner function `μ`, an involution: `μ v = w ≠ v` means `v` and `w` are matched, and
`μ v = v` means `v` is unmatched.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STABLE ROOMMATES WITH TIES (weak stability, complete lists) is NP-complete.** Source:
Ronn (1990); Cseh, Irving and Manlove (2019), Section 1. -/
public theorem_wanted stableRoommatesWithTies_npComplete :
    stableRoommatesWithTiesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stableRoommatesWithTiesDec

end MetaMathlibExt.Complexity.NPComplete.StableRoommatesWithTies
