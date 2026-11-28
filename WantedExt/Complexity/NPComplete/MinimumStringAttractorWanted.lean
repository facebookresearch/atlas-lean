/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM STRING ATTRACTOR is NP-complete

Source:
D. Kempa and N. Prezza, "At the roots of dictionary compression: string attractors",
Proceedings of the 50th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2018), 827-840,
doi:10.1145/3188745.3188814; full version arXiv:1710.10964, Definition 3.1 (string attractor),
Section 4 (the language `ATTRACTOR`) and Theorem 4.2 (with `k = n`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumStringAttractorDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumStringAttractor

/-!
# MINIMUM STRING ATTRACTOR is NP-complete

INSTANCE: a string `T ∈ Σⁿ` over an unbounded alphabet and a natural number `p`.
QUESTION: does `T` have a string attractor of size at most `p`, i.e., a set `Γ` of positions of
`T` such that every substring `T[i..j]` (`i ≤ j < |T|`) has an occurrence
`T[i'..j'] = T[i..j]` with `j'' ∈ [i', j']` for some `j'' ∈ Γ` (Kempa and Prezza,
Definition 3.1), and `|Γ| ≤ p`?
This is the language `ATTRACTOR = {⟨T, p⟩ : T has an attractor of size ≤ p}` of Kempa and
Prezza, Section 4; it is `k-ATTRACTOR` with `k = n`, NP-complete by their Theorem 4.2.

Letters are natural numbers and positions are 0-based: the source's position `i ∈ [1..n]` is
`i - 1` here. Every instance is well formed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM STRING ATTRACTOR is NP-complete.** Source: Kempa and Prezza (2018), Theorem 4.2
with `k = n`. -/
public theorem_wanted minimumStringAttractor_npComplete :
    minimumStringAttractorDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumStringAttractorDec

end MetaMathlibExt.Complexity.NPComplete.MinimumStringAttractor
