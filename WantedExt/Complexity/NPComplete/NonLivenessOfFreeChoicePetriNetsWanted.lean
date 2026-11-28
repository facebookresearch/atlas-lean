/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-LIVENESS OF FREE CHOICE PETRI NETS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS3] NON-LIVENESS OF FREE
CHOICE PETRI NETS;
N. D. Jones, L. H. Landweber, and Y. E. Lien, "Complexity of some problems in Petri
nets", Theoretical Computer Science 4 (1977), 277-299,
doi:10.1016/0304-3975(77)90014-7;
liveness as in T. Murata, "Petri nets: properties, analysis and applications",
Proceedings of the IEEE 77 (1989), 541-580, doi:10.1109/5.24143.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NonLivenessOfFreeChoicePetriNetsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonLivenessOfFreeChoicePetriNets

/-!
# NON-LIVENESS OF FREE CHOICE PETRI NETS is NP-complete

INSTANCE: a Petri net `P = (n, M₀, T)`, where `n ∈ ℤ⁺`, `M₀` is an `n`-tuple of non-negative
integers (the initial marking), and `T` is a set of transitions `⟨a, b⟩` in which `a` and `b`
are `n`-tuples of `0`'s and `1`'s; firing `⟨a, b⟩` at a marking `M` requires `M - a ≥ 0` and
gives `M - a + b`. `P` is free choice: for each `⟨a, b⟩ ∈ T`, either `a` contains exactly one
`1`, or every other `⟨c, d⟩ ∈ T` has `c` equal to `0` in every position where `a` has a `1`.
QUESTION: is `P` not live, that is, is there a transition `t ∈ T` and a firing sequence `σ`
such that, for every sequence `τ` of transitions, the sequence `σ τ t` is not firable at `M₀`?

`σ` is a firing sequence, so it is itself firable at `M₀`. This is the standard notion of
liveness (Murata 1989, Section IV): a net is live if, no matter what marking has been reached
from `M₀`, every transition can still be fired by some further firing sequence. So `P` is not
live exactly when some reachable marking (the one `σ` leads to) allows no continuation that
fires `t`. Without that condition any non-firable `σ` would make the answer yes. Places are
`0, ..., n - 1`; a marking is a function `ℕ → ℕ`, and only places below `n` are ever changed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NON-LIVENESS OF FREE CHOICE PETRI NETS is NP-complete.** Source: Garey and Johnson
(1979), [MS3]; Jones, Landweber, and Lien (1977). -/
public theorem_wanted nonLivenessOfFreeChoicePetriNets_npComplete :
    nonLivenessOfFreeChoicePetriNetsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonLivenessOfFreeChoicePetriNetsDec

end MetaMathlibExt.Complexity.NPComplete.NonLivenessOfFreeChoicePetriNets
