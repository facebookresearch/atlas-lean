/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO17] STRONG INEQUIVALENCE FOR
MONADIC RECURSION SCHEMES, p. 277 (reference [Constable, Hunt, and Sahni, 1974];
transformation from STRONG INEQUIVALENCE OF IANOV SCHEMES);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031
(journal version of the 1974 Cornell report GJ cites: strong equivalence of linear monadic
recursion schemes is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StrongInequivalenceForMonadicRecursionSchemesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceForMonadicRecursionSchemes

/-!
# STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES is NP-complete

INSTANCE: finite sets `F` and `P` of function and predicate symbols, a set `G` of "defined"
function symbols disjoint from `F`, a specified symbol `f₀ ∈ G`, and two linear monadic
recursion schemes `S₁` and `S₂`, each consisting of a defining statement for each `f ∈ G` of
the form `fx = if px then αx else βx`, where `p ∈ P`, `α, β ∈ (F ∪ G)*`, and `α` and `β` each
contain at most one occurrence of a symbol from `G`.
QUESTION: is there a domain set `D`, an interpretation of each `f ∈ F` as a function
`f : D → D`, an interpretation of each `p ∈ P` as a function `p : D → {T, F}`, and an initial
value `x₀ ∈ D` such that, as defined by the recursion schemes `S₁` and `S₂`, either the two
values for `f₀(x₀)` differ or one is defined and the other isn't?

The symbols are `a₀, …, a_{|F|-1}` of `F`, written `(false, k)`, `g₀, …, g_{|G|-1}` of `G`,
written `(true, k)` (so `F` and `G` are disjoint), and `p₀, …, p_{|P|-1}` of `P`; `f₀` is
`g_{k₀}` for a given index `k₀`. Interpretations are families indexed by `ℕ`, of which only
the indices below `|F|` and `|P|` occur. A scheme is the list of its defining statements, the
`k`-th being `(j, α, β)` for `gₖ x = if pⱼ x then α x else β x`. A word `s₁ s₂ ⋯ sᵣ` applied to
`x` is `s₁(s₂(⋯ sᵣ(x)))`. `Computes S w x y` is the least relation closed under these
equations (the least fixed point semantics of the scheme): `f₀(x₀)` is defined with value `v`
iff `Computes S [g_{k₀}] x₀ v`. All functions are unary and the interpretations are total, so
this agrees with every standard evaluation order.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES is NP-complete.** Source: Garey and
Johnson (1979), [PO17]; Constable, Hunt and Sahni (1980). -/
public theorem_wanted strongInequivalenceForMonadicRecursionSchemes_npComplete :
    strongInequivalenceForMonadicRecursionSchemesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strongInequivalenceForMonadicRecursionSchemesDec

end MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceForMonadicRecursionSchemes
