/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REYNOLDS COVERING FOR CONTEXT-FREE GRAMMARS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL11] REYNOLDS COVERING FOR
CONTEXT-FREE GRAMMARS;
H. B. Hunt III and D. J. Rosenkrantz, "Complexity of grammatical similarity relations:
preliminary report", Proc. Conference on Theoretical Computer Science, University of
Waterloo (1977), 139-148.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ReynoldsCoveringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering

/-!
# REYNOLDS COVERING FOR CONTEXT-FREE GRAMMARS is NP-complete

Given context-free grammars `G₁ = (N₁, Σ, Π₁, S₁)` and `G₂ = (N₂, Σ, Π₂, S₂)` over the same
terminal alphabet, does `G₂` Reynolds cover `G₁`: is there a function `f` from `N₁ ∪ Σ` to
`N₂ ∪ Σ` with `f x = x` for every terminal `x`, `f A ∈ N₂` for every `A ∈ N₁`,
`f S₁ = S₂`, and such that for every production `A → x₁ ⋯ xᵣ` of `Π₁` the image
`f A → f x₁ ⋯ f xᵣ` is a production of `Π₂`?

The terminal alphabet is `Σ = {0, ..., k - 1}` and the nonterminals of a grammar with `n`
nonterminals are `0, ..., n - 1`. A production is a pair of a left-hand side and a list of
right-hand side symbols, in which `(false, B)` is nonterminal `B` and `(true, a)` is terminal
`a`; the set of productions is a list (a repeated production does not change the grammar).
Each grammar is read as a `Cslib.Language.EncodedCFG`, whose `toCFG` is a Mathlib
`ContextFreeGrammar` with nonterminals `ℕ`. Since `f` is the identity on terminals, it is
determined by its values on nonterminals, a map `f : ℕ → ℕ`, and the image of a production
is `Cslib.Language.mapRule f`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **REYNOLDS COVERING FOR CONTEXT-FREE GRAMMARS is NP-complete.** Source: Garey and
Johnson (1979), [AL11]; Hunt and Rosenkrantz (1977). -/
public theorem_wanted reynoldsCovering_npComplete :
    reynoldsCoveringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L reynoldsCoveringDec

end MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering
