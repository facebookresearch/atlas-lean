/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HOMOMORPHIC IMAGE FOR CONTEXT-FREE GRAMMARS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [AL11] REYNOLDS COVERING FOR CONTEXT-FREE
GRAMMARS, comment ("The same results hold for the related questions of whether ... `G₂` is a
"homomorphic image" of `G₁`"; reference: [Hunt and Rosenkrantz, 1977]);
D. J. Rosenkrantz and H. B. Hunt III, "Testing for grammatical coverings", Theoretical Computer
Science 38 (1985), 323-341, doi:10.1016/0304-3975(85)90226-9, Definition 2.7(1) and
Theorem 3.2(1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HomomorphicImageContextFreeGrammarsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HomomorphicImageContextFreeGrammars

open MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering
  (ReynoldsCoveringInstance toEncodedCFG)

/-!
# HOMOMORPHIC IMAGE FOR CONTEXT-FREE GRAMMARS is NP-complete

INSTANCE: context-free grammars `G₁ = (N₁, Σ, Π₁, S₁)` and `G₂ = (N₂, Σ, Π₂, S₂)` over the same
terminal alphabet `Σ`.
QUESTION: is `G₂` a "homomorphic image" of `G₁`, i.e., is there a function `f` mapping
`N₁ ∪ Σ` into `N₂ ∪ Σ` such that `f(x) = x` for all `x ∈ Σ`, `f(A) ∈ N₂` for all `A ∈ N₁`,
`f(S₁) = S₂`, and `f(Π₁) = Π₂`, where `f(Π₁)` is the set of images `f(A) → f(x₁) ⋯ f(xᵣ)` of the
productions `A → x₁ ⋯ xᵣ` of `Π₁`?

Garey and Johnson list this question in the comment to REYNOLDS COVERING FOR CONTEXT-FREE
GRAMMARS and refer to Hunt and Rosenkrantz for the definition. Rosenkrantz and Hunt
(Definition 2.7(1)) call such an `f` a grammar homomorphism from `G₁` onto `G₂`; a Reynolds
cover (`ReynoldsCoveringWanted`) asks only `f(Π₁) ⊆ Π₂`. Their Theorem 3.2(1) proves the
question NP-complete, also for regular grammars.

The instance format, the grammars (`Cslib.Language.EncodedCFG`, read as Mathlib
`ContextFreeGrammar`s with nonterminals `ℕ`), their well-formedness and the image of a
production (`Cslib.Language.mapRule f` for a map `f : ℕ → ℕ` on nonterminals, extended by the
identity on terminals) are those of `ReynoldsCoveringWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HOMOMORPHIC IMAGE FOR CONTEXT-FREE GRAMMARS is NP-complete.** Source: Garey and Johnson
(1979), [AL11]; Rosenkrantz and Hunt (1985), Theorem 3.2(1). -/
public theorem_wanted homomorphicImage_npComplete :
    homomorphicImageDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L homomorphicImageDec

end MetaMathlibExt.Complexity.NPComplete.HomomorphicImageContextFreeGrammars
