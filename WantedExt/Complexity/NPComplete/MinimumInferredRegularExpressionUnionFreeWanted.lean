/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM INFERRED UNION-FREE REGULAR EXPRESSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [AL10] MINIMUM INFERRED REGULAR EXPRESSION,
comment ("Remains NP-complete even if `E` is required to contain no "∪" operations or to be
"star-free" (contain no "*" operations) [Angluin, 1976]");
D. Angluin, "On the complexity of minimum inference of regular sets", Information and Control
39 (1978), 337-350, doi:10.1016/S0019-9958(78)90683-6, Corollary 3;
D. Angluin, *An Application of the Theory of Computational Complexity to the Study of Inductive
Inference*, Ph.D. thesis, University of California, Berkeley (1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumInferredRegularExpressionUnionFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpressionUnionFree

open MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpression
  (MinimumInferredRegularExpressionInstance symbolOccurrences)

/-!
# MINIMUM INFERRED UNION-FREE REGULAR EXPRESSION is NP-complete

MINIMUM INFERRED REGULAR EXPRESSION ([AL10], `MinimumInferredRegularExpressionWanted`) with the
expression `E` required to contain no `∪` operations. INSTANCE: a finite
alphabet `Σ`, two finite subsets `S, T ⊆ Σ*`, and a positive integer `K`. QUESTION: is there a
regular expression `E` over `Σ` containing no `∪` operation that has `K` or fewer occurrences
of symbols from `Σ` and such that, if `L ⊆ Σ*` is the language represented by `E`, then `S ⊆ L` and
`T ⊆ Σ* - L`?

The instance, its well-formedness, regular expressions (Mathlib's `RegularExpression`, with
language `RegularExpression.matches'`) and the size `symbolOccurrences E` are those of
`MinimumInferredRegularExpressionWanted`; the only change is the restriction on `E`,
`UnionFree E`: `E` has no `RegularExpression.plus` node (the atoms `0`, `1` and letters,
concatenation and Kleene star remain).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM INFERRED UNION-FREE REGULAR EXPRESSION is NP-complete.** Source: Garey and Johnson
(1979), [AL10]; Angluin (1978), Corollary 3. -/
public theorem_wanted minimumInferredRegularExpressionUnionFree_npComplete :
    minimumInferredRegularExpressionUnionFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumInferredRegularExpressionUnionFreeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpressionUnionFree
