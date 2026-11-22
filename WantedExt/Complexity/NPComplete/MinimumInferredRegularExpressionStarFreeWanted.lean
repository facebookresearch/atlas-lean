/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM INFERRED STAR-FREE REGULAR EXPRESSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [AL10] MINIMUM INFERRED REGULAR EXPRESSION,
comment ("Remains NP-complete even if `E` is required to contain no "∪" operations or to be
"star-free" (contain no "*" operations) [Angluin, 1976]");
D. Angluin, *An Application of the Theory of Computational Complexity to the Study of Inductive
Inference*, Ph.D. thesis, University of California, Berkeley (1976);
D. Angluin, "On the complexity of minimum inference of regular sets", Information and Control
39 (1978), 337-350, doi:10.1016/S0019-9958(78)90683-6, Section 4 (records the star-free case).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Languages.GeneralizedRegularExpression
public import CSLibExt.Computability.Languages.KleeneConverse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumInferredRegularExpressionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpressionStarFree

open MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpression
  (MinimumInferredRegularExpressionInstance symbolOccurrences)

/-!
# MINIMUM INFERRED STAR-FREE REGULAR EXPRESSION is NP-complete

MINIMUM INFERRED REGULAR EXPRESSION ([AL10], `MinimumInferredRegularExpressionWanted`) with the
expression `E` required to be "star-free" (to contain no `*` operations). INSTANCE: a finite
alphabet `Σ`, two finite subsets `S, T ⊆ Σ*`, and a positive integer `K`. QUESTION: is there a
star-free regular expression `E` over `Σ` that has `K` or fewer occurrences of symbols from
`Σ` and such that, if `L ⊆ Σ*` is the language represented by `E`, then `S ⊆ L` and
`T ⊆ Σ* - L`?

The instance, its well-formedness, regular expressions (Mathlib's `RegularExpression`, with
language `RegularExpression.matches'`) and the size `symbolOccurrences E` are those of
`MinimumInferredRegularExpressionWanted`; the only change is the restriction on `E`,
that `E` has star height `0` (`Cslib.Language.regularStarHeight E = 0`, the nesting depth of
`*` being zero), i.e. no `RegularExpression.star` node occurs (the atoms `0`, `1` and letters,
union and concatenation remain), as in `StarFreeRegularExpressionInequivalenceWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some star-free regular expression over the alphabet `{0, ..., k - 1}` with at most `K`
symbol occurrences matches every word of `S` and no word of `T`. -/
def MinimumInferredRegularExpressionStarFreeFeasible
    (i : MinimumInferredRegularExpressionInstance) : Prop :=
  ∃ E : RegularExpression ℕ, Cslib.Language.regularStarHeight E = 0 ∧
    (∀ a ∈ Cslib.Language.KleeneConverse.regexLetters E, a < i.1) ∧
      symbolOccurrences E ≤ i.2.2.2 ∧
      (∀ s ∈ i.2.1, s ∈ E.matches') ∧
      ∀ t ∈ i.2.2.1, t ∉ E.matches'

open Classical in
/-- MINIMUM INFERRED STAR-FREE REGULAR EXPRESSION as a decision problem over bitstrings. -/
noncomputable def minimumInferredRegularExpressionStarFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumInferredRegularExpressionInstance) x with
  | some i => decide (MinimumInferredRegularExpression.WellFormed i ∧
      MinimumInferredRegularExpressionStarFreeFeasible i)
  | none => false

/-- **MINIMUM INFERRED STAR-FREE REGULAR EXPRESSION is NP-complete.** Source: Garey and Johnson
(1979), [AL10]; Angluin (1976). -/
public theorem_wanted minimumInferredRegularExpressionStarFree_npComplete :
    minimumInferredRegularExpressionStarFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumInferredRegularExpressionStarFreeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpressionStarFree
