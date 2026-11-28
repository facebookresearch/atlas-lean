/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM INFERRED STAR-FREE REGULAR EXPRESSION: definitions

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

public import CSLibExt.Computability.Languages.GeneralizedRegularExpression
public import CSLibExt.Computability.Languages.KleeneConverse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumInferredRegularExpressionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpressionStarFree

open MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpression
  (MinimumInferredRegularExpressionInstance symbolOccurrences)

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

end MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpressionStarFree
