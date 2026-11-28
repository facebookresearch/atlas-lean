/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM INFERRED UNION-FREE REGULAR EXPRESSION: definitions

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

public import CSLibExt.Computability.Languages.KleeneConverse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumInferredRegularExpressionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpressionUnionFree

open MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpression
  (MinimumInferredRegularExpressionInstance symbolOccurrences)

/-- `E` contains no `∪` (`RegularExpression.plus`) operation. -/
def UnionFree {α : Type*} : RegularExpression α → Prop
  | .zero => True
  | .epsilon => True
  | .char _ => True
  | .plus _ _ => False
  | .comp P Q => UnionFree P ∧ UnionFree Q
  | .star P => UnionFree P

/-- Some union-free regular expression over the alphabet `{0, ..., k - 1}` with at most `K`
symbol occurrences matches every word of `S` and no word of `T`. -/
def MinimumInferredRegularExpressionUnionFreeFeasible
    (i : MinimumInferredRegularExpressionInstance) : Prop :=
  ∃ E : RegularExpression ℕ, UnionFree E ∧
    (∀ a ∈ Cslib.Language.KleeneConverse.regexLetters E, a < i.1) ∧
      symbolOccurrences E ≤ i.2.2.2 ∧
      (∀ s ∈ i.2.1, s ∈ E.matches') ∧
      ∀ t ∈ i.2.2.1, t ∉ E.matches'

open Classical in
/-- MINIMUM INFERRED UNION-FREE REGULAR EXPRESSION as a decision problem over bitstrings. -/
noncomputable def minimumInferredRegularExpressionUnionFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumInferredRegularExpressionInstance) x with
  | some i => decide (MinimumInferredRegularExpression.WellFormed i ∧
      MinimumInferredRegularExpressionUnionFreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpressionUnionFree
