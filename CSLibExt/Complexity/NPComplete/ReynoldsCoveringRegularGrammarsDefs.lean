/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REYNOLDS COVERING FOR REGULAR GRAMMARS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL11] REYNOLDS COVERING FOR
CONTEXT-FREE GRAMMARS, p. 268, comment: "Remains NP-complete even if G₁ and G₂ are
restricted to "regular" grammars", attributed to
H. B. Hunt III and D. J. Rosenkrantz, "Complexity of grammatical similarity relations:
preliminary report", Proc. Conference on Theoretical Computer Science, University of
Waterloo (1977), 139-148 (original not available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ReynoldsCoveringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReynoldsCoveringRegularGrammars

/-- A production `(A, w)` is right-linear when every symbol of `w` except possibly the last is
a terminal: it has the form `A → x₁ ⋯ xⱼ` or `A → x₁ ⋯ xⱼ B` with terminals `xᵢ`. -/
def IsRightLinearProduction (p : ℕ × List (Bool × ℕ)) : Prop :=
  ∀ x ∈ p.2.dropLast, x.1 = true

/-- A grammar is regular (right-linear) when every production is right-linear. -/
def IsRegularGrammar (g : ReynoldsCovering.GrammarData) : Prop :=
  ∀ p ∈ g.2.2, IsRightLinearProduction p

/-- Well-formedness of an instance: the instance is well-formed for REYNOLDS COVERING FOR
CONTEXT-FREE GRAMMARS, and both grammars are regular. -/
def WellFormed (i : ReynoldsCovering.ReynoldsCoveringInstance) : Prop :=
  ReynoldsCovering.WellFormed i ∧ IsRegularGrammar i.2.1 ∧ IsRegularGrammar i.2.2

open Classical in
/-- REYNOLDS COVERING FOR REGULAR GRAMMARS as a decision problem over bitstrings. -/
noncomputable def reynoldsCoveringRegularGrammarsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ReynoldsCovering.ReynoldsCoveringInstance) x with
  | some i => decide (WellFormed i ∧ ReynoldsCovering.ReynoldsCoveringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ReynoldsCoveringRegularGrammars
