/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HOMOMORPHIC IMAGE FOR CONTEXT-FREE GRAMMARS: definitions

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

public import CSLibExt.Computability.Languages.ContextFree.Encoded
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ReynoldsCoveringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HomomorphicImageContextFreeGrammars

open MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering
  (ReynoldsCoveringInstance toEncodedCFG)

/-- `G₂` is a homomorphic image of `G₁`: some map `f` on nonterminals (extended by the identity
on terminals) sends every nonterminal of `G₁` to a nonterminal of `G₂` and the initial symbol of
`G₁` to that of `G₂`, every production of `G₁` to a production of `G₂`, and every production of
`G₂` is the image of a production of `G₁`. -/
def HomomorphicImageFeasible : ReynoldsCoveringInstance → Prop
  | (_, g₁, g₂) =>
    ∃ f : ℕ → ℕ, (∀ A < g₁.1, f A < g₂.1) ∧
      f (toEncodedCFG g₁).toCFG.initial = (toEncodedCFG g₂).toCFG.initial ∧
      (∀ r ∈ (toEncodedCFG g₁).toCFG.rules,
        Cslib.Language.mapRule f r ∈ (toEncodedCFG g₂).toCFG.rules) ∧
      ∀ q ∈ (toEncodedCFG g₂).toCFG.rules,
        ∃ r ∈ (toEncodedCFG g₁).toCFG.rules, Cslib.Language.mapRule f r = q

open Classical in
/-- HOMOMORPHIC IMAGE FOR CONTEXT-FREE GRAMMARS as a decision problem over bitstrings. -/
noncomputable def homomorphicImageDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ReynoldsCoveringInstance) x with
  | some i => decide (ReynoldsCovering.WellFormed i ∧ HomomorphicImageFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HomomorphicImageContextFreeGrammars
