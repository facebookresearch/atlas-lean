/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM AXIOM SET with all sentences true: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO17] MINIMUM AXIOM SET, comment on
p. 263 ("Remains NP-complete even if T = S");
P. Pudlák, "Polynomially complete problems in the logic of automated
discovery", Mathematical Foundations of Computer Science 1975, Lecture Notes in
Computer Science 32, Springer (1975), 358-361, doi:10.1007/3-540-07389-2_221.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumAxiomSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSetAllSentencesTrue

open MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSet
  (MinimumAxiomSetInstance MinimumAxiomSetFeasible)

/-- Well-formedness of an instance: a well-formed MINIMUM AXIOM SET instance in which every
sentence is true (`T = S`). -/
def WellFormed (i : MinimumAxiomSetInstance) : Prop :=
  MinimumAxiomSet.WellFormed i ∧ ∀ x < i.1, x ∈ i.2.1

open Classical in
/-- MINIMUM AXIOM SET with all sentences true as a decision problem over bitstrings. -/
noncomputable def minimumAxiomSetAllSentencesTrueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumAxiomSetInstance) x with
  | some i => decide (WellFormed i ∧ MinimumAxiomSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSetAllSentencesTrue
