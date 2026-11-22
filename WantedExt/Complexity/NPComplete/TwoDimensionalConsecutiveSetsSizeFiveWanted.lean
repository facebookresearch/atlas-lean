/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-DIMENSIONAL CONSECUTIVE SETS with sets of size at most 5 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR19] 2-DIMENSIONAL CONSECUTIVE
SETS, p. 230, comment: "Remains NP-complete if all `Σⱼ ∈ C` have `|Σⱼ| ≤ 5`, but is solvable in
polynomial time if all `Σⱼ ∈ C` have `|Σⱼ| ≤ 2`" (the entry's reference is [Lipsky, 1977b]);
W. Lipski, Jr., "One more polynomial complete consecutive retrieval problem", Information
Processing Letters 6 (1977), 91-93, doi:10.1016/0020-0190(77)90034-5 (Garey and Johnson's
reference for [SR19]; its text was not available to check the bound `5`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsSizeFive

/-!
# 2-DIMENSIONAL CONSECUTIVE SETS with sets of size at most 5 is NP-complete

INSTANCE: a finite alphabet `Σ` and a collection `C = {Σ₁, Σ₂, ..., Σₙ}` of subsets of `Σ` with
`|Σⱼ| ≤ 5` for every `Σⱼ ∈ C`.
QUESTION: is there a partition of `Σ` into disjoint sets `X₁, X₂, ..., X_k` such that each `Xᵢ`
has at most one element in common with each `Σⱼ` and such that, for each `Σⱼ ∈ C`, there is an
index `l(j)` such that `Σⱼ` is contained in `X_{l(j)} ∪ X_{l(j)+1} ∪ ... ∪ X_{l(j)+|Σⱼ|-1}`?

This is the restriction of 2-DIMENSIONAL CONSECUTIVE SETS
(`WantedExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsWanted`) to subsets of size at
most `5`, from Garey and Johnson's comment to [SR19]. The instance type, the parent
well-formedness condition and the question are that module's
(`TwoDimensionalConsecutiveSets.TwoDimensionalConsecutiveSetsInstance`,
`TwoDimensionalConsecutiveSets.WellFormed`,
`TwoDimensionalConsecutiveSets.TwoDimensionalConsecutiveSetsFeasible`); the restriction is
added to `WellFormed`. Each subset `Σⱼ` is a list of distinct symbols, so `|Σⱼ|` is its length.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed 2-DIMENSIONAL CONSECUTIVE SETS instance
(every subset lists distinct symbols of the alphabet), and every subset has at most `5`
elements. -/
def WellFormed (i : TwoDimensionalConsecutiveSets.TwoDimensionalConsecutiveSetsInstance) :
    Prop :=
  TwoDimensionalConsecutiveSets.WellFormed i ∧ ∀ S ∈ i.2, S.length ≤ 5

open Classical in
/-- 2-DIMENSIONAL CONSECUTIVE SETS with sets of size at most 5 as a decision problem over
bitstrings. -/
noncomputable def twoDimensionalConsecutiveSetsSizeFiveDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoDimensionalConsecutiveSets.TwoDimensionalConsecutiveSetsInstance) x with
  | some i => decide (WellFormed i ∧
      TwoDimensionalConsecutiveSets.TwoDimensionalConsecutiveSetsFeasible i)
  | none => false

/-- **2-DIMENSIONAL CONSECUTIVE SETS with sets of size at most 5 is NP-complete.** Source: Garey
and Johnson (1979), [SR19], comment; Lipski (1977). -/
public theorem_wanted twoDimensionalConsecutiveSetsSizeFive_npComplete :
    twoDimensionalConsecutiveSetsSizeFiveDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoDimensionalConsecutiveSetsSizeFiveDec

end MetaMathlibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsSizeFive
