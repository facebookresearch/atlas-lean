/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit weights is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS4] SEQUENCING TO MINIMIZE
WEIGHTED COMPLETION TIME (comment: NP-complete in the strong sense and remains so even if all
task weights are 1);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22;
E. L. Lawler, "Sequencing jobs to minimize total weighted completion time subject to
precedence constraints", Annals of Discrete Mathematics 2 (1978), 75-90,
doi:10.1016/S0167-5060(08)70323-6.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PrecedenceWeightedCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitWeightCompletion

/-!
# SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit weights is NP-complete

The restriction of SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME (`1|prec|∑ wⱼCⱼ`) to
instances in which every task weight is `w(t) = 1` (`1|prec|∑ Cⱼ`): given tasks with lengths
`l(t) ∈ ℤ⁺`, a partial order `<` on them, and a positive integer `K`, is there a one-processor
schedule obeying the precedence constraints whose total completion time
`∑ₜ (σ(t) + l(t))` is `K` or less? The instance type, the base well-formedness and the question
are those of `PrecedenceWeightedCompletionWanted`, reused unchanged; this module adds to
`WellFormed` the restriction `w(t) = 1` together with Garey and Johnson's `l(t) ∈ ℤ⁺` and
`K ∈ ℤ⁺`, which the base module leaves unconstrained. Binary encoding of all numbers (the
problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance, as in `PrecedenceWeightedCompletionWanted`: the jobs (processing time `l(t)`,
weight `w(t)`), the precedence pairs, and the bound `K`. -/
abbrev PrecedenceUnitWeightCompletionInstance :=
  PrecedenceWeightedCompletion.PrecedenceWeightedCompletionInstance

/-- Well-formedness of an instance: the base instance is well-formed, every job has a positive
processing time and weight `1`, and `K` is positive. -/
def WellFormed (i : PrecedenceUnitWeightCompletionInstance) : Prop :=
  PrecedenceWeightedCompletion.WellFormed i ∧ (∀ j ∈ i.1, 0 < j.1 ∧ j.2 = 1) ∧ 0 < i.2.2

/-- A precedence-respecting ordering of weighted completion sum at most `K`, exactly as in
`PrecedenceWeightedCompletionWanted`. -/
def PrecedenceUnitWeightCompletionFeasible (i : PrecedenceUnitWeightCompletionInstance) :
    Prop :=
  PrecedenceWeightedCompletion.PrecedenceWeightedCompletionFeasible i

open Classical in
/-- SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit weights as a decision problem
over bitstrings. -/
noncomputable def precedenceUnitWeightCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceUnitWeightCompletionInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceUnitWeightCompletionFeasible i)
  | none => false

/-- **SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit weights is NP-complete.**
Source: Garey and Johnson (1979), [SS4]; Lenstra and Rinnooy Kan (1978); Lawler (1978). -/
public theorem_wanted precedenceUnitWeightCompletion_npComplete :
    precedenceUnitWeightCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceUnitWeightCompletionDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitWeightCompletion
