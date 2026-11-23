/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for veto with three candidates is NP-complete

Source:
V. Conitzer, T. Sandholm and J. Lang, "When are elections with few candidates hard to
manipulate?", Journal of the ACM 54(3) (2007), Article 14, doi:10.1145/1236457.1236461,
Definition 1, Theorem 6 and Corollary 1 (reduction from PARTITION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CoalitionalManipulationBordaWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationVeto

open MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationBorda

/-!
# CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for veto with three candidates is NP-complete

INSTANCE: three candidates, a set `S` of weighted votes (the nonmanipulators' votes), the
weights of a set `T` of votes that are still open (the manipulators' votes), and a preferred
candidate `p`.
QUESTION: is there a way to cast the votes in `T` so that `p` wins the election under the veto
protocol?

The veto protocol for three candidates is the positional scoring protocol with
`α = (1, 1, 0)`: each voter gives one point to each candidate except the one it ranks last,
and the candidate with the highest score wins. As in the source, a manipulation that leaves `p`
tied for the win is not successful: `p` must score strictly more than each other candidate.

The instance type, the well-formedness condition, votes (`IsRanking`), positional scores
(`points`, `score`) and the manipulation question (`ManipulationFeasible`) are those of the
Borda module `CoalitionalManipulationBordaWanted`, taken with the veto vector instead of the
Borda vector. Weights are natural numbers in the canonical binary encoding; the source's
hardness proof reduces from PARTITION, so the weights carry the hardness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The veto scoring vector for three candidates, `(1, 1, 0)`. -/
def vetoVector : List ℕ := [1, 1, 0]

/-- The manipulators can make `p` the unique veto winner. -/
def CoalitionalManipulationVetoFeasible (i : CoalitionalManipulationInstance) : Prop :=
  ManipulationFeasible vetoVector i

open Classical in
/-- CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for veto with three candidates as a
decision problem over bitstrings. -/
noncomputable def coalitionalManipulationVetoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoalitionalManipulationInstance) x with
  | some i => decide (WellFormed i ∧ CoalitionalManipulationVetoFeasible i)
  | none => false

/-- **CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for veto with three candidates is
NP-complete.** Source: Conitzer, Sandholm and Lang (2007), Corollary 1. -/
public theorem_wanted coalitionalManipulationVeto_npComplete :
    coalitionalManipulationVetoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coalitionalManipulationVetoDec

end MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationVeto
