/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MIN-FEATURES is NP-complete

Source:
S. Davies and S. Russell, "NP-completeness of searches for smallest possible feature sets",
in *Relevance: Papers from the 1994 AAAI Fall Symposium*, AAAI Technical Report FS-94-02
(1994), 37-39 (reduction from VERTEX COVER);
the problem is from H. Almuallim and T. G. Dietterich, "Learning Boolean concepts in the
presence of many irrelevant features", Artificial Intelligence 69 (1994), 279-305,
doi:10.1016/0004-3702(94)90084-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinFeatures

/-!
# MIN-FEATURES is NP-complete

INSTANCE: a set `X` of examples, each composed of a binary value of the target feature and a
vector of binary values of the input features, and a number `n`. QUESTION: is there a feature
set `S` such that `S` is a subset of the set of all input features, `S` has cardinality `n`, and
there exist no two examples in `X` that have identical values for all the features in `S` but
have different values for the target feature?

The input features are `0, …, f - 1`; an example is a pair of a Boolean vector of length `f`
(the input feature values) and a Boolean (the target value), and `X` is a list of examples.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `f` of input features, the examples (input values, target value),
and the cardinality `n`. -/
abbrev MinFeaturesInstance := ℕ × List (List Bool × Bool) × ℕ

/-- Well-formedness of an instance: every example gives a value for each of the `f` input
features. -/
def WellFormed (i : MinFeaturesInstance) : Prop :=
  ∀ x ∈ i.2.1, x.1.length = i.1

/-- Some set `S` of exactly `n` input features is sufficient: two examples that agree on every
feature in `S` have the same target value. -/
def MinFeaturesFeasible (i : MinFeaturesInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card = i.2.2 ∧
    ∀ x ∈ i.2.1, ∀ y ∈ i.2.1, (∀ j ∈ S, x.1.getD j false = y.1.getD j false) → x.2 = y.2

open Classical in
/-- MIN-FEATURES as a decision problem over bitstrings. -/
noncomputable def minFeaturesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinFeaturesInstance) x with
  | some i => decide (WellFormed i ∧ MinFeaturesFeasible i)
  | none => false

/-- **MIN-FEATURES is NP-complete.** Source: Davies and Russell (1994). -/
public theorem_wanted minFeatures_npComplete :
    minFeaturesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minFeaturesDec

end MetaMathlibExt.Complexity.NPComplete.MinFeatures
