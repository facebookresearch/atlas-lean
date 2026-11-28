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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinFeaturesDefs

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

/-- **MIN-FEATURES is NP-complete.** Source: Davies and Russell (1994). -/
public theorem_wanted minFeatures_npComplete :
    minFeaturesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minFeaturesDec

end MetaMathlibExt.Complexity.NPComplete.MinFeatures
