/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECOLORING EXTENSION is NP-complete

Source:
M. Biro, M. Hujter, and Z. Tuza, "Precoloring extension. I. Interval graphs", Discrete
Mathematics 100 (1992), 267-279 (NP-completeness on interval graphs, hence on general graphs);
hardness also follows directly from Garey-Johnson CHROMATIC NUMBER (GT4) by taking the
precoloring to be empty.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PrecoloringExtensionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecoloringExtension

/-!
# PRECOLORING EXTENSION is NP-complete

An undirected graph, a partial coloring (0 means uncolored, `k + 1` means color `k`), and a
bound `K`. The question is whether the partial coloring extends to a proper coloring with
colors `0, …, K - 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PRECOLORING EXTENSION is NP-complete.** The decision problem PRECOLORING EXTENSION lies in
NP, and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. Biro, M. Hujter, and Z. Tuza,
"Precoloring extension. I. Interval graphs", Discrete Mathematics 100 (1992), 267-279 (NP-
completeness on interval graphs, hence on general graphs); hardness also follows directly
from Garey-Johnson CHROMATIC NUMBER (GT4) by taking the precoloring to be empty. -/
public theorem_wanted precoloringExtension_npComplete :
    precoloringExtensionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precoloringExtensionDec

end MetaMathlibExt.Complexity.NPComplete.PrecoloringExtension
