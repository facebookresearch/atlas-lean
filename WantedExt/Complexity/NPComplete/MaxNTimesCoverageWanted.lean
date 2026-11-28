/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM n-TIMES COVERAGE is NP-complete

Source:
G. Liu, A. Dimitrakakis, B. Carter and D. Gifford, "Maximum n-times coverage for vaccine design",
*International Conference on Learning Representations (ICLR)* (2022).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaxNTimesCoverageDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxNTimesCoverage

/-!
# MAXIMUM n-TIMES COVERAGE is NP-complete

An instance is `(n, rows, weights, k, τ)`: each row lists, for one overlay, how many times it
covers each element; `weights` are the element weights. The question is whether at most `k`
overlays cover elements of total weight at least `τ` at least `n` times each (the decision
version of the problem of Liu et al.; the objective is `nCoverage` in
`CSLibExt/Algorithms/Lean/Approximation/MaxNTimesCoverage.lean`). For `n = 1` and unit
multiplicities this contains maximum coverage, hence SET COVER.

Encoding and the NP-completeness format follow
`WantedExt/Complexity/NPComplete/SetCoverWanted.lean`.
-/

/-- **MAXIMUM n-TIMES COVERAGE is NP-complete** (Liu, Dimitrakakis, Carter and Gifford 2022). -/
public theorem_wanted maxNTimesCoverage_npComplete :
    maxNTimesCoverageDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxNTimesCoverageDec

end MetaMathlibExt.Complexity.NPComplete.MaxNTimesCoverage
