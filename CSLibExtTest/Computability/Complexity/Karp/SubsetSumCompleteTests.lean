/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.SubsetSumComplete

/-! Elaboration checks for the SUBSET-SUM assembly (the components have their own run tests). -/

namespace Cslib.Complexity.Karp.SubsetSumCompleteTests

open Cslib.CookLevin MetaMathlibExt.ComplexityTheory

example : IsPolyTime reduceSS := isPolyTime_reduceSS
example : subsetSumDec ∈ NP := subsetSumDec_mem_NP
example : PolyManyOneRed vertexCoverDec subsetSumDec := vertexCoverDec_polyManyOneRed_subsetSumDec
example : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L subsetSumDec :=
  subsetSumDec_npComplete.2

end Cslib.Complexity.Karp.SubsetSumCompleteTests
