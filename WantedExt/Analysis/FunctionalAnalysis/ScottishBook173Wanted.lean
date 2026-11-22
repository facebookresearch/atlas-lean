/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook173Wanted

/-- Eidelheit's Problem 173 from the Scottish Book, in its original form:
in the ring `A` of all bounded linear operations of a Banach space into
itself, the operations possessing a continuous (two-sided) inverse are
dense in `A` under the usual operator norm. -/
def ScottishBookProblem173Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    Dense {T : E →L[ℝ] E |
      ∃ S : E →L[ℝ] E,
        ContinuousLinearMap.comp T S = ContinuousLinearMap.id ℝ E ∧
          ContinuousLinearMap.comp S T = ContinuousLinearMap.id ℝ E}

/--
Eidelheit's Problem 173 is false in general: in an infinite-dimensional
Hilbert space the invertible operators are not dense, e.g. by the
Fredholm-index obstruction (the unilateral shift cannot be approximated
by invertible operators). Source: M. Eidelheit, Problem 173 of the
Scottish Book; see P. Halmos, A Hilbert Space Problem Book, Problem 109.
-/
theorem_wanted eidelheit173_refuted : ¬ ScottishBookProblem173Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook173Wanted
