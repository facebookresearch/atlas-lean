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

/-- **Scottish Book Problem 173.** Eidelheit's claim that for every real Banach space $E$, the
bounded linear operators $E \to E$ that have a bounded linear two-sided inverse are dense, for
the operator norm, in the space of all bounded linear operators on $E$. -/
def ScottishBookProblem173Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    Dense {T : E →L[ℝ] E |
      ∃ S : E →L[ℝ] E,
        ContinuousLinearMap.comp T S = ContinuousLinearMap.id ℝ E ∧
          ContinuousLinearMap.comp S T = ContinuousLinearMap.id ℝ E}

/--
**Negative answer to Scottish Book Problem 173.** Eidelheit's claim in Problem 173 is false:
there is a real Banach space $E$ in which the bounded linear operators $E \to E$ that have a
bounded linear two-sided inverse are not dense, for the operator norm, in the space of all
bounded linear operators on $E$.

For instance, in an infinite-dimensional Hilbert space the invertible operators are not dense,
by the Fredholm-index obstruction: the unilateral shift cannot be approximated by invertible
operators.

Source: M. Eidelheit, Problem 173 of the
Scottish Book; see P. Halmos, A Hilbert Space Problem Book, Problem 109.
-/
theorem_wanted eidelheit173_refuted : ¬ ScottishBookProblem173Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook173Wanted
