/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook122Wanted

/--
Every infinite-dimensional Banach space contains a series that converges
unconditionally but not absolutely: it converges under every ordering of
its terms, while `∑ ‖x_n‖` diverges. Source: S. Mazur and W. Orlicz,
Problem 122 of the Scottish Book; A. Dvoretzky and C. A. Rogers, "Absolute
and unconditional convergence in normed linear spaces", Proc. Natl. Acad.
Sci. USA 36 (1950), 192-197.
-/
theorem_wanted dvoretzky_rogers_unconditional_not_absolute :
    ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
      ¬ Module.Finite ℝ E →
      ∃ x : ℕ → E,
        (∀ σ : Equiv.Perm ℕ, Summable (x ∘ σ)) ∧
        ¬ Summable (fun n => ‖x n‖)

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook122Wanted
