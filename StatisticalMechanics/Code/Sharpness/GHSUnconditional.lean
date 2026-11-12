/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.GHSLebowitz
import Code.Walls.gc4_concavitysharpness

open scoped BigOperators
open Set SimpleGraph

namespace StatMech
namespace Sharpness

open Ising Walls Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem ghs_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    GHSSignDominance G β h o := by
  intro x y hox _ _
  have hpair := ghsL_pair G β h hβ hh o x y hox
  rw [← sub_nonpos, ghsThreePoint_eq_ursell] at hpair
  simpa [eg_ursell3] using hpair



theorem ghs_magnetization_concaveOn (β : ℝ) (hβ : 0 ≤ β) (o : V) :
    ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)) :=
  gc4_magnetization_concaveOn G β hβ o
    (fun h hh => ghs_signDominance G β h hβ hh o)




theorem ghs_susceptibility_unconditional (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 < h)
    (o : V) :
    deriv (fun t => isingExpectation G β t (fun s => spin s o)) h =
        β * ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x) -
          isingExpectation G β h (fun s => spin s o) *
            isingExpectation G β h (fun s => spin s x))
      ∧ deriv (fun t => isingExpectation G β t (fun s => spin s o)) h ≤ 1 / h := by
  refine ⟨deriv_magnetization_eq_sum_cov G β h o, ?_⟩
  exact (ghs_susceptibility_bound G β h hh o
    (ghs_magnetization_concaveOn G β hβ o)).2

end Sharpness
end StatMech
