/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.CurrentContinuityAxisInfrared
import Code.FrontierB.CurrentContinuityAxisClosure
import Code.Ising.GibbsSimplexInfinite

open MeasureTheory

namespace StatMech.FrontierB

open StatMech.Ising

variable {d : Nat}




theorem isingCritical_magnetization_zero_and_gibbs_unique
    (hd : 2 < d) :
    magnetization d (IsingFK.betaC (magnetization d)) = 0 ∧
      ∀ (mu : Measure (ConfigSpace (Lattice.Site d)))
        [IsProbabilityMeasure mu],
        IsDLRState d (IsingFK.betaC (magnetization d)) 0 mu →
          mu = (minusState d (IsingFK.betaC (magnetization d)) 0 :
            Measure (ConfigSpace (Lattice.Site d))) := by
  have hbetaC : 0 < IsingFK.betaC (magnetization d) := by
    rw [StatMech.FrontierA.isingFK_betaC_eq_tildeBetaCIsing
      (by omega : 2 ≤ d)]
    exact Sharpness.tildeBetaCIsing_pos (by omega : 2 ≤ d)
  have hLRO := currentContinuityFreeAxisLROZero_at_isingCritical hd
  have hcollapse :=
    currentContinuity_magnetization_and_phase_eq_of_freeAxisLROZero
      (IsingFK.betaC (magnetization d)) hbetaC (by omega : 1 ≤ d) hLRO
  refine ⟨hcollapse.2.2.1, ?_⟩
  intro mu hprob hmu
  exact gsi_gibbs_unique_of_phases_eq
    (IsingFK.betaC (magnetization d)) 0 hbetaC.le (by norm_num)
      mu hmu hcollapse.2.2.2

end StatMech.FrontierB
